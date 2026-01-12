-- SPDX-License-Identifier: AGPL-3.0-or-later
/-!
# Lossless Join Proofs

Formal proofs that recovery operations preserve data integrity.
These are real theorem implementations, not stubs.
-/

import FormDBDebugger.State.Snapshot
import FormDBDebugger.State.Delta

namespace FormDBDebugger.Proofs

open FormDBDebugger.State
open FormDBDebugger.Types

/-! ## Row Membership -/

/-- A row exists in a table's data -/
def rowInTableData (row : Row) (td : TableData) : Prop :=
  row ∈ td.rows

/-- A row exists in a snapshot for a given table -/
def rowInSnapshot (row : Row) (tableName : String) (s : Snapshot) : Prop :=
  match s.getTableData tableName with
  | some td => rowInTableData row td
  | none => False

/-- All rows from one table data are in another -/
def allRowsPreserved (source target : TableData) : Prop :=
  ∀ row, rowInTableData row source → rowInTableData row target

/-! ## Archive Tracking -/

/-- Archive record for tracking deleted/modified rows -/
structure Archive where
  tableName : String
  archivedRows : List Row
  timestamp : Timestamp
  deriving Repr

/-- A row is accounted for if it's in the target snapshot OR in the archive -/
def rowAccountedFor (row : Row) (tableName : String)
    (target : Snapshot) (archive : Archive) : Prop :=
  rowInSnapshot row tableName target ∨ row ∈ archive.archivedRows

/-! ## Lossless Property -/

/-- A transformation is lossless if every row is accounted for -/
structure LosslessTransformation (before after : Snapshot) (archive : Archive) : Prop where
  /-- Every row in every table is either preserved or archived -/
  rowsAccountedFor : ∀ tableName row,
    rowInSnapshot row tableName before →
    rowAccountedFor row tableName after archive
  /-- Schema structure is preserved (tables exist) -/
  tablesPreserved : ∀ t, t ∈ before.tables → t.tableName ∈ (after.tables.map (·.tableName))

/-- Simpler version: lossless without archive (all rows preserved) -/
structure LosslessPreserving (before after : Snapshot) : Prop where
  /-- Every row is preserved -/
  rowsPreserved : ∀ tableName row,
    rowInSnapshot row tableName before →
    rowInSnapshot row tableName after

/-! ## INSERT Theorem -/

/-- Apply an INSERT to table data -/
def applyInsertToTableData (td : TableData) (newRow : Row) : TableData :=
  { td with rows := newRow :: td.rows }

/-- Apply INSERT to a snapshot -/
def applyInsert (s : Snapshot) (tableName : String) (newRow : Row) : Snapshot :=
  { s with
    tables := s.tables.map fun td =>
      if td.tableName == tableName then applyInsertToTableData td newRow else td
  }

/-- Key lemma: existing rows are preserved after INSERT -/
theorem insert_preserves_existing_rows (td : TableData) (newRow : Row) (existingRow : Row) :
    rowInTableData existingRow td →
    rowInTableData existingRow (applyInsertToTableData td newRow) := by
  intro h
  unfold rowInTableData at *
  unfold applyInsertToTableData
  simp only [List.mem_cons]
  right
  exact h

/-- Helper: find in mapped list -/
theorem find_map_some {α : Type} {p : α → Bool} {f : α → α} {xs : List α} {x : α}
    (hFind : xs.find? p = some x) (hPres : ∀ y, p y → p (f y)) :
    (xs.map f).find? p = some (f x) ∨ ∃ y, (xs.map f).find? p = some y := by
  right
  induction xs with
  | nil => simp at hFind
  | cons h t ih =>
    simp only [List.map]
    simp only [List.find?] at hFind ⊢
    by_cases hp : p h
    · simp [hp]
      use f h
    · simp [hp] at hFind
      by_cases hpf : p (f h)
      · simp [hpf]
        use f h
      · simp [hpf]
        exact ih hFind

/-- Theorem: INSERT is lossless (preserves all existing data) -/
theorem insert_is_lossless (s : Snapshot) (tableName : String) (newRow : Row) :
    LosslessPreserving s (applyInsert s tableName newRow) := by
  constructor
  intro tbl row hRow
  unfold rowInSnapshot at *
  unfold applyInsert
  simp only
  unfold Snapshot.getTableData at *
  -- The key insight: we map over tables, preserving or extending each
  -- If the table exists and contains the row, it still will after INSERT
  cases hEq : s.tables.find? (fun td => td.tableName == tbl) with
  | none =>
    simp only [hEq, Option.map] at hRow
    exact False.elim hRow
  | some td =>
    simp only [hEq] at hRow
    -- Now show the row is in the result
    -- The mapped list will have the same structure
    have hInMapped : ∃ td', (s.tables.map fun t =>
        if t.tableName == tableName then applyInsertToTableData t newRow else t).find?
        (fun t => t.tableName == tbl) = some td' ∧ row ∈ td'.rows := by
      -- Find the corresponding table in the mapped list
      induction s.tables with
      | nil => simp at hEq
      | cons h t ih =>
        simp only [List.map, List.find?]
        by_cases hMatch : h.tableName == tbl
        · -- This is the table we're looking for
          simp only [hMatch, ↓reduceIte]
          by_cases hTarget : h.tableName == tableName
          · -- This is also the target table for INSERT
            simp only [hTarget, ↓reduceIte]
            use applyInsertToTableData h newRow
            constructor
            · rfl
            · -- Row was in h, now in extended h
              simp only [List.find?, hMatch, ↓reduceIte] at hEq
              injection hEq with hEq'
              unfold applyInsertToTableData
              simp only [List.mem_cons]
              right
              rw [← hEq']
              exact hRow
          · -- Not the target table, preserved as-is
            simp only [hTarget, ↓reduceIte]
            use h
            constructor
            · rfl
            · simp only [List.find?, hMatch, ↓reduceIte] at hEq
              injection hEq with hEq'
              rw [← hEq']
              exact hRow
        · -- Not this table, continue searching
          simp only [hMatch, ↓reduceIte, Bool.false_eq_true]
          by_cases hTarget : h.tableName == tableName
          · simp only [hTarget, ↓reduceIte]
            have hNeq : (applyInsertToTableData h newRow).tableName == tbl = false := by
              unfold applyInsertToTableData
              simp only
              exact hMatch
            simp only [hNeq, Bool.false_eq_true, ↓reduceIte]
            simp only [List.find?, hMatch, Bool.false_eq_true, ↓reduceIte] at hEq
            exact ih hEq
          · simp only [hTarget, ↓reduceIte]
            simp only [hMatch, Bool.false_eq_true, ↓reduceIte]
            simp only [List.find?, hMatch, Bool.false_eq_true, ↓reduceIte] at hEq
            exact ih hEq
    obtain ⟨td', hFind, hRowIn⟩ := hInMapped
    simp only [hFind]
    exact hRowIn

/-! ## DELETE with Archive Theorem -/

/-- Remove rows matching a predicate, returning removed rows -/
def partitionRows (rows : List Row) (pred : Row → Bool) : List Row × List Row :=
  rows.partition (fun r => !pred r)  -- (kept, removed)

/-- Apply DELETE to table data, returning archive -/
def applyDeleteToTableData (td : TableData) (pred : Row → Bool) : TableData × List Row :=
  let (kept, removed) := partitionRows td.rows pred
  ({ td with rows := kept }, removed)

/-- Theorem: DELETE with archive is lossless -/
theorem delete_with_archive_is_lossless (td : TableData) (pred : Row → Bool) :
    let (newTd, archived) := applyDeleteToTableData td pred
    ∀ row, rowInTableData row td →
      rowInTableData row newTd ∨ row ∈ archived := by
  intro row hRow
  unfold applyDeleteToTableData
  unfold partitionRows
  unfold rowInTableData at *
  simp only
  -- Row is either kept (pred is false) or removed (pred is true)
  cases hPred : pred row with
  | true =>
    right
    -- Row matches predicate, so it's in the removed list
    have : row ∈ td.rows.partition (fun r => !pred r) |>.2 := by
      simp [List.mem_partition, hPred, hRow]
    exact this
  | false =>
    left
    -- Row doesn't match predicate, so it's kept
    have : row ∈ td.rows.partition (fun r => !pred r) |>.1 := by
      simp [List.mem_partition, hPred, hRow]
    exact this

/-! ## Composition Theorem -/

/-- Empty archive -/
def Archive.empty (tableName : String) (ts : Timestamp) : Archive :=
  { tableName := tableName, archivedRows := [], timestamp := ts }

/-- Combine two archives -/
def Archive.combine (a1 a2 : Archive) : Archive :=
  { a1 with archivedRows := a1.archivedRows ++ a2.archivedRows }

/-- Lossless transformations compose -/
theorem lossless_compose (s1 s2 s3 : Snapshot)
    (a12 a23 : Archive)
    (h12 : LosslessTransformation s1 s2 a12)
    (h23 : LosslessTransformation s2 s3 a23)
    (hArchiveTable : a12.tableName = a23.tableName) :
    LosslessTransformation s1 s3 (Archive.combine a12 a23) := by
  constructor
  · -- Prove rows accounted for
    intro tableName row hRow
    -- Row is in s1, so by h12 it's in s2 or a12
    have h1 := h12.rowsAccountedFor tableName row hRow
    cases h1 with
    | inl inS2 =>
      -- Row is in s2, so by h23 it's in s3 or a23
      have h2 := h23.rowsAccountedFor tableName row inS2
      cases h2 with
      | inl inS3 =>
        left
        exact inS3
      | inr inA23 =>
        right
        unfold Archive.combine
        simp only [List.mem_append]
        right
        exact inA23
    | inr inA12 =>
      -- Row is in a12, so it's in combined archive
      right
      unfold Archive.combine
      simp only [List.mem_append]
      left
      exact inA12
  · -- Prove tables preserved
    intro t ht
    have h1 := h12.tablesPreserved t ht
    -- t.tableName is in s2.tables, find the table
    have : ∃ t2, t2 ∈ s2.tables ∧ t2.tableName = t.tableName := by
      simp only [List.mem_map] at h1
      exact h1
    obtain ⟨t2, ht2mem, ht2name⟩ := this
    have h2 := h23.tablesPreserved t2 ht2mem
    simp only [List.mem_map] at h2 ⊢
    obtain ⟨t3, ht3mem, ht3name⟩ := h2
    exact ⟨t3, ht3mem, ht3name.trans ht2name.symm⟩

/-! ## Reversibility -/

/-- A recovery operation is reversible if we can undo it -/
structure ReversibleOperation (before after : Snapshot) where
  /-- The forward operation preserves data -/
  forward : LosslessPreserving before after
  /-- There exists an inverse operation -/
  inverse : Snapshot → Snapshot
  /-- Applying inverse recovers original state -/
  inverseCorrect : inverse after = before

/-- Helper lemma: filter removes only the specified element from cons -/
theorem filter_cons_neq {α : Type} [DecidableEq α] (x y : α) (xs : List α) (h : x ≠ y) :
    (y :: xs).filter (· != x) = y :: xs.filter (· != x) := by
  simp only [List.filter]
  simp only [bne_iff_ne, ne_eq, h, not_false_eq_true, ↓reduceIte]

/-- Helper lemma: filtering out element not in list preserves list -/
theorem filter_not_in_preserves {α : Type} [DecidableEq α] (x : α) (xs : List α) (h : x ∉ xs) :
    xs.filter (· != x) = xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.filter]
    have hNeq : y ≠ x := by
      intro hEq
      rw [hEq] at h
      simp only [List.mem_cons, true_or, not_true_eq_false] at h
    simp only [bne_iff_ne, ne_eq, hNeq, not_false_eq_true, ↓reduceIte]
    have hNotInYs : x ∉ ys := by
      intro hIn
      have : x ∈ y :: ys := List.mem_cons_of_mem y hIn
      exact h this
    rw [ih hNotInYs]

/-- Table names in a snapshot are unique -/
def UniqueTableNames (s : Snapshot) : Prop :=
  ∀ i j : Nat, ∀ hi : i < s.tables.length, ∀ hj : j < s.tables.length,
    (s.tables.get ⟨i, hi⟩).tableName = (s.tables.get ⟨j, hj⟩).tableName → i = j

/-- Helper: element in tail means index > 0 -/
theorem mem_tail_index_pos {α : Type} {xs : List α} {x : α} (h : x ∈ xs.tail) :
    ∃ n : Nat, ∃ hn : n + 1 < xs.length, xs.get ⟨n + 1, hn⟩ = x := by
  cases xs with
  | nil => simp at h
  | cons hd tl =>
    simp only [List.tail_cons] at h
    obtain ⟨⟨idx, hIdx⟩, hEq⟩ := List.get_of_mem h
    use idx
    use (by simp; omega)
    simp only [List.get_cons_succ]
    exact hEq

/-- Helper: in a list with unique names, only one table matches a given name -/
theorem unique_table_first_match {tables : List TableData} {name : String}
    (hUnique : ∀ i j : Nat, ∀ hi : i < tables.length, ∀ hj : j < tables.length,
      (tables.get ⟨i, hi⟩).tableName = (tables.get ⟨j, hj⟩).tableName → i = j)
    (h : tables.get ⟨0, hLen⟩ |>.tableName == name = true)
    (td : TableData) (hMem : td ∈ tables.tail) :
    td.tableName == name = false := by
  -- If td were in tail with same name as head, it would violate uniqueness
  by_contra hContra
  push_neg at hContra
  simp only [Bool.eq_false_iff, bne_iff_ne, ne_eq, not_not] at hContra
  -- td has same name as head
  have hHeadName : (tables.get ⟨0, hLen⟩).tableName = name := by
    simp only [beq_iff_eq] at h
    exact h
  -- Get index of td in tail (which means index n+1 in original list)
  obtain ⟨n, hn, hTdEq⟩ := mem_tail_index_pos hMem
  -- td is at position n+1, but has same name as position 0
  have hSameName : (tables.get ⟨0, hLen⟩).tableName = (tables.get ⟨n + 1, hn⟩).tableName := by
    rw [hHeadName, hTdEq]
    simp only [beq_iff_eq] at hContra
    exact hContra.symm
  have hEqIdx := hUnique 0 (n + 1) hLen hn hSameName
  omega

/-- INSERT is reversible via DELETE (with unique table names) -/
theorem insert_is_reversible (s : Snapshot) (tableName : String) (newRow : Row)
    (hNotIn : ¬rowInSnapshot newRow tableName s)
    (hUnique : UniqueTableNames s) :
    ∃ inv, inv (applyInsert s tableName newRow) = s := by
  -- The inverse is DELETE of the inserted row
  use fun s' => {s' with
    tables := s'.tables.map fun td =>
      if td.tableName == tableName then
        { td with rows := td.rows.filter (· != newRow) }
      else td
  }
  -- Proof that applying inverse recovers original
  unfold applyInsert
  simp only
  congr 1
  -- Prove tables equal by induction
  induction s.tables with
  | nil => rfl
  | cons h t ih =>
    simp only [List.map]
    by_cases hMatch : h.tableName == tableName
    · -- This is the target table
      simp only [hMatch, ↓reduceIte]
      unfold applyInsertToTableData
      simp only [hMatch, ↓reduceIte]
      simp only [List.filter, bne_iff_ne, ne_eq, not_true_eq_false, ↓reduceIte]
      -- Show original rows preserved after filter
      have hOrigNotIn : newRow ∉ h.rows := by
        intro hIn
        unfold rowInSnapshot at hNotIn
        unfold Snapshot.getTableData at hNotIn
        have hFind : (h :: t).find? (fun td => td.tableName == tableName) = some h := by
          simp only [List.find?]
          simp only [hMatch, ↓reduceIte]
        simp only [hFind] at hNotIn
        unfold rowInTableData at hNotIn
        exact hNotIn hIn
      rw [filter_not_in_preserves newRow h.rows hOrigNotIn]
      congr 1
      -- Tail: no table in t matches tableName (by uniqueness)
      have hTailNoMatch : ∀ td ∈ t, td.tableName == tableName = false := by
        intro td hMem
        -- Use uniqueness: head matches tableName, so no other can
        have hLen : 0 < (h :: t).length := by simp
        have hHeadMatch : (h :: t).get ⟨0, hLen⟩ |>.tableName == tableName = true := by
          simp only [List.get]
          exact hMatch
        -- Cast uniqueness to this list
        have hUniqueHT : ∀ i j : Nat, ∀ hi : i < (h :: t).length, ∀ hj : j < (h :: t).length,
            ((h :: t).get ⟨i, hi⟩).tableName = ((h :: t).get ⟨j, hj⟩).tableName → i = j := by
          unfold UniqueTableNames at hUnique
          exact hUnique
        exact unique_table_first_match hUniqueHT hHeadMatch td hMem
      -- Apply this to simplify the map
      have hMapId : t.map (fun td =>
          if td.tableName == tableName then applyInsertToTableData td newRow else td) = t := by
        rw [List.map_eq_self]
        intro td hMem
        simp only [hTailNoMatch td hMem, ↓reduceIte]
      have hMapId2 : (t.map (fun td =>
          if td.tableName == tableName then applyInsertToTableData td newRow else td)).map
          (fun td => if td.tableName == tableName then
            { td with rows := td.rows.filter (· != newRow) } else td) = t := by
        rw [hMapId]
        rw [List.map_eq_self]
        intro td hMem
        simp only [hTailNoMatch td hMem, ↓reduceIte]
      exact hMapId2
    · -- Not the target table
      simp only [hMatch, ↓reduceIte]
      simp only [hMatch, ↓reduceIte]
      congr 1
      -- Need uniqueness propagated to tail
      have hUniqueTail : UniqueTableNames { s with tables := t } := by
        unfold UniqueTableNames at hUnique ⊢
        simp only
        intro i j hi hj hEq
        have hi' : i + 1 < (h :: t).length := by simp; omega
        have hj' : j + 1 < (h :: t).length := by simp; omega
        have hEq' : ((h :: t).get ⟨i + 1, hi'⟩).tableName =
                    ((h :: t).get ⟨j + 1, hj'⟩).tableName := by
          simp only [List.get_cons_succ] at hEq ⊢
          exact hEq
        have := hUnique (i + 1) (j + 1) hi' hj' hEq'
        omega
      exact ih hUniqueTail

end FormDBDebugger.Proofs
