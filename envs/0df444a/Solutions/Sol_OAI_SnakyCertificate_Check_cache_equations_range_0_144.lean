-- Prove2me | solution 1 for OAI.SnakyCertificate.Check.cache_equations_range_0_144
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T23:52:47.011295+00:00
-- url     : https://prove2.me/submissions/4d9e64b2-44da-4cf7-887f-73547d3a3f5f

import Mathlib
import Definitions.Def_SnakyCertificate
import Definitions.Def_OAIQ114S000

section
-- module Solutions.OAIQ114_SC.Compat
attribute [-instance] _root_.OAI.SnakyCertificate.digitModulus_neZero _root_.OAI.SnakyCertificate.rotationModulus_neZero
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_Lists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

theorem mem_mergeFuel (z : Cell) (n : ℕ) (xs ys : List Cell) :
    z ∈ mergeFuel n xs ys ↔ z ∈ xs ∨ z ∈ ys := by
  induction n generalizing xs ys with
  | zero => simp [mergeFuel]
  | succ n ih =>
    cases xs with
    | nil => simp [mergeFuel]
    | cons x xs =>
      cases ys with
      | nil => simp [mergeFuel]
      | cons y ys =>
        simp only [mergeFuel]
        split
        · rename_i h; subst y
          simp only [List.mem_cons, ih]
          tauto
        · split <;> simp only [List.mem_cons, ih] <;> tauto

@[simp] theorem mem_mergeUnion (z : Cell) (xs ys : List Cell) :
    z ∈ mergeUnion xs ys ↔ z ∈ xs ∨ z ∈ ys :=
  mem_mergeFuel z _ xs ys

@[simp] theorem toFinset_mergeUnion (xs ys : List Cell) :
    (mergeUnion xs ys).toFinset = xs.toFinset ∪ ys.toFinset := by
  ext z; simp

theorem mem_sortFuel (z : Cell) (n : ℕ) (xs : List Cell) :
    z ∈ sortFuel n xs ↔ z ∈ xs := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    simp only [sortFuel]
    split
    · rfl
    · rw [mem_mergeUnion, ih, ih, ← List.mem_append, List.take_append_drop]

@[simp] theorem toFinset_sorted (xs : List Cell) : (sorted xs).toFinset = xs.toFinset := by
  ext z; simp [sorted, mem_sortFuel]

@[simp] theorem denote_place (t : Term) (d : ListRow) :
    denote (place t d) = placeRow t (denote d) := by
  have heq (xs : List Cell) :
      (sorted (xs.map (keyPlace t))).toFinset = xs.toFinset.image (placement t.rotation t.shift) := by
    ext z
    simp [keyPlace]
  simp only [denote, place, placeRow, heq]

@[simp] theorem toFinset_unions (xs : List (List Cell)) :
    (unions xs).toFinset = (xs.map List.toFinset).foldr (· ∪ ·) ∅ := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp_all [unions]

theorem toFinset_inters (xs : List (List Cell)) (a : List Cell) :
    (xs.foldr (· ∩ ·) a).toFinset = (xs.map List.toFinset).foldr (· ∩ ·) a.toFinset := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp_all only [List.foldr_cons, List.map_cons, toFinset_inter_cell]

@[simp] theorem toFinset_common (ds : List ListRow) :
    (common (ds.map ListRow.H)).toFinset = commonH (ds.map denote) := by
  cases ds with
  | nil => rfl
  | cons d ds => simp [common, commonH, toFinset_inters, Function.comp_def, denote]

theorem denote_fork (ds : List ListRow) : denote (fork ds) = forkRow (ds.map denote) := by
  have hA : (unions (ds.map ListRow.A)).toFinset = unionA (ds.map denote) := by
    simp [unionA, Function.comp_def, denote]
  have hH : (unions (ds.map ListRow.H)).toFinset = unionH (ds.map denote) := by
    simp [unionH, Function.comp_def, denote]
  have hf (xs : List Cell) :
      (xs.filter (fun p => decide (p ≠ origin))).toFinset = xs.toFinset.erase origin := by
    ext p; simp [and_comm]
  simp only [denote, fork, hf, toFinset_mergeUnion, hA, hH, toFinset_common,
    List.toFinset_cons, List.toFinset_nil]
  simp [forkRow, denote, Function.comp_def]

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_TableList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate

theorem table_toList : table.toList = tableList := by
  simp only [table, Array.toList_append]
  rfl

theorem table_getElem?_eq (k : ℕ) : table[k]? = tableList[k]? := by
  rw [← Array.getElem?_toList, table_toList]

theorem merge_ranges {P : ℕ → Prop} {a b c : ℕ}
    (left : ∀ i, a ≤ i → i < b → P i)
    (right : ∀ i, b ≤ i → i < c → P i) :
    ∀ i, a ≤ i → i < c → P i := by
  intro i hlo hhi
  by_cases h : i < b
  · exact left i hlo h
  · exact right i (by omega) hhi

end SnakyCertificate

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_Equations00
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

theorem cache_equation_0 : CacheEquation 0 := by
  unfold CacheEquation
  decide +kernel

theorem cache_equation_1 : CacheEquation 1 := by
  unfold CacheEquation
  decide +kernel

theorem cache_equation_2 : CacheEquation 2 := by
  unfold CacheEquation
  decide +kernel

theorem cache_equation_3 : CacheEquation 3 := by
  unfold CacheEquation
  decide +kernel

theorem cache_equation_4 : CacheEquation 4 := by
  unfold CacheEquation
  decide +kernel

theorem cache_equation_5 : CacheEquation 5 := by
  unfold CacheEquation
  decide +kernel

theorem verified_row_6 : fork [place ⟨0, 0, 0, 3⟩ cache_0] = cache_6 := by
  decide +kernel

theorem load_entry_6 : entryAt 6 = entry_6 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_6 : CacheEquation 6 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(6 < 6)), load_entry_6]
  change forkRow [placeRow ⟨0, 0, 0, 3⟩ (denote cache_0)] = denote cache_6
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_6

theorem verified_row_7 : fork [place ⟨4, 0, 3, 4⟩ cache_4, place ⟨6, 0, 5, 4⟩ cache_6] = cache_7 := by
  decide +kernel

theorem load_entry_7 : entryAt 7 = entry_7 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_7 : CacheEquation 7 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(7 < 6)), load_entry_7]
  change forkRow [placeRow ⟨4, 0, 3, 4⟩ (denote cache_4), placeRow ⟨6, 0, 5, 4⟩ (denote cache_6)] = denote cache_7
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_7

theorem verified_row_8 : fork [place ⟨0, 4, 8, 3⟩ cache_0, place ⟨6, 4, 3, 4⟩ cache_6] = cache_8 := by
  decide +kernel

theorem load_entry_8 : entryAt 8 = entry_8 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_8 : CacheEquation 8 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(8 < 6)), load_entry_8]
  change forkRow [placeRow ⟨0, 4, 8, 3⟩ (denote cache_0), placeRow ⟨6, 4, 3, 4⟩ (denote cache_6)] = denote cache_8
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_8

theorem verified_row_9 : fork [place ⟨0, 4, 5, 4⟩ cache_0, place ⟨6, 4, 0, 5⟩ cache_6] = cache_9 := by
  decide +kernel

theorem load_entry_9 : entryAt 9 = entry_9 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_9 : CacheEquation 9 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(9 < 6)), load_entry_9]
  change forkRow [placeRow ⟨0, 4, 5, 4⟩ (denote cache_0), placeRow ⟨6, 4, 0, 5⟩ (denote cache_6)] = denote cache_9
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_9

theorem verified_row_10 : fork [place ⟨2, 0, 2, 3⟩ cache_2, place ⟨2, 6, 2, 4⟩ cache_2] = cache_10 := by
  decide +kernel

theorem load_entry_10 : entryAt 10 = entry_10 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_10 : CacheEquation 10 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(10 < 6)), load_entry_10]
  change forkRow [placeRow ⟨2, 0, 2, 3⟩ (denote cache_2), placeRow ⟨2, 6, 2, 4⟩ (denote cache_2)] = denote cache_10
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_10

theorem verified_row_11 : fork [place ⟨6, 4, 2, 5⟩ cache_6, place ⟨6, 6, 2, 3⟩ cache_6] = cache_11 := by
  decide +kernel

theorem load_entry_11 : entryAt 11 = entry_11 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_11 : CacheEquation 11 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(11 < 6)), load_entry_11]
  change forkRow [placeRow ⟨6, 4, 2, 5⟩ (denote cache_6), placeRow ⟨6, 6, 2, 3⟩ (denote cache_6)] = denote cache_11
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_11

theorem verified_row_12 : fork [place ⟨0, 6, 5, 4⟩ cache_0, place ⟨0, 0, 0, 3⟩ cache_0] = cache_12 := by
  decide +kernel

theorem load_entry_12 : entryAt 12 = entry_12 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_12 : CacheEquation 12 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(12 < 6)), load_entry_12]
  change forkRow [placeRow ⟨0, 6, 5, 4⟩ (denote cache_0), placeRow ⟨0, 0, 0, 3⟩ (denote cache_0)] = denote cache_12
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_12

theorem verified_row_13 : fork [place ⟨6, 6, 0, 3⟩ cache_6, place ⟨6, 4, 0, 5⟩ cache_6] = cache_13 := by
  decide +kernel

theorem load_entry_13 : entryAt 13 = entry_13 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_13 : CacheEquation 13 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(13 < 6)), load_entry_13]
  change forkRow [placeRow ⟨6, 6, 0, 3⟩ (denote cache_6), placeRow ⟨6, 4, 0, 5⟩ (denote cache_6)] = denote cache_13
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_13

theorem verified_row_14 : fork [place ⟨0, 6, 5, 4⟩ cache_0, place ⟨3, 6, 1, 4⟩ cache_3] = cache_14 := by
  decide +kernel

theorem load_entry_14 : entryAt 14 = entry_14 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_14 : CacheEquation 14 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(14 < 6)), load_entry_14]
  change forkRow [placeRow ⟨0, 6, 5, 4⟩ (denote cache_0), placeRow ⟨3, 6, 1, 4⟩ (denote cache_3)] = denote cache_14
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_14

theorem verified_row_15 : fork [place ⟨0, 6, 6, 4⟩ cache_0, place ⟨3, 6, 2, 4⟩ cache_3] = cache_15 := by
  decide +kernel

theorem load_entry_15 : entryAt 15 = entry_15 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_15 : CacheEquation 15 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(15 < 6)), load_entry_15]
  change forkRow [placeRow ⟨0, 6, 6, 4⟩ (denote cache_0), placeRow ⟨3, 6, 2, 4⟩ (denote cache_3)] = denote cache_15
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_15

theorem verified_row_16 : fork [place ⟨3, 6, 3, 4⟩ cache_3, place ⟨0, 6, 7, 4⟩ cache_0] = cache_16 := by
  decide +kernel

theorem load_entry_16 : entryAt 16 = entry_16 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_16 : CacheEquation 16 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(16 < 6)), load_entry_16]
  change forkRow [placeRow ⟨3, 6, 3, 4⟩ (denote cache_3), placeRow ⟨0, 6, 7, 4⟩ (denote cache_0)] = denote cache_16
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_16

theorem verified_row_17 : fork [place ⟨0, 6, 5, 4⟩ cache_0, place ⟨3, 0, 3, 3⟩ cache_3] = cache_17 := by
  decide +kernel

theorem load_entry_17 : entryAt 17 = entry_17 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_17 : CacheEquation 17 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(17 < 6)), load_entry_17]
  change forkRow [placeRow ⟨0, 6, 5, 4⟩ (denote cache_0), placeRow ⟨3, 0, 3, 3⟩ (denote cache_3)] = denote cache_17
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_17

theorem verified_row_18 : fork [place ⟨3, 6, 2, 4⟩ cache_3, place ⟨3, 0, 4, 3⟩ cache_3] = cache_18 := by
  decide +kernel

theorem load_entry_18 : entryAt 18 = entry_18 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_18 : CacheEquation 18 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(18 < 6)), load_entry_18]
  change forkRow [placeRow ⟨3, 6, 2, 4⟩ (denote cache_3), placeRow ⟨3, 0, 4, 3⟩ (denote cache_3)] = denote cache_18
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_18

theorem verified_row_19 : fork [place ⟨6, 4, 1, 5⟩ cache_6, place ⟨6, 0, 6, 5⟩ cache_6] = cache_19 := by
  decide +kernel

theorem load_entry_19 : entryAt 19 = entry_19 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_19 : CacheEquation 19 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(19 < 6)), load_entry_19]
  change forkRow [placeRow ⟨6, 4, 1, 5⟩ (denote cache_6), placeRow ⟨6, 0, 6, 5⟩ (denote cache_6)] = denote cache_19
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_19

theorem verified_row_20 : fork [place ⟨6, 4, 0, 5⟩ cache_6, place ⟨6, 0, 5, 5⟩ cache_6] = cache_20 := by
  decide +kernel

theorem load_entry_20 : entryAt 20 = entry_20 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_20 : CacheEquation 20 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(20 < 6)), load_entry_20]
  change forkRow [placeRow ⟨6, 4, 0, 5⟩ (denote cache_6), placeRow ⟨6, 0, 5, 5⟩ (denote cache_6)] = denote cache_20
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_20

theorem verified_row_21 : fork [place ⟨4, 6, 2, 3⟩ cache_4, place ⟨6, 0, 6, 5⟩ cache_6] = cache_21 := by
  decide +kernel

theorem load_entry_21 : entryAt 21 = entry_21 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_21 : CacheEquation 21 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(21 < 6)), load_entry_21]
  change forkRow [placeRow ⟨4, 6, 2, 3⟩ (denote cache_4), placeRow ⟨6, 0, 6, 5⟩ (denote cache_6)] = denote cache_21
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_21

theorem verified_row_22 : fork [place ⟨0, 6, 7, 5⟩ cache_0, place ⟨3, 0, 5, 4⟩ cache_3] = cache_22 := by
  decide +kernel

theorem load_entry_22 : entryAt 22 = entry_22 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_22 : CacheEquation 22 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(22 < 6)), load_entry_22]
  change forkRow [placeRow ⟨0, 6, 7, 5⟩ (denote cache_0), placeRow ⟨3, 0, 5, 4⟩ (denote cache_3)] = denote cache_22
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_22

theorem verified_row_23 : fork [place ⟨0, 6, 6, 4⟩ cache_0, place ⟨0, 0, 1, 3⟩ cache_0] = cache_23 := by
  decide +kernel

theorem load_entry_23 : entryAt 23 = entry_23 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_23 : CacheEquation 23 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(23 < 6)), load_entry_23]
  change forkRow [placeRow ⟨0, 6, 6, 4⟩ (denote cache_0), placeRow ⟨0, 0, 1, 3⟩ (denote cache_0)] = denote cache_23
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_23

theorem verified_row_24 : fork [place ⟨0, 0, 0, 3⟩ cache_0, place ⟨17, 0, 5, 4⟩ cache_17] = cache_24 := by
  decide +kernel

theorem load_entry_24 : entryAt 24 = entry_24 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_24 : CacheEquation 24 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(24 < 6)), load_entry_24]
  change forkRow [placeRow ⟨0, 0, 0, 3⟩ (denote cache_0), placeRow ⟨17, 0, 5, 4⟩ (denote cache_17)] = denote cache_24
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_24

theorem verified_row_25 : fork [place ⟨0, 0, 0, 3⟩ cache_0, place ⟨14, 0, 5, 4⟩ cache_14] = cache_25 := by
  decide +kernel

theorem load_entry_25 : entryAt 25 = entry_25 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_25 : CacheEquation 25 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(25 < 6)), load_entry_25]
  change forkRow [placeRow ⟨0, 0, 0, 3⟩ (denote cache_0), placeRow ⟨14, 0, 5, 4⟩ (denote cache_14)] = denote cache_25
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_25

theorem verified_row_26 : fork [place ⟨0, 4, 6, 4⟩ cache_0, place ⟨6, 0, 6, 5⟩ cache_6] = cache_26 := by
  decide +kernel

theorem load_entry_26 : entryAt 26 = entry_26 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_26 : CacheEquation 26 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(26 < 6)), load_entry_26]
  change forkRow [placeRow ⟨0, 4, 6, 4⟩ (denote cache_0), placeRow ⟨6, 0, 6, 5⟩ (denote cache_6)] = denote cache_26
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_26

theorem verified_row_27 : fork [place ⟨0, 6, 5, 4⟩ cache_0, place ⟨6, 4, 0, 5⟩ cache_6] = cache_27 := by
  decide +kernel

theorem load_entry_27 : entryAt 27 = entry_27 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_27 : CacheEquation 27 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(27 < 6)), load_entry_27]
  change forkRow [placeRow ⟨0, 6, 5, 4⟩ (denote cache_0), placeRow ⟨6, 4, 0, 5⟩ (denote cache_6)] = denote cache_27
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_27

theorem verified_row_28 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨0, 6, 6, 4⟩ cache_0] = cache_28 := by
  decide +kernel

theorem load_entry_28 : entryAt 28 = entry_28 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_28 : CacheEquation 28 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(28 < 6)), load_entry_28]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨0, 6, 6, 4⟩ (denote cache_0)] = denote cache_28
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_28

theorem verified_row_29 : fork [place ⟨1, 4, 7, 3⟩ cache_1, place ⟨6, 3, 4, 5⟩ cache_6] = cache_29 := by
  decide +kernel

theorem load_entry_29 : entryAt 29 = entry_29 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_29 : CacheEquation 29 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(29 < 6)), load_entry_29]
  change forkRow [placeRow ⟨1, 4, 7, 3⟩ (denote cache_1), placeRow ⟨6, 3, 4, 5⟩ (denote cache_6)] = denote cache_29
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_29

theorem verified_row_30 : fork [place ⟨0, 0, 1, 3⟩ cache_0, place ⟨14, 0, 6, 4⟩ cache_14] = cache_30 := by
  decide +kernel

theorem load_entry_30 : entryAt 30 = entry_30 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_30 : CacheEquation 30 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(30 < 6)), load_entry_30]
  change forkRow [placeRow ⟨0, 0, 1, 3⟩ (denote cache_0), placeRow ⟨14, 0, 6, 4⟩ (denote cache_14)] = denote cache_30
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_30

theorem verified_row_31 : fork [place ⟨0, 0, 1, 4⟩ cache_0, place ⟨17, 0, 6, 5⟩ cache_17] = cache_31 := by
  decide +kernel

theorem load_entry_31 : entryAt 31 = entry_31 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_31 : CacheEquation 31 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(31 < 6)), load_entry_31]
  change forkRow [placeRow ⟨0, 0, 1, 4⟩ (denote cache_0), placeRow ⟨17, 0, 6, 5⟩ (denote cache_17)] = denote cache_31
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_31

theorem verified_row_32 : fork [place ⟨0, 4, 8, 3⟩ cache_0, place ⟨6, 3, 4, 5⟩ cache_6] = cache_32 := by
  decide +kernel

theorem load_entry_32 : entryAt 32 = entry_32 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_32 : CacheEquation 32 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(32 < 6)), load_entry_32]
  change forkRow [placeRow ⟨0, 4, 8, 3⟩ (denote cache_0), placeRow ⟨6, 3, 4, 5⟩ (denote cache_6)] = denote cache_32
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_32

theorem verified_row_33 : fork [place ⟨0, 0, 2, 4⟩ cache_0, place ⟨17, 0, 7, 5⟩ cache_17] = cache_33 := by
  decide +kernel

theorem load_entry_33 : entryAt 33 = entry_33 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_33 : CacheEquation 33 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(33 < 6)), load_entry_33]
  change forkRow [placeRow ⟨0, 0, 2, 4⟩ (denote cache_0), placeRow ⟨17, 0, 7, 5⟩ (denote cache_17)] = denote cache_33
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_33

theorem verified_row_34 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨1, 6, 5, 4⟩ cache_1] = cache_34 := by
  decide +kernel

theorem load_entry_34 : entryAt 34 = entry_34 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_34 : CacheEquation 34 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(34 < 6)), load_entry_34]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨1, 6, 5, 4⟩ (denote cache_1)] = denote cache_34
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_34

theorem verified_row_35 : fork [place ⟨0, 0, 2, 4⟩ cache_0, place ⟨14, 0, 7, 5⟩ cache_14] = cache_35 := by
  decide +kernel

theorem load_entry_35 : entryAt 35 = entry_35 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_35 : CacheEquation 35 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(35 < 6)), load_entry_35]
  change forkRow [placeRow ⟨0, 0, 2, 4⟩ (denote cache_0), placeRow ⟨14, 0, 7, 5⟩ (denote cache_14)] = denote cache_35
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_35

theorem verified_row_36 : fork [place ⟨0, 0, 3, 4⟩ cache_0, place ⟨17, 0, 8, 5⟩ cache_17] = cache_36 := by
  decide +kernel

theorem load_entry_36 : entryAt 36 = entry_36 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_36 : CacheEquation 36 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(36 < 6)), load_entry_36]
  change forkRow [placeRow ⟨0, 0, 3, 4⟩ (denote cache_0), placeRow ⟨17, 0, 8, 5⟩ (denote cache_17)] = denote cache_36
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_36

theorem verified_row_37 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨2, 4, 6, 3⟩ cache_2] = cache_37 := by
  decide +kernel

theorem load_entry_37 : entryAt 37 = entry_37 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_37 : CacheEquation 37 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(37 < 6)), load_entry_37]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨2, 4, 6, 3⟩ (denote cache_2)] = denote cache_37
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_37

theorem verified_row_38 : fork [place ⟨3, 0, 3, 3⟩ cache_3, place ⟨16, 0, 2, 4⟩ cache_16] = cache_38 := by
  decide +kernel

theorem load_entry_38 : entryAt 38 = entry_38 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_38 : CacheEquation 38 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(38 < 6)), load_entry_38]
  change forkRow [placeRow ⟨3, 0, 3, 3⟩ (denote cache_3), placeRow ⟨16, 0, 2, 4⟩ (denote cache_16)] = denote cache_38
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_38

theorem verified_row_39 : fork [place ⟨0, 0, 1, 3⟩ cache_0, place ⟨17, 0, 6, 4⟩ cache_17] = cache_39 := by
  decide +kernel

theorem load_entry_39 : entryAt 39 = entry_39 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_39 : CacheEquation 39 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(39 < 6)), load_entry_39]
  change forkRow [placeRow ⟨0, 0, 1, 3⟩ (denote cache_0), placeRow ⟨17, 0, 6, 4⟩ (denote cache_17)] = denote cache_39
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_39

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_Equations01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

theorem verified_row_40 : fork [place ⟨3, 0, 4, 3⟩ cache_3, place ⟨16, 0, 3, 4⟩ cache_16] = cache_40 := by
  decide +kernel

theorem load_entry_40 : entryAt 40 = entry_40 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_40 : CacheEquation 40 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(40 < 6)), load_entry_40]
  change forkRow [placeRow ⟨3, 0, 4, 3⟩ (denote cache_3), placeRow ⟨16, 0, 3, 4⟩ (denote cache_16)] = denote cache_40
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_40

theorem verified_row_41 : fork [place ⟨6, 3, 3, 5⟩ cache_6, place ⟨1, 4, 6, 3⟩ cache_1] = cache_41 := by
  decide +kernel

theorem load_entry_41 : entryAt 41 = entry_41 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_41 : CacheEquation 41 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(41 < 6)), load_entry_41]
  change forkRow [placeRow ⟨6, 3, 3, 5⟩ (denote cache_6), placeRow ⟨1, 4, 6, 3⟩ (denote cache_1)] = denote cache_41
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_41

theorem verified_row_42 : fork [place ⟨0, 6, 6, 4⟩ cache_0, place ⟨6, 4, 1, 5⟩ cache_6] = cache_42 := by
  decide +kernel

theorem load_entry_42 : entryAt 42 = entry_42 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_42 : CacheEquation 42 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(42 < 6)), load_entry_42]
  change forkRow [placeRow ⟨0, 6, 6, 4⟩ (denote cache_0), placeRow ⟨6, 4, 1, 5⟩ (denote cache_6)] = denote cache_42
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_42

theorem verified_row_43 : fork [place ⟨2, 4, 5, 3⟩ cache_2, place ⟨6, 3, 3, 5⟩ cache_6] = cache_43 := by
  decide +kernel

theorem load_entry_43 : entryAt 43 = entry_43 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_43 : CacheEquation 43 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(43 < 6)), load_entry_43]
  change forkRow [placeRow ⟨2, 4, 5, 3⟩ (denote cache_2), placeRow ⟨6, 3, 3, 5⟩ (denote cache_6)] = denote cache_43
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_43

theorem verified_row_44 : fork [place ⟨4, 4, 1, 5⟩ cache_4, place ⟨7, 0, 4, 5⟩ cache_7] = cache_44 := by
  decide +kernel

theorem load_entry_44 : entryAt 44 = entry_44 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_44 : CacheEquation 44 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(44 < 6)), load_entry_44]
  change forkRow [placeRow ⟨4, 4, 1, 5⟩ (denote cache_4), placeRow ⟨7, 0, 4, 5⟩ (denote cache_7)] = denote cache_44
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_44

theorem verified_row_45 : fork [place ⟨6, 4, 0, 5⟩ cache_6, place ⟨7, 0, 4, 5⟩ cache_7] = cache_45 := by
  decide +kernel

theorem load_entry_45 : entryAt 45 = entry_45 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_45 : CacheEquation 45 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(45 < 6)), load_entry_45]
  change forkRow [placeRow ⟨6, 4, 0, 5⟩ (denote cache_6), placeRow ⟨7, 0, 4, 5⟩ (denote cache_7)] = denote cache_45
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_45

theorem verified_row_46 : fork [place ⟨6, 6, 0, 3⟩ cache_6, place ⟨7, 0, 4, 5⟩ cache_7] = cache_46 := by
  decide +kernel

theorem load_entry_46 : entryAt 46 = entry_46 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_46 : CacheEquation 46 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(46 < 6)), load_entry_46]
  change forkRow [placeRow ⟨6, 6, 0, 3⟩ (denote cache_6), placeRow ⟨7, 0, 4, 5⟩ (denote cache_7)] = denote cache_46
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_46

theorem verified_row_47 : fork [place ⟨6, 3, 3, 5⟩ cache_6, place ⟨6, 2, 7, 3⟩ cache_6] = cache_47 := by
  decide +kernel

theorem load_entry_47 : entryAt 47 = entry_47 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_47 : CacheEquation 47 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(47 < 6)), load_entry_47]
  change forkRow [placeRow ⟨6, 3, 3, 5⟩ (denote cache_6), placeRow ⟨6, 2, 7, 3⟩ (denote cache_6)] = denote cache_47
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_47

theorem verified_row_48 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨6, 2, 8, 3⟩ cache_6] = cache_48 := by
  decide +kernel

theorem load_entry_48 : entryAt 48 = entry_48 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_48 : CacheEquation 48 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(48 < 6)), load_entry_48]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨6, 2, 8, 3⟩ (denote cache_6)] = denote cache_48
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_48

theorem verified_row_49 : fork [place ⟨4, 7, 3, 1⟩ cache_4, place ⟨7, 1, 5, 4⟩ cache_7] = cache_49 := by
  decide +kernel

theorem load_entry_49 : entryAt 49 = entry_49 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_49 : CacheEquation 49 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(49 < 6)), load_entry_49]
  change forkRow [placeRow ⟨4, 7, 3, 1⟩ (denote cache_4), placeRow ⟨7, 1, 5, 4⟩ (denote cache_7)] = denote cache_49
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_49

theorem verified_row_50 : fork [place ⟨6, 3, 3, 5⟩ cache_6, place ⟨7, 1, 5, 4⟩ cache_7] = cache_50 := by
  decide +kernel

theorem load_entry_50 : entryAt 50 = entry_50 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_50 : CacheEquation 50 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(50 < 6)), load_entry_50]
  change forkRow [placeRow ⟨6, 3, 3, 5⟩ (denote cache_6), placeRow ⟨7, 1, 5, 4⟩ (denote cache_7)] = denote cache_50
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_50

theorem verified_row_51 : fork [place ⟨10, 2, 5, 3⟩ cache_10, place ⟨10, 0, 5, 4⟩ cache_10, place ⟨26, 2, 3, 4⟩ cache_26, place ⟨26, 0, 3, 3⟩ cache_26] = cache_51 := by
  decide +kernel

theorem load_entry_51 : entryAt 51 = entry_51 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_51 : CacheEquation 51 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(51 < 6)), load_entry_51]
  change forkRow [placeRow ⟨10, 2, 5, 3⟩ (denote cache_10), placeRow ⟨10, 0, 5, 4⟩ (denote cache_10), placeRow ⟨26, 2, 3, 4⟩ (denote cache_26), placeRow ⟨26, 0, 3, 3⟩ (denote cache_26)] = denote cache_51
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_51

theorem verified_row_52 : fork [place ⟨0, 0, 0, 3⟩ cache_0, place ⟨0, 4, 7, 3⟩ cache_0] = cache_52 := by
  decide +kernel

theorem load_entry_52 : entryAt 52 = entry_52 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_52 : CacheEquation 52 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(52 < 6)), load_entry_52]
  change forkRow [placeRow ⟨0, 0, 0, 3⟩ (denote cache_0), placeRow ⟨0, 4, 7, 3⟩ (denote cache_0)] = denote cache_52
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_52

theorem verified_row_53 : fork [place ⟨6, 4, 3, 4⟩ cache_6, place ⟨3, 1, 4, 5⟩ cache_3] = cache_53 := by
  decide +kernel

theorem load_entry_53 : entryAt 53 = entry_53 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_53 : CacheEquation 53 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(53 < 6)), load_entry_53]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (denote cache_6), placeRow ⟨3, 1, 4, 5⟩ (denote cache_3)] = denote cache_53
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_53

theorem verified_row_54 : fork [place ⟨22, 0, 2, 3⟩ cache_22, place ⟨3, 6, 1, 4⟩ cache_3] = cache_54 := by
  decide +kernel

theorem load_entry_54 : entryAt 54 = entry_54 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_54 : CacheEquation 54 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(54 < 6)), load_entry_54]
  change forkRow [placeRow ⟨22, 0, 2, 3⟩ (denote cache_22), placeRow ⟨3, 6, 1, 4⟩ (denote cache_3)] = denote cache_54
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_54

theorem verified_row_55 : fork [place ⟨7, 4, 0, 5⟩ cache_7, place ⟨7, 0, 4, 5⟩ cache_7] = cache_55 := by
  decide +kernel

theorem load_entry_55 : entryAt 55 = entry_55 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_55 : CacheEquation 55 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(55 < 6)), load_entry_55]
  change forkRow [placeRow ⟨7, 4, 0, 5⟩ (denote cache_7), placeRow ⟨7, 0, 4, 5⟩ (denote cache_7)] = denote cache_55
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_55

theorem verified_row_56 : fork [place ⟨7, 4, 0, 5⟩ cache_7, place ⟨7, 6, 0, 3⟩ cache_7] = cache_56 := by
  decide +kernel

theorem load_entry_56 : entryAt 56 = entry_56 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_56 : CacheEquation 56 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(56 < 6)), load_entry_56]
  change forkRow [placeRow ⟨7, 4, 0, 5⟩ (denote cache_7), placeRow ⟨7, 6, 0, 3⟩ (denote cache_7)] = denote cache_56
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_56

theorem verified_row_57 : fork [place ⟨0, 6, 5, 4⟩ cache_0, place ⟨7, 0, 4, 5⟩ cache_7] = cache_57 := by
  decide +kernel

theorem load_entry_57 : entryAt 57 = entry_57 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_57 : CacheEquation 57 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(57 < 6)), load_entry_57]
  change forkRow [placeRow ⟨0, 6, 5, 4⟩ (denote cache_0), placeRow ⟨7, 0, 4, 5⟩ (denote cache_7)] = denote cache_57
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_57

theorem verified_row_58 : fork [place ⟨0, 4, 5, 4⟩ cache_0, place ⟨7, 0, 4, 5⟩ cache_7] = cache_58 := by
  decide +kernel

theorem load_entry_58 : entryAt 58 = entry_58 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_58 : CacheEquation 58 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(58 < 6)), load_entry_58]
  change forkRow [placeRow ⟨0, 4, 5, 4⟩ (denote cache_0), placeRow ⟨7, 0, 4, 5⟩ (denote cache_7)] = denote cache_58
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_58

theorem verified_row_59 : fork [place ⟨0, 6, 5, 4⟩ cache_0, place ⟨7, 4, 0, 5⟩ cache_7] = cache_59 := by
  decide +kernel

theorem load_entry_59 : entryAt 59 = entry_59 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_59 : CacheEquation 59 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(59 < 6)), load_entry_59]
  change forkRow [placeRow ⟨0, 6, 5, 4⟩ (denote cache_0), placeRow ⟨7, 4, 0, 5⟩ (denote cache_7)] = denote cache_59
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_59

theorem verified_row_60 : fork [place ⟨6, 6, 1, 3⟩ cache_6, place ⟨49, 1, 6, 4⟩ cache_49] = cache_60 := by
  decide +kernel

theorem load_entry_60 : entryAt 60 = entry_60 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_60 : CacheEquation 60 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(60 < 6)), load_entry_60]
  change forkRow [placeRow ⟨6, 6, 1, 3⟩ (denote cache_6), placeRow ⟨49, 1, 6, 4⟩ (denote cache_49)] = denote cache_60
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_60

theorem verified_row_61 : fork [place ⟨6, 0, 5, 4⟩ cache_6, place ⟨14, 1, 4, 5⟩ cache_14] = cache_61 := by
  decide +kernel

theorem load_entry_61 : entryAt 61 = entry_61 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_61 : CacheEquation 61 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(61 < 6)), load_entry_61]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (denote cache_6), placeRow ⟨14, 1, 4, 5⟩ (denote cache_14)] = denote cache_61
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_61

theorem verified_row_62 : fork [place ⟨6, 6, 0, 3⟩ cache_6, place ⟨53, 0, 1, 5⟩ cache_53] = cache_62 := by
  decide +kernel

theorem load_entry_62 : entryAt 62 = entry_62 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_62 : CacheEquation 62 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(62 < 6)), load_entry_62]
  change forkRow [placeRow ⟨6, 6, 0, 3⟩ (denote cache_6), placeRow ⟨53, 0, 1, 5⟩ (denote cache_53)] = denote cache_62
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_62

theorem verified_row_63 : fork [place ⟨4, 3, 4, 3⟩ cache_4, place ⟨50, 0, 5, 4⟩ cache_50] = cache_63 := by
  decide +kernel

theorem load_entry_63 : entryAt 63 = entry_63 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_63 : CacheEquation 63 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(63 < 6)), load_entry_63]
  change forkRow [placeRow ⟨4, 3, 4, 3⟩ (denote cache_4), placeRow ⟨50, 0, 5, 4⟩ (denote cache_50)] = denote cache_63
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_63

theorem verified_row_64 : fork [place ⟨6, 6, 3, 4⟩ cache_6, place ⟨49, 1, 8, 5⟩ cache_49] = cache_64 := by
  decide +kernel

theorem load_entry_64 : entryAt 64 = entry_64 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_64 : CacheEquation 64 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(64 < 6)), load_entry_64]
  change forkRow [placeRow ⟨6, 6, 3, 4⟩ (denote cache_6), placeRow ⟨49, 1, 8, 5⟩ (denote cache_49)] = denote cache_64
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_64

theorem verified_row_65 : fork [place ⟨6, 6, 0, 3⟩ cache_6, place ⟨49, 1, 5, 4⟩ cache_49] = cache_65 := by
  decide +kernel

theorem load_entry_65 : entryAt 65 = entry_65 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_65 : CacheEquation 65 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(65 < 6)), load_entry_65]
  change forkRow [placeRow ⟨6, 6, 0, 3⟩ (denote cache_6), placeRow ⟨49, 1, 5, 4⟩ (denote cache_49)] = denote cache_65
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_65

theorem verified_row_66 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨53, 5, 6, 4⟩ cache_53] = cache_66 := by
  decide +kernel

theorem load_entry_66 : entryAt 66 = entry_66 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_66 : CacheEquation 66 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(66 < 6)), load_entry_66]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨53, 5, 6, 4⟩ (denote cache_53)] = denote cache_66
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_66

theorem verified_row_67 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨9, 2, 5, 4⟩ cache_9] = cache_67 := by
  decide +kernel

theorem load_entry_67 : entryAt 67 = entry_67 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_67 : CacheEquation 67 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(67 < 6)), load_entry_67]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨9, 2, 5, 4⟩ (denote cache_9)] = denote cache_67
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_67

theorem verified_row_68 : fork [place ⟨6, 4, 0, 5⟩ cache_6, place ⟨44, 0, 5, 4⟩ cache_44] = cache_68 := by
  decide +kernel

theorem load_entry_68 : entryAt 68 = entry_68 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_68 : CacheEquation 68 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(68 < 6)), load_entry_68]
  change forkRow [placeRow ⟨6, 4, 0, 5⟩ (denote cache_6), placeRow ⟨44, 0, 5, 4⟩ (denote cache_44)] = denote cache_68
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_68

theorem verified_row_69 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨34, 0, 6, 5⟩ cache_34] = cache_69 := by
  decide +kernel

theorem load_entry_69 : entryAt 69 = entry_69 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_69 : CacheEquation 69 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(69 < 6)), load_entry_69]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨34, 0, 6, 5⟩ (denote cache_34)] = denote cache_69
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_69

theorem verified_row_70 : fork [place ⟨4, 3, 4, 3⟩ cache_4, place ⟨41, 0, 5, 4⟩ cache_41] = cache_70 := by
  decide +kernel

theorem load_entry_70 : entryAt 70 = entry_70 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_70 : CacheEquation 70 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(70 < 6)), load_entry_70]
  change forkRow [placeRow ⟨4, 3, 4, 3⟩ (denote cache_4), placeRow ⟨41, 0, 5, 4⟩ (denote cache_41)] = denote cache_70
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_70

theorem verified_row_71 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨23, 2, 4, 3⟩ cache_23] = cache_71 := by
  decide +kernel

theorem load_entry_71 : entryAt 71 = entry_71 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_71 : CacheEquation 71 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(71 < 6)), load_entry_71]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨23, 2, 4, 3⟩ (denote cache_23)] = denote cache_71
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_71

theorem verified_row_72 : fork [place ⟨0, 5, 3, 8⟩ cache_0, place ⟨8, 6, 5, 4⟩ cache_8] = cache_72 := by
  decide +kernel

theorem load_entry_72 : entryAt 72 = entry_72 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_72 : CacheEquation 72 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(72 < 6)), load_entry_72]
  change forkRow [placeRow ⟨0, 5, 3, 8⟩ (denote cache_0), placeRow ⟨8, 6, 5, 4⟩ (denote cache_8)] = denote cache_72
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_72

theorem verified_row_73 : fork [place ⟨4, 3, 3, 4⟩ cache_4, place ⟨50, 0, 4, 5⟩ cache_50] = cache_73 := by
  decide +kernel

theorem load_entry_73 : entryAt 73 = entry_73 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_73 : CacheEquation 73 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(73 < 6)), load_entry_73]
  change forkRow [placeRow ⟨4, 3, 3, 4⟩ (denote cache_4), placeRow ⟨50, 0, 4, 5⟩ (denote cache_50)] = denote cache_73
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_73

theorem verified_row_74 : fork [place ⟨2, 7, 4, 3⟩ cache_2, place ⟨53, 0, 3, 3⟩ cache_53] = cache_74 := by
  decide +kernel

theorem load_entry_74 : entryAt 74 = entry_74 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_74 : CacheEquation 74 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(74 < 6)), load_entry_74]
  change forkRow [placeRow ⟨2, 7, 4, 3⟩ (denote cache_2), placeRow ⟨53, 0, 3, 3⟩ (denote cache_53)] = denote cache_74
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_74

theorem verified_row_75 : fork [place ⟨0, 0, 1, 3⟩ cache_0, place ⟨9, 0, 7, 3⟩ cache_9] = cache_75 := by
  decide +kernel

theorem load_entry_75 : entryAt 75 = entry_75 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_75 : CacheEquation 75 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(75 < 6)), load_entry_75]
  change forkRow [placeRow ⟨0, 0, 1, 3⟩ (denote cache_0), placeRow ⟨9, 0, 7, 3⟩ (denote cache_9)] = denote cache_75
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_75

theorem verified_row_76 : fork [place ⟨0, 7, 5, 7⟩ cache_0, place ⟨14, 0, 7, 5⟩ cache_14] = cache_76 := by
  decide +kernel

theorem load_entry_76 : entryAt 76 = entry_76 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_76 : CacheEquation 76 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(76 < 6)), load_entry_76]
  change forkRow [placeRow ⟨0, 7, 5, 7⟩ (denote cache_0), placeRow ⟨14, 0, 7, 5⟩ (denote cache_14)] = denote cache_76
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_76

theorem verified_row_77 : fork [place ⟨0, 5, 3, 7⟩ cache_0, place ⟨12, 0, 5, 4⟩ cache_12] = cache_77 := by
  decide +kernel

theorem load_entry_77 : entryAt 77 = entry_77 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_77 : CacheEquation 77 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(77 < 6)), load_entry_77]
  change forkRow [placeRow ⟨0, 5, 3, 7⟩ (denote cache_0), placeRow ⟨12, 0, 5, 4⟩ (denote cache_12)] = denote cache_77
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_77

theorem verified_row_78 : fork [place ⟨6, 4, 3, 4⟩ cache_6, place ⟨52, 0, 5, 4⟩ cache_52] = cache_78 := by
  decide +kernel

theorem load_entry_78 : entryAt 78 = entry_78 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_78 : CacheEquation 78 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(78 < 6)), load_entry_78]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (denote cache_6), placeRow ⟨52, 0, 5, 4⟩ (denote cache_52)] = denote cache_78
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_78

theorem verified_row_79 : fork [place ⟨6, 1, 5, 5⟩ cache_6, place ⟨48, 0, 3, 4⟩ cache_48] = cache_79 := by
  decide +kernel

theorem load_entry_79 : entryAt 79 = entry_79 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_79 : CacheEquation 79 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(79 < 6)), load_entry_79]
  change forkRow [placeRow ⟨6, 1, 5, 5⟩ (denote cache_6), placeRow ⟨48, 0, 3, 4⟩ (denote cache_48)] = denote cache_79
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_79

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_Equations02
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

theorem verified_row_80 : fork [place ⟨0, 6, 6, 4⟩ cache_0, place ⟨13, 4, 2, 4⟩ cache_13] = cache_80 := by
  decide +kernel

theorem load_entry_80 : entryAt 80 = entry_80 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_80 : CacheEquation 80 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(80 < 6)), load_entry_80]
  change forkRow [placeRow ⟨0, 6, 6, 4⟩ (denote cache_0), placeRow ⟨13, 4, 2, 4⟩ (denote cache_13)] = denote cache_80
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_80

theorem verified_row_81 : fork [place ⟨4, 3, 4, 3⟩ cache_4, place ⟨43, 0, 5, 4⟩ cache_43] = cache_81 := by
  decide +kernel

theorem load_entry_81 : entryAt 81 = entry_81 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_81 : CacheEquation 81 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(81 < 6)), load_entry_81]
  change forkRow [placeRow ⟨4, 3, 4, 3⟩ (denote cache_4), placeRow ⟨43, 0, 5, 4⟩ (denote cache_43)] = denote cache_81
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_81

theorem verified_row_82 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨36, 0, 1, 3⟩ cache_36] = cache_82 := by
  decide +kernel

theorem load_entry_82 : entryAt 82 = entry_82 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_82 : CacheEquation 82 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(82 < 6)), load_entry_82]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨36, 0, 1, 3⟩ (denote cache_36)] = denote cache_82
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_82

theorem verified_row_83 : fork [place ⟨0, 7, 5, 7⟩ cache_0, place ⟨67, 2, 6, 3⟩ cache_67] = cache_83 := by
  decide +kernel

theorem load_entry_83 : entryAt 83 = entry_83 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_83 : CacheEquation 83 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(83 < 6)), load_entry_83]
  change forkRow [placeRow ⟨0, 7, 5, 7⟩ (denote cache_0), placeRow ⟨67, 2, 6, 3⟩ (denote cache_67)] = denote cache_83
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_83

theorem verified_row_84 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨67, 0, 6, 4⟩ cache_67] = cache_84 := by
  decide +kernel

theorem load_entry_84 : entryAt 84 = entry_84 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_84 : CacheEquation 84 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(84 < 6)), load_entry_84]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨67, 0, 6, 4⟩ (denote cache_67)] = denote cache_84
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_84

theorem verified_row_85 : fork [place ⟨9, 0, 6, 3⟩ cache_9, place ⟨8, 4, 5, 4⟩ cache_8] = cache_85 := by
  decide +kernel

theorem load_entry_85 : entryAt 85 = entry_85 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_85 : CacheEquation 85 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(85 < 6)), load_entry_85]
  change forkRow [placeRow ⟨9, 0, 6, 3⟩ (denote cache_9), placeRow ⟨8, 4, 5, 4⟩ (denote cache_8)] = denote cache_85
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_85

theorem verified_row_86 : fork [place ⟨0, 6, 5, 4⟩ cache_0, place ⟨67, 3, 1, 5⟩ cache_67] = cache_86 := by
  decide +kernel

theorem load_entry_86 : entryAt 86 = entry_86 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_86 : CacheEquation 86 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(86 < 6)), load_entry_86]
  change forkRow [placeRow ⟨0, 6, 5, 4⟩ (denote cache_0), placeRow ⟨67, 3, 1, 5⟩ (denote cache_67)] = denote cache_86
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_86

theorem verified_row_87 : fork [place ⟨0, 5, 3, 7⟩ cache_0, place ⟨24, 2, 5, 3⟩ cache_24] = cache_87 := by
  decide +kernel

theorem load_entry_87 : entryAt 87 = entry_87 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_87 : CacheEquation 87 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(87 < 6)), load_entry_87]
  change forkRow [placeRow ⟨0, 5, 3, 7⟩ (denote cache_0), placeRow ⟨24, 2, 5, 3⟩ (denote cache_24)] = denote cache_87
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_87

theorem verified_row_88 : fork [place ⟨0, 6, 6, 4⟩ cache_0, place ⟨67, 3, 2, 5⟩ cache_67] = cache_88 := by
  decide +kernel

theorem load_entry_88 : entryAt 88 = entry_88 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_88 : CacheEquation 88 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(88 < 6)), load_entry_88]
  change forkRow [placeRow ⟨0, 6, 6, 4⟩ (denote cache_0), placeRow ⟨67, 3, 2, 5⟩ (denote cache_67)] = denote cache_88
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_88

theorem verified_row_89 : fork [place ⟨8, 3, 3, 1⟩ cache_8, place ⟨7, 1, 5, 4⟩ cache_7] = cache_89 := by
  decide +kernel

theorem load_entry_89 : entryAt 89 = entry_89 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_89 : CacheEquation 89 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(89 < 6)), load_entry_89]
  change forkRow [placeRow ⟨8, 3, 3, 1⟩ (denote cache_8), placeRow ⟨7, 1, 5, 4⟩ (denote cache_7)] = denote cache_89
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_89

theorem verified_row_90 : fork [place ⟨31, 0, 3, 3⟩ cache_31, place ⟨54, 6, 0, 3⟩ cache_54, place ⟨54, 0, 5, 4⟩ cache_54, place ⟨31, 6, 2, 4⟩ cache_31] = cache_90 := by
  decide +kernel

theorem load_entry_90 : entryAt 90 = entry_90 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_90 : CacheEquation 90 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(90 < 6)), load_entry_90]
  change forkRow [placeRow ⟨31, 0, 3, 3⟩ (denote cache_31), placeRow ⟨54, 6, 0, 3⟩ (denote cache_54), placeRow ⟨54, 0, 5, 4⟩ (denote cache_54), placeRow ⟨31, 6, 2, 4⟩ (denote cache_31)] = denote cache_90
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_90

theorem verified_row_91 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨74, 5, 7, 3⟩ cache_74] = cache_91 := by
  decide +kernel

theorem load_entry_91 : entryAt 91 = entry_91 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_91 : CacheEquation 91 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(91 < 6)), load_entry_91]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨74, 5, 7, 3⟩ (denote cache_74)] = denote cache_91
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_91

theorem verified_row_92 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨33, 0, 2, 3⟩ cache_33] = cache_92 := by
  decide +kernel

theorem load_entry_92 : entryAt 92 = entry_92 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_92 : CacheEquation 92 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(92 < 6)), load_entry_92]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨33, 0, 2, 3⟩ (denote cache_33)] = denote cache_92
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_92

theorem verified_row_93 : fork [place ⟨4, 3, 4, 3⟩ cache_4, place ⟨47, 0, 5, 4⟩ cache_47] = cache_93 := by
  decide +kernel

theorem load_entry_93 : entryAt 93 = entry_93 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_93 : CacheEquation 93 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(93 < 6)), load_entry_93]
  change forkRow [placeRow ⟨4, 3, 4, 3⟩ (denote cache_4), placeRow ⟨47, 0, 5, 4⟩ (denote cache_47)] = denote cache_93
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_93

theorem verified_row_94 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨27, 3, 3, 6⟩ cache_27] = cache_94 := by
  decide +kernel

theorem load_entry_94 : entryAt 94 = entry_94 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_94 : CacheEquation 94 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(94 < 6)), load_entry_94]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨27, 3, 3, 6⟩ (denote cache_27)] = denote cache_94
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_94

theorem verified_row_95 : fork [place ⟨0, 5, 3, 7⟩ cache_0, place ⟨29, 0, 2, 5⟩ cache_29] = cache_95 := by
  decide +kernel

theorem load_entry_95 : entryAt 95 = entry_95 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_95 : CacheEquation 95 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(95 < 6)), load_entry_95]
  change forkRow [placeRow ⟨0, 5, 3, 7⟩ (denote cache_0), placeRow ⟨29, 0, 2, 5⟩ (denote cache_29)] = denote cache_95
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_95

theorem verified_row_96 : fork [place ⟨6, 1, 5, 5⟩ cache_6, place ⟨70, 0, 3, 5⟩ cache_70] = cache_96 := by
  decide +kernel

theorem load_entry_96 : entryAt 96 = entry_96 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_96 : CacheEquation 96 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(96 < 6)), load_entry_96]
  change forkRow [placeRow ⟨6, 1, 5, 5⟩ (denote cache_6), placeRow ⟨70, 0, 3, 5⟩ (denote cache_70)] = denote cache_96
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_96

theorem verified_row_97 : fork [place ⟨6, 6, 0, 3⟩ cache_6, place ⟨44, 0, 5, 4⟩ cache_44] = cache_97 := by
  decide +kernel

theorem load_entry_97 : entryAt 97 = entry_97 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_97 : CacheEquation 97 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(97 < 6)), load_entry_97]
  change forkRow [placeRow ⟨6, 6, 0, 3⟩ (denote cache_6), placeRow ⟨44, 0, 5, 4⟩ (denote cache_44)] = denote cache_97
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_97

theorem verified_row_98 : fork [place ⟨6, 6, 2, 3⟩ cache_6, place ⟨44, 0, 7, 4⟩ cache_44] = cache_98 := by
  decide +kernel

theorem load_entry_98 : entryAt 98 = entry_98 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_98 : CacheEquation 98 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(98 < 6)), load_entry_98]
  change forkRow [placeRow ⟨6, 6, 2, 3⟩ (denote cache_6), placeRow ⟨44, 0, 7, 4⟩ (denote cache_44)] = denote cache_98
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_98

theorem verified_row_99 : fork [place ⟨2, 1, 3, 2⟩ cache_2, place ⟨24, 0, 5, 4⟩ cache_24] = cache_99 := by
  decide +kernel

theorem load_entry_99 : entryAt 99 = entry_99 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_99 : CacheEquation 99 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(99 < 6)), load_entry_99]
  change forkRow [placeRow ⟨2, 1, 3, 2⟩ (denote cache_2), placeRow ⟨24, 0, 5, 4⟩ (denote cache_24)] = denote cache_99
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_99

theorem verified_row_100 : fork [place ⟨0, 6, 5, 4⟩ cache_0, place ⟨48, 0, 1, 4⟩ cache_48] = cache_100 := by
  decide +kernel

theorem load_entry_100 : entryAt 100 = entry_100 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_100 : CacheEquation 100 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(100 < 6)), load_entry_100]
  change forkRow [placeRow ⟨0, 6, 5, 4⟩ (denote cache_0), placeRow ⟨48, 0, 1, 4⟩ (denote cache_48)] = denote cache_100
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_100

theorem verified_row_101 : fork [place ⟨0, 7, 4, 6⟩ cache_0, place ⟨24, 0, 5, 4⟩ cache_24] = cache_101 := by
  decide +kernel

theorem load_entry_101 : entryAt 101 = entry_101 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_101 : CacheEquation 101 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(101 < 6)), load_entry_101]
  change forkRow [placeRow ⟨0, 7, 4, 6⟩ (denote cache_0), placeRow ⟨24, 0, 5, 4⟩ (denote cache_24)] = denote cache_101
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_101

theorem verified_row_102 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨25, 2, 6, 3⟩ cache_25] = cache_102 := by
  decide +kernel

theorem load_entry_102 : entryAt 102 = entry_102 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_102 : CacheEquation 102 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(102 < 6)), load_entry_102]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨25, 2, 6, 3⟩ (denote cache_25)] = denote cache_102
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_102

theorem verified_row_103 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨71, 0, 6, 4⟩ cache_71] = cache_103 := by
  decide +kernel

theorem load_entry_103 : entryAt 103 = entry_103 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_103 : CacheEquation 103 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(103 < 6)), load_entry_103]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨71, 0, 6, 4⟩ (denote cache_71)] = denote cache_103
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_103

theorem verified_row_104 : fork [place ⟨6, 0, 5, 4⟩ cache_6, place ⟨75, 0, 3, 4⟩ cache_75] = cache_104 := by
  decide +kernel

theorem load_entry_104 : entryAt 104 = entry_104 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_104 : CacheEquation 104 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(104 < 6)), load_entry_104]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (denote cache_6), placeRow ⟨75, 0, 3, 4⟩ (denote cache_75)] = denote cache_104
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_104

theorem verified_row_105 : fork [place ⟨6, 5, 4, 3⟩ cache_6, place ⟨77, 0, 4, 5⟩ cache_77] = cache_105 := by
  decide +kernel

theorem load_entry_105 : entryAt 105 = entry_105 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_105 : CacheEquation 105 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(105 < 6)), load_entry_105]
  change forkRow [placeRow ⟨6, 5, 4, 3⟩ (denote cache_6), placeRow ⟨77, 0, 4, 5⟩ (denote cache_77)] = denote cache_105
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_105

theorem verified_row_106 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨36, 6, 5, 4⟩ cache_36] = cache_106 := by
  decide +kernel

theorem load_entry_106 : entryAt 106 = entry_106 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_106 : CacheEquation 106 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(106 < 6)), load_entry_106]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨36, 6, 5, 4⟩ (denote cache_36)] = denote cache_106
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_106

theorem verified_row_107 : fork [place ⟨6, 6, 0, 3⟩ cache_6, place ⟨63, 1, 5, 3⟩ cache_63] = cache_107 := by
  decide +kernel

theorem load_entry_107 : entryAt 107 = entry_107 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_107 : CacheEquation 107 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(107 < 6)), load_entry_107]
  change forkRow [placeRow ⟨6, 6, 0, 3⟩ (denote cache_6), placeRow ⟨63, 1, 5, 3⟩ (denote cache_63)] = denote cache_107
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_107

theorem verified_row_108 : fork [place ⟨4, 6, 1, 3⟩ cache_4, place ⟨63, 1, 5, 3⟩ cache_63] = cache_108 := by
  decide +kernel

theorem load_entry_108 : entryAt 108 = entry_108 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_108 : CacheEquation 108 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(108 < 6)), load_entry_108]
  change forkRow [placeRow ⟨4, 6, 1, 3⟩ (denote cache_4), placeRow ⟨63, 1, 5, 3⟩ (denote cache_63)] = denote cache_108
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_108

theorem verified_row_109 : fork [place ⟨4, 6, 1, 3⟩ cache_4, place ⟨55, 0, 5, 4⟩ cache_55] = cache_109 := by
  decide +kernel

theorem load_entry_109 : entryAt 109 = entry_109 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_109 : CacheEquation 109 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(109 < 6)), load_entry_109]
  change forkRow [placeRow ⟨4, 6, 1, 3⟩ (denote cache_4), placeRow ⟨55, 0, 5, 4⟩ (denote cache_55)] = denote cache_109
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_109

theorem verified_row_110 : fork [place ⟨6, 6, 1, 3⟩ cache_6, place ⟨63, 1, 6, 3⟩ cache_63] = cache_110 := by
  decide +kernel

theorem load_entry_110 : entryAt 110 = entry_110 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_110 : CacheEquation 110 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(110 < 6)), load_entry_110]
  change forkRow [placeRow ⟨6, 6, 1, 3⟩ (denote cache_6), placeRow ⟨63, 1, 6, 3⟩ (denote cache_63)] = denote cache_110
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_110

theorem verified_row_111 : fork [place ⟨6, 7, 4, 3⟩ cache_6, place ⟨83, 0, 4, 5⟩ cache_83] = cache_111 := by
  decide +kernel

theorem load_entry_111 : entryAt 111 = entry_111 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_111 : CacheEquation 111 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(111 < 6)), load_entry_111]
  change forkRow [placeRow ⟨6, 7, 4, 3⟩ (denote cache_6), placeRow ⟨83, 0, 4, 5⟩ (denote cache_83)] = denote cache_111
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_111

theorem verified_row_112 : fork [place ⟨4, 1, 5, 4⟩ cache_4, place ⟨93, 0, 3, 5⟩ cache_93] = cache_112 := by
  decide +kernel

theorem load_entry_112 : entryAt 112 = entry_112 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_112 : CacheEquation 112 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(112 < 6)), load_entry_112]
  change forkRow [placeRow ⟨4, 1, 5, 4⟩ (denote cache_4), placeRow ⟨93, 0, 3, 5⟩ (denote cache_93)] = denote cache_112
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_112

theorem verified_row_113 : fork [place ⟨1, 6, 6, 4⟩ cache_1, place ⟨36, 6, 7, 5⟩ cache_36] = cache_113 := by
  decide +kernel

theorem load_entry_113 : entryAt 113 = entry_113 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_113 : CacheEquation 113 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(113 < 6)), load_entry_113]
  change forkRow [placeRow ⟨1, 6, 6, 4⟩ (denote cache_1), placeRow ⟨36, 6, 7, 5⟩ (denote cache_36)] = denote cache_113
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_113

theorem verified_row_114 : fork [place ⟨6, 0, 6, 5⟩ cache_6, place ⟨67, 3, 2, 5⟩ cache_67] = cache_114 := by
  decide +kernel

theorem load_entry_114 : entryAt 114 = entry_114 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_114 : CacheEquation 114 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(114 < 6)), load_entry_114]
  change forkRow [placeRow ⟨6, 0, 6, 5⟩ (denote cache_6), placeRow ⟨67, 3, 2, 5⟩ (denote cache_67)] = denote cache_114
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_114

theorem verified_row_115 : fork [place ⟨6, 2, 7, 3⟩ cache_6, place ⟨70, 7, 2, 5⟩ cache_70] = cache_115 := by
  decide +kernel

theorem load_entry_115 : entryAt 115 = entry_115 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_115 : CacheEquation 115 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(115 < 6)), load_entry_115]
  change forkRow [placeRow ⟨6, 2, 7, 3⟩ (denote cache_6), placeRow ⟨70, 7, 2, 5⟩ (denote cache_70)] = denote cache_115
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_115

theorem verified_row_116 : fork [place ⟨0, 7, 4, 6⟩ cache_0, place ⟨24, 2, 5, 4⟩ cache_24] = cache_116 := by
  decide +kernel

theorem load_entry_116 : entryAt 116 = entry_116 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_116 : CacheEquation 116 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(116 < 6)), load_entry_116]
  change forkRow [placeRow ⟨0, 7, 4, 6⟩ (denote cache_0), placeRow ⟨24, 2, 5, 4⟩ (denote cache_24)] = denote cache_116
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_116

theorem verified_row_117 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨100, 0, 5, 4⟩ cache_100] = cache_117 := by
  decide +kernel

theorem load_entry_117 : entryAt 117 = entry_117 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_117 : CacheEquation 117 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(117 < 6)), load_entry_117]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨100, 0, 5, 4⟩ (denote cache_100)] = denote cache_117
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_117

theorem verified_row_118 : fork [place ⟨4, 7, 3, 1⟩ cache_4, place ⟨61, 1, 5, 4⟩ cache_61] = cache_118 := by
  decide +kernel

theorem load_entry_118 : entryAt 118 = entry_118 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_118 : CacheEquation 118 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(118 < 6)), load_entry_118]
  change forkRow [placeRow ⟨4, 7, 3, 1⟩ (denote cache_4), placeRow ⟨61, 1, 5, 4⟩ (denote cache_61)] = denote cache_118
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_118

theorem verified_row_119 : fork [place ⟨6, 6, 1, 3⟩ cache_6, place ⟨55, 0, 6, 4⟩ cache_55] = cache_119 := by
  decide +kernel

theorem load_entry_119 : entryAt 119 = entry_119 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_119 : CacheEquation 119 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(119 < 6)), load_entry_119]
  change forkRow [placeRow ⟨6, 6, 1, 3⟩ (denote cache_6), placeRow ⟨55, 0, 6, 4⟩ (denote cache_55)] = denote cache_119
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_119

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_Equations03
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

theorem verified_row_120 : fork [place ⟨4, 0, 4, 5⟩ cache_4, place ⟨58, 2, 5, 4⟩ cache_58] = cache_120 := by
  decide +kernel

theorem load_entry_120 : entryAt 120 = entry_120 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_120 : CacheEquation 120 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(120 < 6)), load_entry_120]
  change forkRow [placeRow ⟨4, 0, 4, 5⟩ (denote cache_4), placeRow ⟨58, 2, 5, 4⟩ (denote cache_58)] = denote cache_120
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_120

theorem verified_row_121 : fork [place ⟨9, 3, 4, 5⟩ cache_9, place ⟨7, 1, 5, 4⟩ cache_7] = cache_121 := by
  decide +kernel

theorem load_entry_121 : entryAt 121 = entry_121 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_121 : CacheEquation 121 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(121 < 6)), load_entry_121]
  change forkRow [placeRow ⟨9, 3, 4, 5⟩ (denote cache_9), placeRow ⟨7, 1, 5, 4⟩ (denote cache_7)] = denote cache_121
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_121

theorem verified_row_122 : fork [place ⟨6, 6, 3, 3⟩ cache_6, place ⟨105, 1, 4, 5⟩ cache_105] = cache_122 := by
  decide +kernel

theorem load_entry_122 : entryAt 122 = entry_122 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_122 : CacheEquation 122 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(122 < 6)), load_entry_122]
  change forkRow [placeRow ⟨6, 6, 3, 3⟩ (denote cache_6), placeRow ⟨105, 1, 4, 5⟩ (denote cache_105)] = denote cache_122
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_122

theorem verified_row_123 : fork [place ⟨6, 6, 1, 3⟩ cache_6, place ⟨64, 2, 2, 5⟩ cache_64] = cache_123 := by
  decide +kernel

theorem load_entry_123 : entryAt 123 = entry_123 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_123 : CacheEquation 123 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(123 < 6)), load_entry_123]
  change forkRow [placeRow ⟨6, 6, 1, 3⟩ (denote cache_6), placeRow ⟨64, 2, 2, 5⟩ (denote cache_64)] = denote cache_123
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_123

theorem verified_row_124 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨31, 2, 5, 4⟩ cache_31] = cache_124 := by
  decide +kernel

theorem load_entry_124 : entryAt 124 = entry_124 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_124 : CacheEquation 124 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(124 < 6)), load_entry_124]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨31, 2, 5, 4⟩ (denote cache_31)] = denote cache_124
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_124

theorem verified_row_125 : fork [place ⟨3, 0, 4, 3⟩ cache_3, place ⟨31, 2, 4, 5⟩ cache_31] = cache_125 := by
  decide +kernel

theorem load_entry_125 : entryAt 125 = entry_125 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_125 : CacheEquation 125 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(125 < 6)), load_entry_125]
  change forkRow [placeRow ⟨3, 0, 4, 3⟩ (denote cache_3), placeRow ⟨31, 2, 4, 5⟩ (denote cache_31)] = denote cache_125
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_125

theorem verified_row_126 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨46, 1, 5, 7⟩ cache_46] = cache_126 := by
  decide +kernel

theorem load_entry_126 : entryAt 126 = entry_126 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_126 : CacheEquation 126 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(126 < 6)), load_entry_126]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨46, 1, 5, 7⟩ (denote cache_46)] = denote cache_126
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_126

theorem verified_row_127 : fork [place ⟨7, 0, 4, 5⟩ cache_7, place ⟨44, 2, 5, 4⟩ cache_44] = cache_127 := by
  decide +kernel

theorem load_entry_127 : entryAt 127 = entry_127 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_127 : CacheEquation 127 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(127 < 6)), load_entry_127]
  change forkRow [placeRow ⟨7, 0, 4, 5⟩ (denote cache_7), placeRow ⟨44, 2, 5, 4⟩ (denote cache_44)] = denote cache_127
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_127

theorem verified_row_128 : fork [place ⟨9, 6, 1, 5⟩ cache_9, place ⟨57, 0, 6, 5⟩ cache_57] = cache_128 := by
  decide +kernel

theorem load_entry_128 : entryAt 128 = entry_128 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_128 : CacheEquation 128 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(128 < 6)), load_entry_128]
  change forkRow [placeRow ⟨9, 6, 1, 5⟩ (denote cache_9), placeRow ⟨57, 0, 6, 5⟩ (denote cache_57)] = denote cache_128
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_128

theorem verified_row_129 : fork [place ⟨6, 4, 2, 5⟩ cache_6, place ⟨58, 1, 3, 6⟩ cache_58] = cache_129 := by
  decide +kernel

theorem load_entry_129 : entryAt 129 = entry_129 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_129 : CacheEquation 129 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(129 < 6)), load_entry_129]
  change forkRow [placeRow ⟨6, 4, 2, 5⟩ (denote cache_6), placeRow ⟨58, 1, 3, 6⟩ (denote cache_58)] = denote cache_129
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_129

theorem verified_row_130 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨60, 0, 5, 4⟩ cache_60] = cache_130 := by
  decide +kernel

theorem load_entry_130 : entryAt 130 = entry_130 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_130 : CacheEquation 130 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(130 < 6)), load_entry_130]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨60, 0, 5, 4⟩ (denote cache_60)] = denote cache_130
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_130

theorem verified_row_131 : fork [place ⟨45, 3, 4, 5⟩ cache_45, place ⟨7, 1, 5, 4⟩ cache_7] = cache_131 := by
  decide +kernel

theorem load_entry_131 : entryAt 131 = entry_131 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_131 : CacheEquation 131 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(131 < 6)), load_entry_131]
  change forkRow [placeRow ⟨45, 3, 4, 5⟩ (denote cache_45), placeRow ⟨7, 1, 5, 4⟩ (denote cache_7)] = denote cache_131
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_131

theorem verified_row_132 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨89, 0, 5, 6⟩ cache_89] = cache_132 := by
  decide +kernel

theorem load_entry_132 : entryAt 132 = entry_132 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_132 : CacheEquation 132 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(132 < 6)), load_entry_132]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨89, 0, 5, 6⟩ (denote cache_89)] = denote cache_132
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_132

theorem verified_row_133 : fork [place ⟨6, 7, 3, 1⟩ cache_6, place ⟨92, 0, 5, 5⟩ cache_92] = cache_133 := by
  decide +kernel

theorem load_entry_133 : entryAt 133 = entry_133 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_133 : CacheEquation 133 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(133 < 6)), load_entry_133]
  change forkRow [placeRow ⟨6, 7, 3, 1⟩ (denote cache_6), placeRow ⟨92, 0, 5, 5⟩ (denote cache_92)] = denote cache_133
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_133

theorem verified_row_134 : fork [place ⟨6, 7, 3, 0⟩ cache_6, place ⟨82, 0, 5, 4⟩ cache_82] = cache_134 := by
  decide +kernel

theorem load_entry_134 : entryAt 134 = entry_134 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_134 : CacheEquation 134 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(134 < 6)), load_entry_134]
  change forkRow [placeRow ⟨6, 7, 3, 0⟩ (denote cache_6), placeRow ⟨82, 0, 5, 4⟩ (denote cache_82)] = denote cache_134
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_134

theorem verified_row_135 : fork [place ⟨7, 0, 4, 5⟩ cache_7, place ⟨75, 4, 2, 5⟩ cache_75, place ⟨44, 0, 5, 4⟩ cache_44] = cache_135 := by
  decide +kernel

theorem load_entry_135 : entryAt 135 = entry_135 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_135 : CacheEquation 135 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(135 < 6)), load_entry_135]
  change forkRow [placeRow ⟨7, 0, 4, 5⟩ (denote cache_7), placeRow ⟨75, 4, 2, 5⟩ (denote cache_75), placeRow ⟨44, 0, 5, 4⟩ (denote cache_44)] = denote cache_135
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_135

theorem verified_row_136 : fork [place ⟨6, 3, 3, 7⟩ cache_6, place ⟨102, 2, 3, 3⟩ cache_102] = cache_136 := by
  decide +kernel

theorem load_entry_136 : entryAt 136 = entry_136 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_136 : CacheEquation 136 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(136 < 6)), load_entry_136]
  change forkRow [placeRow ⟨6, 3, 3, 7⟩ (denote cache_6), placeRow ⟨102, 2, 3, 3⟩ (denote cache_102)] = denote cache_136
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_136

theorem verified_row_137 : fork [place ⟨4, 1, 4, 3⟩ cache_4, place ⟨96, 0, 3, 4⟩ cache_96] = cache_137 := by
  decide +kernel

theorem load_entry_137 : entryAt 137 = entry_137 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_137 : CacheEquation 137 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(137 < 6)), load_entry_137]
  change forkRow [placeRow ⟨4, 1, 4, 3⟩ (denote cache_4), placeRow ⟨96, 0, 3, 4⟩ (denote cache_96)] = denote cache_137
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_137

theorem verified_row_138 : fork [place ⟨27, 0, 5, 4⟩ cache_27, place ⟨10, 1, 4, 7⟩ cache_10] = cache_138 := by
  decide +kernel

theorem load_entry_138 : entryAt 138 = entry_138 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_138 : CacheEquation 138 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(138 < 6)), load_entry_138]
  change forkRow [placeRow ⟨27, 0, 5, 4⟩ (denote cache_27), placeRow ⟨10, 1, 4, 7⟩ (denote cache_10)] = denote cache_138
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_138

theorem verified_row_139 : fork [place ⟨28, 1, 4, 5⟩ cache_28, place ⟨27, 0, 5, 4⟩ cache_27] = cache_139 := by
  decide +kernel

theorem load_entry_139 : entryAt 139 = entry_139 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_139 : CacheEquation 139 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(139 < 6)), load_entry_139]
  change forkRow [placeRow ⟨28, 1, 4, 5⟩ (denote cache_28), placeRow ⟨27, 0, 5, 4⟩ (denote cache_27)] = denote cache_139
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_139

theorem verified_row_140 : fork [place ⟨6, 7, 3, 2⟩ cache_6, place ⟨82, 0, 5, 6⟩ cache_82] = cache_140 := by
  decide +kernel

theorem load_entry_140 : entryAt 140 = entry_140 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_140 : CacheEquation 140 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(140 < 6)), load_entry_140]
  change forkRow [placeRow ⟨6, 7, 3, 2⟩ (denote cache_6), placeRow ⟨82, 0, 5, 6⟩ (denote cache_82)] = denote cache_140
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_140

theorem verified_row_141 : fork [place ⟨7, 0, 4, 5⟩ cache_7, place ⟨78, 2, 1, 3⟩ cache_78] = cache_141 := by
  decide +kernel

theorem load_entry_141 : entryAt 141 = entry_141 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_141 : CacheEquation 141 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(141 < 6)), load_entry_141]
  change forkRow [placeRow ⟨7, 0, 4, 5⟩ (denote cache_7), placeRow ⟨78, 2, 1, 3⟩ (denote cache_78)] = denote cache_141
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_141

theorem verified_row_142 : fork [place ⟨72, 4, 2, 3⟩ cache_72, place ⟨32, 1, 4, 3⟩ cache_32, place ⟨55, 2, 5, 4⟩ cache_55] = cache_142 := by
  decide +kernel

theorem load_entry_142 : entryAt 142 = entry_142 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_142 : CacheEquation 142 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(142 < 6)), load_entry_142]
  change forkRow [placeRow ⟨72, 4, 2, 3⟩ (denote cache_72), placeRow ⟨32, 1, 4, 3⟩ (denote cache_32), placeRow ⟨55, 2, 5, 4⟩ (denote cache_55)] = denote cache_142
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_142

theorem verified_row_143 : fork [place ⟨6, 6, 3, 4⟩ cache_6, place ⟨108, 0, 8, 5⟩ cache_108] = cache_143 := by
  decide +kernel

theorem load_entry_143 : entryAt 143 = entry_143 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_143 : CacheEquation 143 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(143 < 6)), load_entry_143]
  change forkRow [placeRow ⟨6, 6, 3, 4⟩ (denote cache_6), placeRow ⟨108, 0, 8, 5⟩ (denote cache_108)] = denote cache_143
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_143

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_Reconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

theorem cache_equations_range_0 : ∀ i, 0 ≤ i → i < 16 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_0
  · exact cache_equation_1
  · exact cache_equation_2
  · exact cache_equation_3
  · exact cache_equation_4
  · exact cache_equation_5
  · exact cache_equation_6
  · exact cache_equation_7
  · exact cache_equation_8
  · exact cache_equation_9
  · exact cache_equation_10
  · exact cache_equation_11
  · exact cache_equation_12
  · exact cache_equation_13
  · exact cache_equation_14
  · exact cache_equation_15

theorem cache_equations_range_16 : ∀ i, 16 ≤ i → i < 32 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_16
  · exact cache_equation_17
  · exact cache_equation_18
  · exact cache_equation_19
  · exact cache_equation_20
  · exact cache_equation_21
  · exact cache_equation_22
  · exact cache_equation_23
  · exact cache_equation_24
  · exact cache_equation_25
  · exact cache_equation_26
  · exact cache_equation_27
  · exact cache_equation_28
  · exact cache_equation_29
  · exact cache_equation_30
  · exact cache_equation_31

theorem cache_equations_range_32 : ∀ i, 32 ≤ i → i < 48 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_32
  · exact cache_equation_33
  · exact cache_equation_34
  · exact cache_equation_35
  · exact cache_equation_36
  · exact cache_equation_37
  · exact cache_equation_38
  · exact cache_equation_39
  · exact cache_equation_40
  · exact cache_equation_41
  · exact cache_equation_42
  · exact cache_equation_43
  · exact cache_equation_44
  · exact cache_equation_45
  · exact cache_equation_46
  · exact cache_equation_47

theorem cache_equations_range_48 : ∀ i, 48 ≤ i → i < 64 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_48
  · exact cache_equation_49
  · exact cache_equation_50
  · exact cache_equation_51
  · exact cache_equation_52
  · exact cache_equation_53
  · exact cache_equation_54
  · exact cache_equation_55
  · exact cache_equation_56
  · exact cache_equation_57
  · exact cache_equation_58
  · exact cache_equation_59
  · exact cache_equation_60
  · exact cache_equation_61
  · exact cache_equation_62
  · exact cache_equation_63

theorem cache_equations_range_64 : ∀ i, 64 ≤ i → i < 80 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_64
  · exact cache_equation_65
  · exact cache_equation_66
  · exact cache_equation_67
  · exact cache_equation_68
  · exact cache_equation_69
  · exact cache_equation_70
  · exact cache_equation_71
  · exact cache_equation_72
  · exact cache_equation_73
  · exact cache_equation_74
  · exact cache_equation_75
  · exact cache_equation_76
  · exact cache_equation_77
  · exact cache_equation_78
  · exact cache_equation_79

theorem cache_equations_range_80 : ∀ i, 80 ≤ i → i < 96 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_80
  · exact cache_equation_81
  · exact cache_equation_82
  · exact cache_equation_83
  · exact cache_equation_84
  · exact cache_equation_85
  · exact cache_equation_86
  · exact cache_equation_87
  · exact cache_equation_88
  · exact cache_equation_89
  · exact cache_equation_90
  · exact cache_equation_91
  · exact cache_equation_92
  · exact cache_equation_93
  · exact cache_equation_94
  · exact cache_equation_95

theorem cache_equations_range_96 : ∀ i, 96 ≤ i → i < 112 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_96
  · exact cache_equation_97
  · exact cache_equation_98
  · exact cache_equation_99
  · exact cache_equation_100
  · exact cache_equation_101
  · exact cache_equation_102
  · exact cache_equation_103
  · exact cache_equation_104
  · exact cache_equation_105
  · exact cache_equation_106
  · exact cache_equation_107
  · exact cache_equation_108
  · exact cache_equation_109
  · exact cache_equation_110
  · exact cache_equation_111

theorem cache_equations_range_112 : ∀ i, 112 ≤ i → i < 128 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_112
  · exact cache_equation_113
  · exact cache_equation_114
  · exact cache_equation_115
  · exact cache_equation_116
  · exact cache_equation_117
  · exact cache_equation_118
  · exact cache_equation_119
  · exact cache_equation_120
  · exact cache_equation_121
  · exact cache_equation_122
  · exact cache_equation_123
  · exact cache_equation_124
  · exact cache_equation_125
  · exact cache_equation_126
  · exact cache_equation_127

theorem cache_equations_range_128 : ∀ i, 128 ≤ i → i < 144 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_128
  · exact cache_equation_129
  · exact cache_equation_130
  · exact cache_equation_131
  · exact cache_equation_132
  · exact cache_equation_133
  · exact cache_equation_134
  · exact cache_equation_135
  · exact cache_equation_136
  · exact cache_equation_137
  · exact cache_equation_138
  · exact cache_equation_139
  · exact cache_equation_140
  · exact cache_equation_141
  · exact cache_equation_142
  · exact cache_equation_143

theorem cache_equations_range_0_32 : ∀ i, 0 ≤ i → i < 32 → CacheEquation i :=
  merge_ranges cache_equations_range_0 cache_equations_range_16

theorem cache_equations_range_32_64 : ∀ i, 32 ≤ i → i < 64 → CacheEquation i :=
  merge_ranges cache_equations_range_32 cache_equations_range_48

theorem cache_equations_range_0_64 : ∀ i, 0 ≤ i → i < 64 → CacheEquation i :=
  merge_ranges cache_equations_range_0_32 cache_equations_range_32_64

theorem cache_equations_range_64_96 : ∀ i, 64 ≤ i → i < 96 → CacheEquation i :=
  merge_ranges cache_equations_range_64 cache_equations_range_80

theorem cache_equations_range_112_144 : ∀ i, 112 ≤ i → i < 144 → CacheEquation i :=
  merge_ranges cache_equations_range_112 cache_equations_range_128

theorem cache_equations_range_96_144 : ∀ i, 96 ≤ i → i < 144 → CacheEquation i :=
  merge_ranges cache_equations_range_96 cache_equations_range_112_144

theorem cache_equations_range_64_144 : ∀ i, 64 ≤ i → i < 144 → CacheEquation i :=
  merge_ranges cache_equations_range_64_96 cache_equations_range_96_144

theorem cache_equations_range_0_144_oai : ∀ i, 0 ≤ i → i < 144 → CacheEquation i :=
  merge_ranges cache_equations_range_0_64 cache_equations_range_64_144

end SnakyCertificate.Check

end OAI
end

theorem solution : type_of% @OAI.SnakyCertificate.Check.cache_equations_range_0_144_oai := @OAI.SnakyCertificate.Check.cache_equations_range_0_144_oai
