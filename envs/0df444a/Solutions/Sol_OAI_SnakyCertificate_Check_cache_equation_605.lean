-- Prove2me | solution 1 for OAI.SnakyCertificate.Check.cache_equation_605
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T23:47:34.484657+00:00
-- url     : https://prove2.me/submissions/e49b3779-274e-44b1-bf91-c9bfa9724893

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

end SnakyCertificate

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_Equations15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

theorem verified_row_605 : fork [place ⟨400, 5, 4, 3⟩ cache_400, place ⟨383, 6, 3, 4⟩ cache_383, place ⟨530, 4, 4, 3⟩ cache_530, place ⟨596, 1, 3, 4⟩ cache_596, place ⟨522, 2, 4, 3⟩ cache_522, place ⟨598, 0, 4, 3⟩ cache_598, place ⟨537, 3, 3, 4⟩ cache_537, place ⟨520, 1, 4, 3⟩ cache_520, place ⟨550, 4, 4, 3⟩ cache_550] = cache_605 := by
  decide +kernel

theorem load_entry_605 : entryAt 605 = entry_605 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_605_oai : CacheEquation 605 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(605 < 6)), load_entry_605]
  change forkRow [placeRow ⟨400, 5, 4, 3⟩ (denote cache_400), placeRow ⟨383, 6, 3, 4⟩ (denote cache_383), placeRow ⟨530, 4, 4, 3⟩ (denote cache_530), placeRow ⟨596, 1, 3, 4⟩ (denote cache_596), placeRow ⟨522, 2, 4, 3⟩ (denote cache_522), placeRow ⟨598, 0, 4, 3⟩ (denote cache_598), placeRow ⟨537, 3, 3, 4⟩ (denote cache_537), placeRow ⟨520, 1, 4, 3⟩ (denote cache_520), placeRow ⟨550, 4, 4, 3⟩ (denote cache_550)] = denote cache_605
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_605

end SnakyCertificate.Check

end OAI
end

theorem solution : type_of% @OAI.SnakyCertificate.Check.cache_equation_605_oai := @OAI.SnakyCertificate.Check.cache_equation_605_oai
