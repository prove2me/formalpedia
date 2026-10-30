-- Prove2me | solution 1 for OAI.SnakyCertificate.Check.cache_equations_range_464_544
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T23:57:08.324602+00:00
-- url     : https://prove2.me/submissions/280e88c2-7367-4261-aa42-9adc182e2fcc

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
-- module Solutions.OAIQ114_SC.SnakyCertificate_Equations11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

theorem verified_row_464 : fork [place ⟨63, 0, 3, 5⟩ cache_63, place ⟨224, 0, 5, 4⟩ cache_224, place ⟨315, 0, 7, 3⟩ cache_315, place ⟨306, 0, 5, 5⟩ cache_306, place ⟨358, 0, 7, 3⟩ cache_358, place ⟨461, 0, 5, 5⟩ cache_461] = cache_464 := by
  decide +kernel

theorem load_entry_464 : entryAt 464 = entry_464 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_464 : CacheEquation 464 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(464 < 6)), load_entry_464]
  change forkRow [placeRow ⟨63, 0, 3, 5⟩ (denote cache_63), placeRow ⟨224, 0, 5, 4⟩ (denote cache_224), placeRow ⟨315, 0, 7, 3⟩ (denote cache_315), placeRow ⟨306, 0, 5, 5⟩ (denote cache_306), placeRow ⟨358, 0, 7, 3⟩ (denote cache_358), placeRow ⟨461, 0, 5, 5⟩ (denote cache_461)] = denote cache_464
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_464

theorem verified_row_465 : fork [place ⟨55, 3, 4, 5⟩ cache_55, place ⟨285, 0, 3, 4⟩ cache_285, place ⟨64, 1, 3, 1⟩ cache_64] = cache_465 := by
  decide +kernel

theorem load_entry_465 : entryAt 465 = entry_465 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_465 : CacheEquation 465 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(465 < 6)), load_entry_465]
  change forkRow [placeRow ⟨55, 3, 4, 5⟩ (denote cache_55), placeRow ⟨285, 0, 3, 4⟩ (denote cache_285), placeRow ⟨64, 1, 3, 1⟩ (denote cache_64)] = denote cache_465
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_465

theorem verified_row_466 : fork [place ⟨395, 4, 3, 4⟩ cache_395, place ⟨360, 4, 2, 6⟩ cache_360, place ⟨417, 1, 5, 4⟩ cache_417, place ⟨325, 4, 3, 4⟩ cache_325, place ⟨324, 4, 3, 5⟩ cache_324] = cache_466 := by
  decide +kernel

theorem load_entry_466 : entryAt 466 = entry_466 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_466 : CacheEquation 466 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(466 < 6)), load_entry_466]
  change forkRow [placeRow ⟨395, 4, 3, 4⟩ (denote cache_395), placeRow ⟨360, 4, 2, 6⟩ (denote cache_360), placeRow ⟨417, 1, 5, 4⟩ (denote cache_417), placeRow ⟨325, 4, 3, 4⟩ (denote cache_325), placeRow ⟨324, 4, 3, 5⟩ (denote cache_324)] = denote cache_466
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_466

theorem verified_row_467 : fork [place ⟨64, 7, 5, 7⟩ cache_64, place ⟨314, 6, 5, 4⟩ cache_314, place ⟨443, 1, 5, 7⟩ cache_443] = cache_467 := by
  decide +kernel

theorem load_entry_467 : entryAt 467 = entry_467 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_467 : CacheEquation 467 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(467 < 6)), load_entry_467]
  change forkRow [placeRow ⟨64, 7, 5, 7⟩ (denote cache_64), placeRow ⟨314, 6, 5, 4⟩ (denote cache_314), placeRow ⟨443, 1, 5, 7⟩ (denote cache_443)] = denote cache_467
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_467

theorem verified_row_468 : fork [place ⟨6, 6, 3, 4⟩ cache_6, place ⟨464, 0, 4, 7⟩ cache_464] = cache_468 := by
  decide +kernel

theorem load_entry_468 : entryAt 468 = entry_468 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_468 : CacheEquation 468 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(468 < 6)), load_entry_468]
  change forkRow [placeRow ⟨6, 6, 3, 4⟩ (denote cache_6), placeRow ⟨464, 0, 4, 7⟩ (denote cache_464)] = denote cache_468
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_468

theorem verified_row_469 : fork [place ⟨55, 5, 4, 3⟩ cache_55, place ⟨443, 1, 5, 7⟩ cache_443, place ⟨314, 6, 5, 4⟩ cache_314] = cache_469 := by
  decide +kernel

theorem load_entry_469 : entryAt 469 = entry_469 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_469 : CacheEquation 469 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(469 < 6)), load_entry_469]
  change forkRow [placeRow ⟨55, 5, 4, 3⟩ (denote cache_55), placeRow ⟨443, 1, 5, 7⟩ (denote cache_443), placeRow ⟨314, 6, 5, 4⟩ (denote cache_314)] = denote cache_469
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_469

theorem verified_row_470 : fork [place ⟨6, 4, 3, 4⟩ cache_6, place ⟨468, 0, 4, 2⟩ cache_468] = cache_470 := by
  decide +kernel

theorem load_entry_470 : entryAt 470 = entry_470 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_470 : CacheEquation 470 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(470 < 6)), load_entry_470]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (denote cache_6), placeRow ⟨468, 0, 4, 2⟩ (denote cache_468)] = denote cache_470
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_470

theorem verified_row_471 : fork [place ⟨6, 5, 4, 3⟩ cache_6, place ⟨466, 0, 5, 6⟩ cache_466] = cache_471 := by
  decide +kernel

theorem load_entry_471 : entryAt 471 = entry_471 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_471 : CacheEquation 471 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(471 < 6)), load_entry_471]
  change forkRow [placeRow ⟨6, 5, 4, 3⟩ (denote cache_6), placeRow ⟨466, 0, 5, 6⟩ (denote cache_466)] = denote cache_471
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_471

theorem verified_row_472 : fork [place ⟨6, 5, 5, 0⟩ cache_6, place ⟨466, 0, 6, 3⟩ cache_466] = cache_472 := by
  decide +kernel

theorem load_entry_472 : entryAt 472 = entry_472 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_472 : CacheEquation 472 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(472 < 6)), load_entry_472]
  change forkRow [placeRow ⟨6, 5, 5, 0⟩ (denote cache_6), placeRow ⟨466, 0, 6, 3⟩ (denote cache_466)] = denote cache_472
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_472

theorem verified_row_473 : fork [place ⟨121, 5, 5, 4⟩ cache_121, place ⟨436, 0, 3, 7⟩ cache_436, place ⟨445, 4, 5, 4⟩ cache_445] = cache_473 := by
  decide +kernel

theorem load_entry_473 : entryAt 473 = entry_473 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_473 : CacheEquation 473 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(473 < 6)), load_entry_473]
  change forkRow [placeRow ⟨121, 5, 5, 4⟩ (denote cache_121), placeRow ⟨436, 0, 3, 7⟩ (denote cache_436), placeRow ⟨445, 4, 5, 4⟩ (denote cache_445)] = denote cache_473
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_473

theorem verified_row_474 : fork [place ⟨463, 0, 6, 5⟩ cache_463, place ⟨70, 0, 3, 5⟩ cache_70, place ⟨83, 1, 5, 3⟩ cache_83] = cache_474 := by
  decide +kernel

theorem load_entry_474 : entryAt 474 = entry_474 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_474 : CacheEquation 474 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(474 < 6)), load_entry_474]
  change forkRow [placeRow ⟨463, 0, 6, 5⟩ (denote cache_463), placeRow ⟨70, 0, 3, 5⟩ (denote cache_70), placeRow ⟨83, 1, 5, 3⟩ (denote cache_83)] = denote cache_474
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_474

theorem verified_row_475 : fork [place ⟨63, 1, 5, 3⟩ cache_63, place ⟨261, 1, 4, 3⟩ cache_261, place ⟨457, 0, 2, 5⟩ cache_457, place ⟨269, 2, 2, 5⟩ cache_269] = cache_475 := by
  decide +kernel

theorem load_entry_475 : entryAt 475 = entry_475 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_475 : CacheEquation 475 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(475 < 6)), load_entry_475]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (denote cache_63), placeRow ⟨261, 1, 4, 3⟩ (denote cache_261), placeRow ⟨457, 0, 2, 5⟩ (denote cache_457), placeRow ⟨269, 2, 2, 5⟩ (denote cache_269)] = denote cache_475
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_475

theorem verified_row_476 : fork [place ⟨0, 0, 1, 3⟩ cache_0, place ⟨473, 0, 5, 3⟩ cache_473] = cache_476 := by
  decide +kernel

theorem load_entry_476 : entryAt 476 = entry_476 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_476 : CacheEquation 476 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(476 < 6)), load_entry_476]
  change forkRow [placeRow ⟨0, 0, 1, 3⟩ (denote cache_0), placeRow ⟨473, 0, 5, 3⟩ (denote cache_473)] = denote cache_476
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_476

theorem verified_row_477 : fork [place ⟨55, 1, 4, 5⟩ cache_55, place ⟨154, 7, 4, 5⟩ cache_154, place ⟨154, 3, 4, 0⟩ cache_154, place ⟨471, 2, 5, 4⟩ cache_471] = cache_477 := by
  decide +kernel

theorem load_entry_477 : entryAt 477 = entry_477 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_477 : CacheEquation 477 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(477 < 6)), load_entry_477]
  change forkRow [placeRow ⟨55, 1, 4, 5⟩ (denote cache_55), placeRow ⟨154, 7, 4, 5⟩ (denote cache_154), placeRow ⟨154, 3, 4, 0⟩ (denote cache_154), placeRow ⟨471, 2, 5, 4⟩ (denote cache_471)] = denote cache_477
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_477

theorem verified_row_478 : fork [place ⟨25, 3, 4, 5⟩ cache_25, place ⟨165, 2, 4, 5⟩ cache_165, place ⟨190, 0, 7, 4⟩ cache_190] = cache_478 := by
  decide +kernel

theorem load_entry_478 : entryAt 478 = entry_478 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_478 : CacheEquation 478 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(478 < 6)), load_entry_478]
  change forkRow [placeRow ⟨25, 3, 4, 5⟩ (denote cache_25), placeRow ⟨165, 2, 4, 5⟩ (denote cache_165), placeRow ⟨190, 0, 7, 4⟩ (denote cache_190)] = denote cache_478
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_478

theorem verified_row_479 : fork [place ⟨55, 0, 5, 4⟩ cache_55, place ⟨443, 0, 4, 5⟩ cache_443, place ⟨443, 4, 1, 5⟩ cache_443] = cache_479 := by
  decide +kernel

theorem load_entry_479 : entryAt 479 = entry_479 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_479 : CacheEquation 479 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(479 < 6)), load_entry_479]
  change forkRow [placeRow ⟨55, 0, 5, 4⟩ (denote cache_55), placeRow ⟨443, 0, 4, 5⟩ (denote cache_443), placeRow ⟨443, 4, 1, 5⟩ (denote cache_443)] = denote cache_479
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_479

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_Equations12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

theorem verified_row_480 : fork [place ⟨108, 1, 4, 5⟩ cache_108, place ⟨4, 1, 5, 4⟩ cache_4] = cache_480 := by
  decide +kernel

theorem load_entry_480 : entryAt 480 = entry_480 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_480 : CacheEquation 480 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(480 < 6)), load_entry_480]
  change forkRow [placeRow ⟨108, 1, 4, 5⟩ (denote cache_108), placeRow ⟨4, 1, 5, 4⟩ (denote cache_4)] = denote cache_480
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_480

theorem verified_row_481 : fork [place ⟨303, 1, 5, 4⟩ cache_303, place ⟨429, 2, 1, 4⟩ cache_429, place ⟨309, 1, 1, 4⟩ cache_309, place ⟨206, 2, 1, 4⟩ cache_206, place ⟨169, 2, 1, 4⟩ cache_169, place ⟨207, 2, 1, 4⟩ cache_207] = cache_481 := by
  decide +kernel

theorem load_entry_481 : entryAt 481 = entry_481 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_481 : CacheEquation 481 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(481 < 6)), load_entry_481]
  change forkRow [placeRow ⟨303, 1, 5, 4⟩ (denote cache_303), placeRow ⟨429, 2, 1, 4⟩ (denote cache_429), placeRow ⟨309, 1, 1, 4⟩ (denote cache_309), placeRow ⟨206, 2, 1, 4⟩ (denote cache_206), placeRow ⟨169, 2, 1, 4⟩ (denote cache_169), placeRow ⟨207, 2, 1, 4⟩ (denote cache_207)] = denote cache_481
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_481

theorem verified_row_482 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨218, 2, 4, 3⟩ cache_218] = cache_482 := by
  decide +kernel

theorem load_entry_482 : entryAt 482 = entry_482 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_482 : CacheEquation 482 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(482 < 6)), load_entry_482]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨218, 2, 4, 3⟩ (denote cache_218)] = denote cache_482
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_482

theorem verified_row_483 : fork [place ⟨173, 1, 4, 5⟩ cache_173, place ⟨292, 7, 3, 1⟩ cache_292, place ⟨319, 1, 3, 5⟩ cache_319, place ⟨192, 6, 4, 1⟩ cache_192, place ⟨475, 1, 4, 5⟩ cache_475] = cache_483 := by
  decide +kernel

theorem load_entry_483 : entryAt 483 = entry_483 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_483 : CacheEquation 483 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(483 < 6)), load_entry_483]
  change forkRow [placeRow ⟨173, 1, 4, 5⟩ (denote cache_173), placeRow ⟨292, 7, 3, 1⟩ (denote cache_292), placeRow ⟨319, 1, 3, 5⟩ (denote cache_319), placeRow ⟨192, 6, 4, 1⟩ (denote cache_192), placeRow ⟨475, 1, 4, 5⟩ (denote cache_475)] = denote cache_483
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_483

theorem verified_row_484 : fork [place ⟨25, 4, 1, 5⟩ cache_25, place ⟨107, 2, 5, 4⟩ cache_107, place ⟨349, 3, 1, 5⟩ cache_349, place ⟨163, 2, 5, 4⟩ cache_163] = cache_484 := by
  decide +kernel

theorem load_entry_484 : entryAt 484 = entry_484 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_484 : CacheEquation 484 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(484 < 6)), load_entry_484]
  change forkRow [placeRow ⟨25, 4, 1, 5⟩ (denote cache_25), placeRow ⟨107, 2, 5, 4⟩ (denote cache_107), placeRow ⟨349, 3, 1, 5⟩ (denote cache_349), placeRow ⟨163, 2, 5, 4⟩ (denote cache_163)] = denote cache_484
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_484

theorem verified_row_485 : fork [place ⟨484, 0, 5, 4⟩ cache_484, place ⟨2, 3, 4, 3⟩ cache_2] = cache_485 := by
  decide +kernel

theorem load_entry_485 : entryAt 485 = entry_485 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_485 : CacheEquation 485 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(485 < 6)), load_entry_485]
  change forkRow [placeRow ⟨484, 0, 5, 4⟩ (denote cache_484), placeRow ⟨2, 3, 4, 3⟩ (denote cache_2)] = denote cache_485
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_485

theorem verified_row_486 : fork [place ⟨2, 5, 4, 2⟩ cache_2, place ⟨485, 0, 5, 3⟩ cache_485] = cache_486 := by
  decide +kernel

theorem load_entry_486 : entryAt 486 = entry_486 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_486 : CacheEquation 486 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(486 < 6)), load_entry_486]
  change forkRow [placeRow ⟨2, 5, 4, 2⟩ (denote cache_2), placeRow ⟨485, 0, 5, 3⟩ (denote cache_485)] = denote cache_486
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_486

theorem verified_row_487 : fork [place ⟨2, 3, 4, 3⟩ cache_2, place ⟨481, 0, 5, 4⟩ cache_481] = cache_487 := by
  decide +kernel

theorem load_entry_487 : entryAt 487 = entry_487 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_487 : CacheEquation 487 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(487 < 6)), load_entry_487]
  change forkRow [placeRow ⟨2, 3, 4, 3⟩ (denote cache_2), placeRow ⟨481, 0, 5, 4⟩ (denote cache_481)] = denote cache_487
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_487

theorem verified_row_488 : fork [place ⟨0, 6, 6, 4⟩ cache_0, place ⟨247, 0, 2, 5⟩ cache_247] = cache_488 := by
  decide +kernel

theorem load_entry_488 : entryAt 488 = entry_488 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_488 : CacheEquation 488 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(488 < 6)), load_entry_488]
  change forkRow [placeRow ⟨0, 6, 6, 4⟩ (denote cache_0), placeRow ⟨247, 0, 2, 5⟩ (denote cache_247)] = denote cache_488
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_488

theorem verified_row_489 : fork [place ⟨356, 1, 3, 3⟩ cache_356, place ⟨197, 4, 1, 4⟩ cache_197, place ⟨172, 6, 1, 4⟩ cache_172] = cache_489 := by
  decide +kernel

theorem load_entry_489 : entryAt 489 = entry_489 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_489 : CacheEquation 489 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(489 < 6)), load_entry_489]
  change forkRow [placeRow ⟨356, 1, 3, 3⟩ (denote cache_356), placeRow ⟨197, 4, 1, 4⟩ (denote cache_197), placeRow ⟨172, 6, 1, 4⟩ (denote cache_172)] = denote cache_489
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_489

theorem verified_row_490 : fork [place ⟨64, 1, 3, 1⟩ cache_64, place ⟨471, 0, 5, 1⟩ cache_471, place ⟨470, 1, 5, 1⟩ cache_470, place ⟨111, 0, 3, 1⟩ cache_111] = cache_490 := by
  decide +kernel

theorem load_entry_490 : entryAt 490 = entry_490 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_490 : CacheEquation 490 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(490 < 6)), load_entry_490]
  change forkRow [placeRow ⟨64, 1, 3, 1⟩ (denote cache_64), placeRow ⟨471, 0, 5, 1⟩ (denote cache_471), placeRow ⟨470, 1, 5, 1⟩ (denote cache_470), placeRow ⟨111, 0, 3, 1⟩ (denote cache_111)] = denote cache_490
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_490

theorem verified_row_491 : fork [place ⟨6, 3, 3, 5⟩ cache_6, place ⟨273, 0, 5, 4⟩ cache_273] = cache_491 := by
  decide +kernel

theorem load_entry_491 : entryAt 491 = entry_491 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_491 : CacheEquation 491 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(491 < 6)), load_entry_491]
  change forkRow [placeRow ⟨6, 3, 3, 5⟩ (denote cache_6), placeRow ⟨273, 0, 5, 4⟩ (denote cache_273)] = denote cache_491
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_491

theorem verified_row_492 : fork [place ⟨62, 4, 3, 4⟩ cache_62, place ⟨107, 4, 3, 4⟩ cache_107, place ⟨487, 0, 6, 6⟩ cache_487] = cache_492 := by
  decide +kernel

theorem load_entry_492 : entryAt 492 = entry_492 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_492 : CacheEquation 492 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(492 < 6)), load_entry_492]
  change forkRow [placeRow ⟨62, 4, 3, 4⟩ (denote cache_62), placeRow ⟨107, 4, 3, 4⟩ (denote cache_107), placeRow ⟨487, 0, 6, 6⟩ (denote cache_487)] = denote cache_492
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_492

theorem verified_row_493 : fork [place ⟨225, 0, 1, 4⟩ cache_225, place ⟨455, 0, 5, 3⟩ cache_455, place ⟨236, 1, 5, 5⟩ cache_236, place ⟨221, 0, 5, 4⟩ cache_221] = cache_493 := by
  decide +kernel

theorem load_entry_493 : entryAt 493 = entry_493 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_493 : CacheEquation 493 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(493 < 6)), load_entry_493]
  change forkRow [placeRow ⟨225, 0, 1, 4⟩ (denote cache_225), placeRow ⟨455, 0, 5, 3⟩ (denote cache_455), placeRow ⟨236, 1, 5, 5⟩ (denote cache_236), placeRow ⟨221, 0, 5, 4⟩ (denote cache_221)] = denote cache_493
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_493

theorem verified_row_494 : fork [place ⟨297, 4, 4, 5⟩ cache_297, place ⟨268, 4, 1, 5⟩ cache_268, place ⟨162, 5, 5, 4⟩ cache_162] = cache_494 := by
  decide +kernel

theorem load_entry_494 : entryAt 494 = entry_494 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_494 : CacheEquation 494 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(494 < 6)), load_entry_494]
  change forkRow [placeRow ⟨297, 4, 4, 5⟩ (denote cache_297), placeRow ⟨268, 4, 1, 5⟩ (denote cache_268), placeRow ⟨162, 5, 5, 4⟩ (denote cache_162)] = denote cache_494
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_494

theorem verified_row_495 : fork [place ⟨25, 6, 1, 3⟩ cache_25, place ⟨167, 4, 1, 4⟩ cache_167, place ⟨456, 4, 1, 4⟩ cache_456] = cache_495 := by
  decide +kernel

theorem load_entry_495 : entryAt 495 = entry_495 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_495 : CacheEquation 495 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(495 < 6)), load_entry_495]
  change forkRow [placeRow ⟨25, 6, 1, 3⟩ (denote cache_25), placeRow ⟨167, 4, 1, 4⟩ (denote cache_167), placeRow ⟨456, 4, 1, 4⟩ (denote cache_456)] = denote cache_495
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_495

theorem verified_row_496 : fork [place ⟨25, 0, 7, 5⟩ cache_25, place ⟨107, 6, 3, 4⟩ cache_107, place ⟨163, 6, 3, 4⟩ cache_163, place ⟨494, 0, 7, 4⟩ cache_494] = cache_496 := by
  decide +kernel

theorem load_entry_496 : entryAt 496 = entry_496 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_496 : CacheEquation 496 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(496 < 6)), load_entry_496]
  change forkRow [placeRow ⟨25, 0, 7, 5⟩ (denote cache_25), placeRow ⟨107, 6, 3, 4⟩ (denote cache_107), placeRow ⟨163, 6, 3, 4⟩ (denote cache_163), placeRow ⟨494, 0, 7, 4⟩ (denote cache_494)] = denote cache_496
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_496

theorem verified_row_497 : fork [place ⟨36, 2, 3, 4⟩ cache_36, place ⟨167, 0, 7, 4⟩ cache_167, place ⟨410, 0, 7, 3⟩ cache_410] = cache_497 := by
  decide +kernel

theorem load_entry_497 : entryAt 497 = entry_497 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_497 : CacheEquation 497 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(497 < 6)), load_entry_497]
  change forkRow [placeRow ⟨36, 2, 3, 4⟩ (denote cache_36), placeRow ⟨167, 0, 7, 4⟩ (denote cache_167), placeRow ⟨410, 0, 7, 3⟩ (denote cache_410)] = denote cache_497
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_497

theorem verified_row_498 : fork [place ⟨14, 1, 4, 6⟩ cache_14, place ⟨298, 2, 2, 4⟩ cache_298] = cache_498 := by
  decide +kernel

theorem load_entry_498 : entryAt 498 = entry_498 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_498 : CacheEquation 498 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(498 < 6)), load_entry_498]
  change forkRow [placeRow ⟨14, 1, 4, 6⟩ (denote cache_14), placeRow ⟨298, 2, 2, 4⟩ (denote cache_298)] = denote cache_498
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_498

theorem verified_row_499 : fork [place ⟨493, 0, 5, 4⟩ cache_493, place ⟨25, 1, 4, 5⟩ cache_25, place ⟨478, 0, 2, 4⟩ cache_478] = cache_499 := by
  decide +kernel

theorem load_entry_499 : entryAt 499 = entry_499 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_499 : CacheEquation 499 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(499 < 6)), load_entry_499]
  change forkRow [placeRow ⟨493, 0, 5, 4⟩ (denote cache_493), placeRow ⟨25, 1, 4, 5⟩ (denote cache_25), placeRow ⟨478, 0, 2, 4⟩ (denote cache_478)] = denote cache_499
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_499

theorem verified_row_500 : fork [place ⟨1, 5, 3, 6⟩ cache_1, place ⟨351, 0, 5, 4⟩ cache_351] = cache_500 := by
  decide +kernel

theorem load_entry_500 : entryAt 500 = entry_500 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_500 : CacheEquation 500 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(500 < 6)), load_entry_500]
  change forkRow [placeRow ⟨1, 5, 3, 6⟩ (denote cache_1), placeRow ⟨351, 0, 5, 4⟩ (denote cache_351)] = denote cache_500
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_500

theorem verified_row_501 : fork [place ⟨6, 4, 0, 5⟩ cache_6, place ⟨316, 0, 1, 3⟩ cache_316] = cache_501 := by
  decide +kernel

theorem load_entry_501 : entryAt 501 = entry_501 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_501 : CacheEquation 501 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(501 < 6)), load_entry_501]
  change forkRow [placeRow ⟨6, 4, 0, 5⟩ (denote cache_6), placeRow ⟨316, 0, 1, 3⟩ (denote cache_316)] = denote cache_501
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_501

theorem verified_row_502 : fork [place ⟨215, 6, 2, 3⟩ cache_215, place ⟨232, 0, 4, 3⟩ cache_232, place ⟨192, 7, 1, 4⟩ cache_192, place ⟨173, 0, 5, 4⟩ cache_173, place ⟨271, 2, 2, 3⟩ cache_271] = cache_502 := by
  decide +kernel

theorem load_entry_502 : entryAt 502 = entry_502 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_502 : CacheEquation 502 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(502 < 6)), load_entry_502]
  change forkRow [placeRow ⟨215, 6, 2, 3⟩ (denote cache_215), placeRow ⟨232, 0, 4, 3⟩ (denote cache_232), placeRow ⟨192, 7, 1, 4⟩ (denote cache_192), placeRow ⟨173, 0, 5, 4⟩ (denote cache_173), placeRow ⟨271, 2, 2, 3⟩ (denote cache_271)] = denote cache_502
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_502

theorem verified_row_503 : fork [place ⟨63, 0, 3, 5⟩ cache_63, place ⟨55, 7, 4, 0⟩ cache_55, place ⟨420, 1, 7, 2⟩ cache_420, place ⟨419, 1, 7, 4⟩ cache_419] = cache_503 := by
  decide +kernel

theorem load_entry_503 : entryAt 503 = entry_503 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_503 : CacheEquation 503 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(503 < 6)), load_entry_503]
  change forkRow [placeRow ⟨63, 0, 3, 5⟩ (denote cache_63), placeRow ⟨55, 7, 4, 0⟩ (denote cache_55), placeRow ⟨420, 1, 7, 2⟩ (denote cache_420), placeRow ⟨419, 1, 7, 4⟩ (denote cache_419)] = denote cache_503
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_503

theorem verified_row_504 : fork [place ⟨381, 0, 3, 4⟩ cache_381, place ⟨310, 4, 4, 5⟩ cache_310, place ⟨159, 0, 5, 6⟩ cache_159, place ⟨351, 4, 3, 4⟩ cache_351, place ⟨496, 0, 3, 4⟩ cache_496] = cache_504 := by
  decide +kernel

theorem load_entry_504 : entryAt 504 = entry_504 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_504 : CacheEquation 504 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(504 < 6)), load_entry_504]
  change forkRow [placeRow ⟨381, 0, 3, 4⟩ (denote cache_381), placeRow ⟨310, 4, 4, 5⟩ (denote cache_310), placeRow ⟨159, 0, 5, 6⟩ (denote cache_159), placeRow ⟨351, 4, 3, 4⟩ (denote cache_351), placeRow ⟨496, 0, 3, 4⟩ (denote cache_496)] = denote cache_504
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_504

theorem verified_row_505 : fork [place ⟨173, 1, 4, 5⟩ cache_173, place ⟨499, 0, 5, 4⟩ cache_499, place ⟨183, 1, 4, 5⟩ cache_183, place ⟨282, 1, 4, 5⟩ cache_282] = cache_505 := by
  decide +kernel

theorem load_entry_505 : entryAt 505 = entry_505 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_505 : CacheEquation 505 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(505 < 6)), load_entry_505]
  change forkRow [placeRow ⟨173, 1, 4, 5⟩ (denote cache_173), placeRow ⟨499, 0, 5, 4⟩ (denote cache_499), placeRow ⟨183, 1, 4, 5⟩ (denote cache_183), placeRow ⟨282, 1, 4, 5⟩ (denote cache_282)] = denote cache_505
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_505

theorem verified_row_506 : fork [place ⟨99, 0, 4, 5⟩ cache_99, place ⟨200, 7, 1, 4⟩ cache_200, place ⟨318, 5, 5, 4⟩ cache_318, place ⟨173, 0, 5, 4⟩ cache_173] = cache_506 := by
  decide +kernel

theorem load_entry_506 : entryAt 506 = entry_506 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_506 : CacheEquation 506 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(506 < 6)), load_entry_506]
  change forkRow [placeRow ⟨99, 0, 4, 5⟩ (denote cache_99), placeRow ⟨200, 7, 1, 4⟩ (denote cache_200), placeRow ⟨318, 5, 5, 4⟩ (denote cache_318), placeRow ⟨173, 0, 5, 4⟩ (denote cache_173)] = denote cache_506
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_506

theorem verified_row_507 : fork [place ⟨151, 0, 2, 4⟩ cache_151, place ⟨33, 3, 4, 3⟩ cache_33, place ⟨481, 0, 5, 4⟩ cache_481] = cache_507 := by
  decide +kernel

theorem load_entry_507 : entryAt 507 = entry_507 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_507 : CacheEquation 507 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(507 < 6)), load_entry_507]
  change forkRow [placeRow ⟨151, 0, 2, 4⟩ (denote cache_151), placeRow ⟨33, 3, 4, 3⟩ (denote cache_33), placeRow ⟨481, 0, 5, 4⟩ (denote cache_481)] = denote cache_507
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_507

theorem verified_row_508 : fork [place ⟨6, 0, 5, 4⟩ cache_6, place ⟨393, 0, 1, 5⟩ cache_393] = cache_508 := by
  decide +kernel

theorem load_entry_508 : entryAt 508 = entry_508 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_508 : CacheEquation 508 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(508 < 6)), load_entry_508]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (denote cache_6), placeRow ⟨393, 0, 1, 5⟩ (denote cache_393)] = denote cache_508
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_508

theorem verified_row_509 : fork [place ⟨252, 0, 6, 4⟩ cache_252, place ⟨241, 4, 2, 4⟩ cache_241, place ⟨455, 0, 6, 3⟩ cache_455, place ⟨68, 2, 6, 4⟩ cache_68] = cache_509 := by
  decide +kernel

theorem load_entry_509 : entryAt 509 = entry_509 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_509 : CacheEquation 509 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(509 < 6)), load_entry_509]
  change forkRow [placeRow ⟨252, 0, 6, 4⟩ (denote cache_252), placeRow ⟨241, 4, 2, 4⟩ (denote cache_241), placeRow ⟨455, 0, 6, 3⟩ (denote cache_455), placeRow ⟨68, 2, 6, 4⟩ (denote cache_68)] = denote cache_509
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_509

theorem verified_row_510 : fork [place ⟨6, 4, 3, 4⟩ cache_6, place ⟨508, 0, 7, 4⟩ cache_508] = cache_510 := by
  decide +kernel

theorem load_entry_510 : entryAt 510 = entry_510 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_510 : CacheEquation 510 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(510 < 6)), load_entry_510]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (denote cache_6), placeRow ⟨508, 0, 7, 4⟩ (denote cache_508)] = denote cache_510
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_510

theorem verified_row_511 : fork [place ⟨15, 1, 4, 5⟩ cache_15, place ⟨331, 0, 5, 3⟩ cache_331, place ⟨380, 4, 2, 4⟩ cache_380] = cache_511 := by
  decide +kernel

theorem load_entry_511 : entryAt 511 = entry_511 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_511 : CacheEquation 511 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(511 < 6)), load_entry_511]
  change forkRow [placeRow ⟨15, 1, 4, 5⟩ (denote cache_15), placeRow ⟨331, 0, 5, 3⟩ (denote cache_331), placeRow ⟨380, 4, 2, 4⟩ (denote cache_380)] = denote cache_511
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_511

theorem verified_row_512 : fork [place ⟨62, 0, 5, 4⟩ cache_62, place ⟨107, 0, 5, 4⟩ cache_107, place ⟨507, 0, 4, 6⟩ cache_507] = cache_512 := by
  decide +kernel

theorem load_entry_512 : entryAt 512 = entry_512 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_512 : CacheEquation 512 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(512 < 6)), load_entry_512]
  change forkRow [placeRow ⟨62, 0, 5, 4⟩ (denote cache_62), placeRow ⟨107, 0, 5, 4⟩ (denote cache_107), placeRow ⟨507, 0, 4, 6⟩ (denote cache_507)] = denote cache_512
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_512

theorem verified_row_513 : fork [place ⟨6, 4, 3, 4⟩ cache_6, place ⟨396, 0, 4, 5⟩ cache_396] = cache_513 := by
  decide +kernel

theorem load_entry_513 : entryAt 513 = entry_513 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_513 : CacheEquation 513 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(513 < 6)), load_entry_513]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (denote cache_6), placeRow ⟨396, 0, 4, 5⟩ (denote cache_396)] = denote cache_513
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_513

theorem verified_row_514 : fork [place ⟨57, 0, 5, 4⟩ cache_57, place ⟨443, 4, 1, 5⟩ cache_443, place ⟨510, 0, 1, 5⟩ cache_510] = cache_514 := by
  decide +kernel

theorem load_entry_514 : entryAt 514 = entry_514 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_514 : CacheEquation 514 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(514 < 6)), load_entry_514]
  change forkRow [placeRow ⟨57, 0, 5, 4⟩ (denote cache_57), placeRow ⟨443, 4, 1, 5⟩ (denote cache_443), placeRow ⟨510, 0, 1, 5⟩ (denote cache_510)] = denote cache_514
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_514

theorem verified_row_515 : fork [place ⟨2, 6, 2, 4⟩ cache_2, place ⟨512, 1, 1, 5⟩ cache_512] = cache_515 := by
  decide +kernel

theorem load_entry_515 : entryAt 515 = entry_515 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_515 : CacheEquation 515 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(515 < 6)), load_entry_515]
  change forkRow [placeRow ⟨2, 6, 2, 4⟩ (denote cache_2), placeRow ⟨512, 1, 1, 5⟩ (denote cache_512)] = denote cache_515
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_515

theorem verified_row_516 : fork [place ⟨329, 0, 4, 3⟩ cache_329, place ⟨244, 4, 2, 4⟩ cache_244, place ⟨10, 1, 4, 5⟩ cache_10, place ⟨506, 4, 2, 4⟩ cache_506] = cache_516 := by
  decide +kernel

theorem load_entry_516 : entryAt 516 = entry_516 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_516 : CacheEquation 516 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(516 < 6)), load_entry_516]
  change forkRow [placeRow ⟨329, 0, 4, 3⟩ (denote cache_329), placeRow ⟨244, 4, 2, 4⟩ (denote cache_244), placeRow ⟨10, 1, 4, 5⟩ (denote cache_10), placeRow ⟨506, 4, 2, 4⟩ (denote cache_506)] = denote cache_516
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_516

theorem verified_row_517 : fork [place ⟨496, 0, 2, 3⟩ cache_496, place ⟨140, 0, 4, 2⟩ cache_140, place ⟨193, 1, 4, 2⟩ cache_193] = cache_517 := by
  decide +kernel

theorem load_entry_517 : entryAt 517 = entry_517 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_517 : CacheEquation 517 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(517 < 6)), load_entry_517]
  change forkRow [placeRow ⟨496, 0, 2, 3⟩ (denote cache_496), placeRow ⟨140, 0, 4, 2⟩ (denote cache_140), placeRow ⟨193, 1, 4, 2⟩ (denote cache_193)] = denote cache_517
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_517

theorem verified_row_518 : fork [place ⟨9, 6, 3, 4⟩ cache_9, place ⟨514, 0, 7, 4⟩ cache_514] = cache_518 := by
  decide +kernel

theorem load_entry_518 : entryAt 518 = entry_518 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_518 : CacheEquation 518 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(518 < 6)), load_entry_518]
  change forkRow [placeRow ⟨9, 6, 3, 4⟩ (denote cache_9), placeRow ⟨514, 0, 7, 4⟩ (denote cache_514)] = denote cache_518
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_518

theorem verified_row_519 : fork [place ⟨498, 0, 4, 3⟩ cache_498, place ⟨311, 4, 3, 4⟩ cache_311, place ⟨38, 1, 4, 5⟩ cache_38, place ⟨408, 0, 3, 4⟩ cache_408] = cache_519 := by
  decide +kernel

theorem load_entry_519 : entryAt 519 = entry_519 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_519 : CacheEquation 519 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(519 < 6)), load_entry_519]
  change forkRow [placeRow ⟨498, 0, 4, 3⟩ (denote cache_498), placeRow ⟨311, 4, 3, 4⟩ (denote cache_311), placeRow ⟨38, 1, 4, 5⟩ (denote cache_38), placeRow ⟨408, 0, 3, 4⟩ (denote cache_408)] = denote cache_519
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_519

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_Equations13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

theorem verified_row_520 : fork [place ⟨254, 0, 2, 3⟩ cache_254, place ⟨200, 5, 6, 4⟩ cache_200, place ⟨271, 6, 5, 3⟩ cache_271, place ⟨215, 2, 5, 3⟩ cache_215, place ⟨252, 4, 2, 4⟩ cache_252] = cache_520 := by
  decide +kernel

theorem load_entry_520 : entryAt 520 = entry_520 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_520 : CacheEquation 520 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(520 < 6)), load_entry_520]
  change forkRow [placeRow ⟨254, 0, 2, 3⟩ (denote cache_254), placeRow ⟨200, 5, 6, 4⟩ (denote cache_200), placeRow ⟨271, 6, 5, 3⟩ (denote cache_271), placeRow ⟨215, 2, 5, 3⟩ (denote cache_215), placeRow ⟨252, 4, 2, 4⟩ (denote cache_252)] = denote cache_520
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_520

theorem verified_row_521 : fork [place ⟨492, 4, 5, 1⟩ cache_492, place ⟨2, 7, 4, 2⟩ cache_2] = cache_521 := by
  decide +kernel

theorem load_entry_521 : entryAt 521 = entry_521 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_521 : CacheEquation 521 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(521 < 6)), load_entry_521]
  change forkRow [placeRow ⟨492, 4, 5, 1⟩ (denote cache_492), placeRow ⟨2, 7, 4, 2⟩ (denote cache_2)] = denote cache_521
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_521

theorem verified_row_522 : fork [place ⟨176, 3, 4, 6⟩ cache_176, place ⟨338, 2, 3, 3⟩ cache_338, place ⟨252, 1, 4, 6⟩ cache_252] = cache_522 := by
  decide +kernel

theorem load_entry_522 : entryAt 522 = entry_522 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_522 : CacheEquation 522 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(522 < 6)), load_entry_522]
  change forkRow [placeRow ⟨176, 3, 4, 6⟩ (denote cache_176), placeRow ⟨338, 2, 3, 3⟩ (denote cache_338), placeRow ⟨252, 1, 4, 6⟩ (denote cache_252)] = denote cache_522
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_522

theorem verified_row_523 : fork [place ⟨303, 1, 5, 4⟩ cache_303, place ⟨25, 4, 1, 5⟩ cache_25, place ⟨107, 2, 5, 4⟩ cache_107, place ⟨511, 4, 1, 6⟩ cache_511] = cache_523 := by
  decide +kernel

theorem load_entry_523 : entryAt 523 = entry_523 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_523 : CacheEquation 523 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(523 < 6)), load_entry_523]
  change forkRow [placeRow ⟨303, 1, 5, 4⟩ (denote cache_303), placeRow ⟨25, 4, 1, 5⟩ (denote cache_25), placeRow ⟨107, 2, 5, 4⟩ (denote cache_107), placeRow ⟨511, 4, 1, 6⟩ (denote cache_511)] = denote cache_523
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_523

theorem verified_row_524 : fork [place ⟨504, 4, 5, 3⟩ cache_504, place ⟨504, 0, 3, 3⟩ cache_504, place ⟨180, 0, 4, 5⟩ cache_180, place ⟨180, 4, 4, 5⟩ cache_180, place ⟨261, 0, 3, 4⟩ cache_261] = cache_524 := by
  decide +kernel

theorem load_entry_524 : entryAt 524 = entry_524 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_524 : CacheEquation 524 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(524 < 6)), load_entry_524]
  change forkRow [placeRow ⟨504, 4, 5, 3⟩ (denote cache_504), placeRow ⟨504, 0, 3, 3⟩ (denote cache_504), placeRow ⟨180, 0, 4, 5⟩ (denote cache_180), placeRow ⟨180, 4, 4, 5⟩ (denote cache_180), placeRow ⟨261, 0, 3, 4⟩ (denote cache_261)] = denote cache_524
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_524

theorem verified_row_525 : fork [place ⟨303, 1, 5, 4⟩ cache_303, place ⟨25, 4, 1, 5⟩ cache_25, place ⟨430, 0, 4, 6⟩ cache_430, place ⟨107, 2, 5, 4⟩ cache_107] = cache_525 := by
  decide +kernel

theorem load_entry_525 : entryAt 525 = entry_525 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_525 : CacheEquation 525 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(525 < 6)), load_entry_525]
  change forkRow [placeRow ⟨303, 1, 5, 4⟩ (denote cache_303), placeRow ⟨25, 4, 1, 5⟩ (denote cache_25), placeRow ⟨430, 0, 4, 6⟩ (denote cache_430), placeRow ⟨107, 2, 5, 4⟩ (denote cache_107)] = denote cache_525
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_525

theorem verified_row_526 : fork [place ⟨359, 0, 4, 3⟩ cache_359, place ⟨416, 4, 2, 4⟩ cache_416, place ⟨327, 5, 4, 3⟩ cache_327, place ⟨489, 0, 5, 4⟩ cache_489, place ⟨399, 3, 2, 4⟩ cache_399] = cache_526 := by
  decide +kernel

theorem load_entry_526 : entryAt 526 = entry_526 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_526 : CacheEquation 526 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(526 < 6)), load_entry_526]
  change forkRow [placeRow ⟨359, 0, 4, 3⟩ (denote cache_359), placeRow ⟨416, 4, 2, 4⟩ (denote cache_416), placeRow ⟨327, 5, 4, 3⟩ (denote cache_327), placeRow ⟨489, 0, 5, 4⟩ (denote cache_489), placeRow ⟨399, 3, 2, 4⟩ (denote cache_399)] = denote cache_526
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_526

theorem verified_row_527 : fork [place ⟨387, 4, 4, 3⟩ cache_387, place ⟨38, 3, 4, 5⟩ cache_38, place ⟨491, 0, 5, 4⟩ cache_491, place ⟨519, 0, 6, 4⟩ cache_519] = cache_527 := by
  decide +kernel

theorem load_entry_527 : entryAt 527 = entry_527 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_527 : CacheEquation 527 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(527 < 6)), load_entry_527]
  change forkRow [placeRow ⟨387, 4, 4, 3⟩ (denote cache_387), placeRow ⟨38, 3, 4, 5⟩ (denote cache_38), placeRow ⟨491, 0, 5, 4⟩ (denote cache_491), placeRow ⟨519, 0, 6, 4⟩ (denote cache_519)] = denote cache_527
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_527

theorem verified_row_528 : fork [place ⟨414, 1, 3, 5⟩ cache_414, place ⟨386, 1, 4, 6⟩ cache_386, place ⟨502, 5, 4, 3⟩ cache_502, place ⟨226, 4, 1, 5⟩ cache_226, place ⟨359, 5, 3, 4⟩ cache_359] = cache_528 := by
  decide +kernel

theorem load_entry_528 : entryAt 528 = entry_528 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_528 : CacheEquation 528 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(528 < 6)), load_entry_528]
  change forkRow [placeRow ⟨414, 1, 3, 5⟩ (denote cache_414), placeRow ⟨386, 1, 4, 6⟩ (denote cache_386), placeRow ⟨502, 5, 4, 3⟩ (denote cache_502), placeRow ⟨226, 4, 1, 5⟩ (denote cache_226), placeRow ⟨359, 5, 3, 4⟩ (denote cache_359)] = denote cache_528
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_528

theorem verified_row_529 : fork [place ⟨55, 4, 3, 4⟩ cache_55, place ⟨441, 0, 4, 3⟩ cache_441, place ⟨63, 3, 3, 3⟩ cache_63, place ⟨64, 6, 7, 5⟩ cache_64] = cache_529 := by
  decide +kernel

theorem load_entry_529 : entryAt 529 = entry_529 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_529 : CacheEquation 529 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(529 < 6)), load_entry_529]
  change forkRow [placeRow ⟨55, 4, 3, 4⟩ (denote cache_55), placeRow ⟨441, 0, 4, 3⟩ (denote cache_441), placeRow ⟨63, 3, 3, 3⟩ (denote cache_63), placeRow ⟨64, 6, 7, 5⟩ (denote cache_64)] = denote cache_529
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_529

theorem verified_row_530 : fork [place ⟨456, 7, 4, 2⟩ cache_456, place ⟨336, 0, 5, 5⟩ cache_336, place ⟨283, 7, 4, 2⟩ cache_283, place ⟨271, 5, 5, 5⟩ cache_271] = cache_530 := by
  decide +kernel

theorem load_entry_530 : entryAt 530 = entry_530 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_530 : CacheEquation 530 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(530 < 6)), load_entry_530]
  change forkRow [placeRow ⟨456, 7, 4, 2⟩ (denote cache_456), placeRow ⟨336, 0, 5, 5⟩ (denote cache_336), placeRow ⟨283, 7, 4, 2⟩ (denote cache_283), placeRow ⟨271, 5, 5, 5⟩ (denote cache_271)] = denote cache_530
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_530

theorem verified_row_531 : fork [place ⟨425, 0, 5, 4⟩ cache_425, place ⟨336, 3, 4, 3⟩ cache_336, place ⟨340, 6, 4, 3⟩ cache_340, place ⟨394, 1, 5, 4⟩ cache_394, place ⟨423, 0, 5, 4⟩ cache_423, place ⟨526, 0, 5, 4⟩ cache_526, place ⟨401, 4, 4, 3⟩ cache_401, place ⟨453, 0, 5, 4⟩ cache_453] = cache_531 := by
  decide +kernel

theorem load_entry_531 : entryAt 531 = entry_531 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_531 : CacheEquation 531 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(531 < 6)), load_entry_531]
  change forkRow [placeRow ⟨425, 0, 5, 4⟩ (denote cache_425), placeRow ⟨336, 3, 4, 3⟩ (denote cache_336), placeRow ⟨340, 6, 4, 3⟩ (denote cache_340), placeRow ⟨394, 1, 5, 4⟩ (denote cache_394), placeRow ⟨423, 0, 5, 4⟩ (denote cache_423), placeRow ⟨526, 0, 5, 4⟩ (denote cache_526), placeRow ⟨401, 4, 4, 3⟩ (denote cache_401), placeRow ⟨453, 0, 5, 4⟩ (denote cache_453)] = denote cache_531
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_531

theorem verified_row_532 : fork [place ⟨504, 4, 5, 3⟩ cache_504, place ⟨6, 7, 3, 0⟩ cache_6] = cache_532 := by
  decide +kernel

theorem load_entry_532 : entryAt 532 = entry_532 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_532 : CacheEquation 532 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(532 < 6)), load_entry_532]
  change forkRow [placeRow ⟨504, 4, 5, 3⟩ (denote cache_504), placeRow ⟨6, 7, 3, 0⟩ (denote cache_6)] = denote cache_532
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_532

theorem verified_row_533 : fork [place ⟨318, 4, 4, 5⟩ cache_318, place ⟨319, 7, 5, 1⟩ cache_319, place ⟨407, 4, 4, 1⟩ cache_407, place ⟨173, 3, 4, 5⟩ cache_173, place ⟨217, 1, 4, 5⟩ cache_217] = cache_533 := by
  decide +kernel

theorem load_entry_533 : entryAt 533 = entry_533 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_533 : CacheEquation 533 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(533 < 6)), load_entry_533]
  change forkRow [placeRow ⟨318, 4, 4, 5⟩ (denote cache_318), placeRow ⟨319, 7, 5, 1⟩ (denote cache_319), placeRow ⟨407, 4, 4, 1⟩ (denote cache_407), placeRow ⟨173, 3, 4, 5⟩ (denote cache_173), placeRow ⟨217, 1, 4, 5⟩ (denote cache_217)] = denote cache_533
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_533

theorem verified_row_534 : fork [place ⟨434, 0, 4, 6⟩ cache_434, place ⟨12, 6, 1, 3⟩ cache_12] = cache_534 := by
  decide +kernel

theorem load_entry_534 : entryAt 534 = entry_534 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_534 : CacheEquation 534 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(534 < 6)), load_entry_534]
  change forkRow [placeRow ⟨434, 0, 4, 6⟩ (denote cache_434), placeRow ⟨12, 6, 1, 3⟩ (denote cache_12)] = denote cache_534
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_534

theorem verified_row_535 : fork [place ⟨444, 0, 4, 5⟩ cache_444, place ⟨426, 0, 4, 5⟩ cache_426, place ⟨25, 0, 5, 4⟩ cache_25, place ⟨321, 4, 4, 2⟩ cache_321] = cache_535 := by
  decide +kernel

theorem load_entry_535 : entryAt 535 = entry_535 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_535 : CacheEquation 535 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(535 < 6)), load_entry_535]
  change forkRow [placeRow ⟨444, 0, 4, 5⟩ (denote cache_444), placeRow ⟨426, 0, 4, 5⟩ (denote cache_426), placeRow ⟨25, 0, 5, 4⟩ (denote cache_25), placeRow ⟨321, 4, 4, 2⟩ (denote cache_321)] = denote cache_535
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_535

theorem verified_row_536 : fork [place ⟨307, 0, 4, 3⟩ cache_307, place ⟨244, 0, 5, 4⟩ cache_244, place ⟨26, 3, 4, 3⟩ cache_26, place ⟨534, 0, 5, 2⟩ cache_534] = cache_536 := by
  decide +kernel

theorem load_entry_536 : entryAt 536 = entry_536 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_536 : CacheEquation 536 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(536 < 6)), load_entry_536]
  change forkRow [placeRow ⟨307, 0, 4, 3⟩ (denote cache_307), placeRow ⟨244, 0, 5, 4⟩ (denote cache_244), placeRow ⟨26, 3, 4, 3⟩ (denote cache_26), placeRow ⟨534, 0, 5, 2⟩ (denote cache_534)] = denote cache_536
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_536

theorem verified_row_537 : fork [place ⟨373, 2, 2, 4⟩ cache_373, place ⟨271, 3, 3, 3⟩ cache_271, place ⟨176, 1, 4, 6⟩ cache_176, place ⟨330, 1, 4, 6⟩ cache_330] = cache_537 := by
  decide +kernel

theorem load_entry_537 : entryAt 537 = entry_537 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_537 : CacheEquation 537 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(537 < 6)), load_entry_537]
  change forkRow [placeRow ⟨373, 2, 2, 4⟩ (denote cache_373), placeRow ⟨271, 3, 3, 3⟩ (denote cache_271), placeRow ⟨176, 1, 4, 6⟩ (denote cache_176), placeRow ⟨330, 1, 4, 6⟩ (denote cache_330)] = denote cache_537
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_537

theorem verified_row_538 : fork [place ⟨63, 3, 3, 3⟩ cache_63, place ⟨470, 0, 4, 5⟩ cache_470, place ⟨64, 6, 7, 5⟩ cache_64, place ⟨55, 4, 3, 4⟩ cache_55] = cache_538 := by
  decide +kernel

theorem load_entry_538 : entryAt 538 = entry_538 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_538 : CacheEquation 538 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(538 < 6)), load_entry_538]
  change forkRow [placeRow ⟨63, 3, 3, 3⟩ (denote cache_63), placeRow ⟨470, 0, 4, 5⟩ (denote cache_470), placeRow ⟨64, 6, 7, 5⟩ (denote cache_64), placeRow ⟨55, 4, 3, 4⟩ (denote cache_55)] = denote cache_538
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_538

theorem verified_row_539 : fork [place ⟨51, 1, 5, 4⟩ cache_51, place ⟨488, 3, 4, 3⟩ cache_488, place ⟨428, 0, 5, 4⟩ cache_428, place ⟨516, 0, 5, 4⟩ cache_516] = cache_539 := by
  decide +kernel

theorem load_entry_539 : entryAt 539 = entry_539 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_539 : CacheEquation 539 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(539 < 6)), load_entry_539]
  change forkRow [placeRow ⟨51, 1, 5, 4⟩ (denote cache_51), placeRow ⟨488, 3, 4, 3⟩ (denote cache_488), placeRow ⟨428, 0, 5, 4⟩ (denote cache_428), placeRow ⟨516, 0, 5, 4⟩ (denote cache_516)] = denote cache_539
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_539

theorem verified_row_540 : fork [place ⟨334, 0, 4, 3⟩ cache_334, place ⟨51, 1, 5, 4⟩ cache_51, place ⟨88, 3, 4, 3⟩ cache_88, place ⟨536, 0, 5, 4⟩ cache_536] = cache_540 := by
  decide +kernel

theorem load_entry_540 : entryAt 540 = entry_540 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_540 : CacheEquation 540 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(540 < 6)), load_entry_540]
  change forkRow [placeRow ⟨334, 0, 4, 3⟩ (denote cache_334), placeRow ⟨51, 1, 5, 4⟩ (denote cache_51), placeRow ⟨88, 3, 4, 3⟩ (denote cache_88), placeRow ⟨536, 0, 5, 4⟩ (denote cache_536)] = denote cache_540
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_540

theorem verified_row_541 : fork [place ⟨236, 0, 5, 5⟩ cache_236, place ⟨142, 7, 4, 1⟩ cache_142, place ⟨160, 3, 4, 1⟩ cache_160, place ⟨194, 0, 5, 3⟩ cache_194, place ⟨501, 4, 1, 2⟩ cache_501, place ⟨412, 0, 5, 3⟩ cache_412] = cache_541 := by
  decide +kernel

theorem load_entry_541 : entryAt 541 = entry_541 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_541 : CacheEquation 541 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(541 < 6)), load_entry_541]
  change forkRow [placeRow ⟨236, 0, 5, 5⟩ (denote cache_236), placeRow ⟨142, 7, 4, 1⟩ (denote cache_142), placeRow ⟨160, 3, 4, 1⟩ (denote cache_160), placeRow ⟨194, 0, 5, 3⟩ (denote cache_194), placeRow ⟨501, 4, 1, 2⟩ (denote cache_501), placeRow ⟨412, 0, 5, 3⟩ (denote cache_412)] = denote cache_541
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_541

theorem verified_row_542 : fork [place ⟨6, 5, 5, 0⟩ cache_6, place ⟨442, 0, 4, 5⟩ cache_442] = cache_542 := by
  decide +kernel

theorem load_entry_542 : entryAt 542 = entry_542 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_542 : CacheEquation 542 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(542 < 6)), load_entry_542]
  change forkRow [placeRow ⟨6, 5, 5, 0⟩ (denote cache_6), placeRow ⟨442, 0, 4, 5⟩ (denote cache_442)] = denote cache_542
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_542

theorem verified_row_543 : fork [place ⟨493, 3, 2, 6⟩ cache_493, place ⟨107, 2, 5, 4⟩ cache_107, place ⟨318, 5, 5, 4⟩ cache_318] = cache_543 := by
  decide +kernel

theorem load_entry_543 : entryAt 543 = entry_543 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_543 : CacheEquation 543 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(543 < 6)), load_entry_543]
  change forkRow [placeRow ⟨493, 3, 2, 6⟩ (denote cache_493), placeRow ⟨107, 2, 5, 4⟩ (denote cache_107), placeRow ⟨318, 5, 5, 4⟩ (denote cache_318)] = denote cache_543
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_543

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

theorem cache_equations_range_464 : ∀ i, 464 ≤ i → i < 480 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_464
  · exact cache_equation_465
  · exact cache_equation_466
  · exact cache_equation_467
  · exact cache_equation_468
  · exact cache_equation_469
  · exact cache_equation_470
  · exact cache_equation_471
  · exact cache_equation_472
  · exact cache_equation_473
  · exact cache_equation_474
  · exact cache_equation_475
  · exact cache_equation_476
  · exact cache_equation_477
  · exact cache_equation_478
  · exact cache_equation_479

theorem cache_equations_range_480 : ∀ i, 480 ≤ i → i < 496 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_480
  · exact cache_equation_481
  · exact cache_equation_482
  · exact cache_equation_483
  · exact cache_equation_484
  · exact cache_equation_485
  · exact cache_equation_486
  · exact cache_equation_487
  · exact cache_equation_488
  · exact cache_equation_489
  · exact cache_equation_490
  · exact cache_equation_491
  · exact cache_equation_492
  · exact cache_equation_493
  · exact cache_equation_494
  · exact cache_equation_495

theorem cache_equations_range_496 : ∀ i, 496 ≤ i → i < 512 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_496
  · exact cache_equation_497
  · exact cache_equation_498
  · exact cache_equation_499
  · exact cache_equation_500
  · exact cache_equation_501
  · exact cache_equation_502
  · exact cache_equation_503
  · exact cache_equation_504
  · exact cache_equation_505
  · exact cache_equation_506
  · exact cache_equation_507
  · exact cache_equation_508
  · exact cache_equation_509
  · exact cache_equation_510
  · exact cache_equation_511

theorem cache_equations_range_512 : ∀ i, 512 ≤ i → i < 528 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_512
  · exact cache_equation_513
  · exact cache_equation_514
  · exact cache_equation_515
  · exact cache_equation_516
  · exact cache_equation_517
  · exact cache_equation_518
  · exact cache_equation_519
  · exact cache_equation_520
  · exact cache_equation_521
  · exact cache_equation_522
  · exact cache_equation_523
  · exact cache_equation_524
  · exact cache_equation_525
  · exact cache_equation_526
  · exact cache_equation_527

theorem cache_equations_range_528 : ∀ i, 528 ≤ i → i < 544 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_528
  · exact cache_equation_529
  · exact cache_equation_530
  · exact cache_equation_531
  · exact cache_equation_532
  · exact cache_equation_533
  · exact cache_equation_534
  · exact cache_equation_535
  · exact cache_equation_536
  · exact cache_equation_537
  · exact cache_equation_538
  · exact cache_equation_539
  · exact cache_equation_540
  · exact cache_equation_541
  · exact cache_equation_542
  · exact cache_equation_543

theorem cache_equations_range_464_496 : ∀ i, 464 ≤ i → i < 496 → CacheEquation i :=
  merge_ranges cache_equations_range_464 cache_equations_range_480

theorem cache_equations_range_512_544 : ∀ i, 512 ≤ i → i < 544 → CacheEquation i :=
  merge_ranges cache_equations_range_512 cache_equations_range_528

theorem cache_equations_range_496_544 : ∀ i, 496 ≤ i → i < 544 → CacheEquation i :=
  merge_ranges cache_equations_range_496 cache_equations_range_512_544

theorem cache_equations_range_464_544_oai : ∀ i, 464 ≤ i → i < 544 → CacheEquation i :=
  merge_ranges cache_equations_range_464_496 cache_equations_range_496_544

end SnakyCertificate.Check

end OAI
end

theorem solution : type_of% @OAI.SnakyCertificate.Check.cache_equations_range_464_544_oai := @OAI.SnakyCertificate.Check.cache_equations_range_464_544_oai
