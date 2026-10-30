-- Prove2me | solution 1 for OAI.SnakyCertificate.Check.cache_equations_range_544_576
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T23:57:30.820598+00:00
-- url     : https://prove2.me/submissions/9cec79a7-25a1-4dd4-8e52-4eb36187012d

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
-- module Solutions.OAIQ114_SC.SnakyCertificate_Equations13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

theorem verified_row_544 : fork [place ⟨263, 2, 7, 4⟩ cache_263, place ⟨9, 6, 3, 4⟩ cache_9, place ⟨451, 1, 8, 3⟩ cache_451] = cache_544 := by
  decide +kernel

theorem load_entry_544 : entryAt 544 = entry_544 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_544 : CacheEquation 544 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(544 < 6)), load_entry_544]
  change forkRow [placeRow ⟨263, 2, 7, 4⟩ (denote cache_263), placeRow ⟨9, 6, 3, 4⟩ (denote cache_9), placeRow ⟨451, 1, 8, 3⟩ (denote cache_451)] = denote cache_544
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_544

theorem verified_row_545 : fork [place ⟨256, 0, 4, 5⟩ cache_256, place ⟨448, 0, 5, 4⟩ cache_448, place ⟨153, 0, 6, 3⟩ cache_153, place ⟨343, 0, 4, 5⟩ cache_343] = cache_545 := by
  decide +kernel

theorem load_entry_545 : entryAt 545 = entry_545 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_545 : CacheEquation 545 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(545 < 6)), load_entry_545]
  change forkRow [placeRow ⟨256, 0, 4, 5⟩ (denote cache_256), placeRow ⟨448, 0, 5, 4⟩ (denote cache_448), placeRow ⟨153, 0, 6, 3⟩ (denote cache_153), placeRow ⟨343, 0, 4, 5⟩ (denote cache_343)] = denote cache_545
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_545

theorem verified_row_546 : fork [place ⟨64, 0, 4, 3⟩ cache_64, place ⟨482, 7, 4, 3⟩ cache_482, place ⟨443, 0, 7, 5⟩ cache_443, place ⟨64, 6, 7, 5⟩ cache_64] = cache_546 := by
  decide +kernel

theorem load_entry_546 : entryAt 546 = entry_546 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_546 : CacheEquation 546 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(546 < 6)), load_entry_546]
  change forkRow [placeRow ⟨64, 0, 4, 3⟩ (denote cache_64), placeRow ⟨482, 7, 4, 3⟩ (denote cache_482), placeRow ⟨443, 0, 7, 5⟩ (denote cache_443), placeRow ⟨64, 6, 7, 5⟩ (denote cache_64)] = denote cache_546
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_546

theorem verified_row_547 : fork [place ⟨443, 0, 7, 5⟩ cache_443, place ⟨510, 4, 7, 5⟩ cache_510, place ⟨131, 3, 3, 4⟩ cache_131] = cache_547 := by
  decide +kernel

theorem load_entry_547 : entryAt 547 = entry_547 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_547 : CacheEquation 547 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(547 < 6)), load_entry_547]
  change forkRow [placeRow ⟨443, 0, 7, 5⟩ (denote cache_443), placeRow ⟨510, 4, 7, 5⟩ (denote cache_510), placeRow ⟨131, 3, 3, 4⟩ (denote cache_131)] = denote cache_547
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_547

theorem verified_row_548 : fork [place ⟨426, 0, 4, 5⟩ cache_426, place ⟨541, 0, 4, 5⟩ cache_541, place ⟨25, 0, 5, 4⟩ cache_25, place ⟨321, 4, 4, 2⟩ cache_321] = cache_548 := by
  decide +kernel

theorem load_entry_548 : entryAt 548 = entry_548 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_548 : CacheEquation 548 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(548 < 6)), load_entry_548]
  change forkRow [placeRow ⟨426, 0, 4, 5⟩ (denote cache_426), placeRow ⟨541, 0, 4, 5⟩ (denote cache_541), placeRow ⟨25, 0, 5, 4⟩ (denote cache_25), placeRow ⟨321, 4, 4, 2⟩ (denote cache_321)] = denote cache_548
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_548

theorem verified_row_549 : fork [place ⟨385, 0, 6, 4⟩ cache_385, place ⟨385, 4, 2, 4⟩ cache_385, place ⟨330, 0, 6, 4⟩ cache_330, place ⟨252, 6, 2, 4⟩ cache_252, place ⟨326, 0, 6, 4⟩ cache_326, place ⟨529, 0, 2, 4⟩ cache_529] = cache_549 := by
  decide +kernel

theorem load_entry_549 : entryAt 549 = entry_549 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_549 : CacheEquation 549 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(549 < 6)), load_entry_549]
  change forkRow [placeRow ⟨385, 0, 6, 4⟩ (denote cache_385), placeRow ⟨385, 4, 2, 4⟩ (denote cache_385), placeRow ⟨330, 0, 6, 4⟩ (denote cache_330), placeRow ⟨252, 6, 2, 4⟩ (denote cache_252), placeRow ⟨326, 0, 6, 4⟩ (denote cache_326), placeRow ⟨529, 0, 2, 4⟩ (denote cache_529)] = denote cache_549
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_549

theorem verified_row_550 : fork [place ⟨424, 0, 4, 6⟩ cache_424, place ⟨172, 7, 4, 2⟩ cache_172, place ⟨215, 1, 5, 5⟩ cache_215, place ⟨456, 7, 4, 2⟩ cache_456] = cache_550 := by
  decide +kernel

theorem load_entry_550 : entryAt 550 = entry_550 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_550 : CacheEquation 550 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(550 < 6)), load_entry_550]
  change forkRow [placeRow ⟨424, 0, 4, 6⟩ (denote cache_424), placeRow ⟨172, 7, 4, 2⟩ (denote cache_172), placeRow ⟨215, 1, 5, 5⟩ (denote cache_215), placeRow ⟨456, 7, 4, 2⟩ (denote cache_456)] = denote cache_550
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_550

theorem verified_row_551 : fork [place ⟨300, 6, 4, 3⟩ cache_300, place ⟨172, 7, 4, 3⟩ cache_172, place ⟨319, 3, 5, 7⟩ cache_319, place ⟨527, 4, 5, 7⟩ cache_527, place ⟨176, 5, 4, 3⟩ cache_176] = cache_551 := by
  decide +kernel

theorem load_entry_551 : entryAt 551 = entry_551 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_551 : CacheEquation 551 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(551 < 6)), load_entry_551]
  change forkRow [placeRow ⟨300, 6, 4, 3⟩ (denote cache_300), placeRow ⟨172, 7, 4, 3⟩ (denote cache_172), placeRow ⟨319, 3, 5, 7⟩ (denote cache_319), placeRow ⟨527, 4, 5, 7⟩ (denote cache_527), placeRow ⟨176, 5, 4, 3⟩ (denote cache_176)] = denote cache_551
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_551

theorem verified_row_552 : fork [place ⟨443, 4, 1, 5⟩ cache_443, place ⟨64, 2, 1, 5⟩ cache_64, place ⟨504, 1, 3, 3⟩ cache_504, place ⟨404, 5, 2, 3⟩ cache_404] = cache_552 := by
  decide +kernel

theorem load_entry_552 : entryAt 552 = entry_552 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_552 : CacheEquation 552 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(552 < 6)), load_entry_552]
  change forkRow [placeRow ⟨443, 4, 1, 5⟩ (denote cache_443), placeRow ⟨64, 2, 1, 5⟩ (denote cache_64), placeRow ⟨504, 1, 3, 3⟩ (denote cache_504), placeRow ⟨404, 5, 2, 3⟩ (denote cache_404)] = denote cache_552
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_552

theorem verified_row_553 : fork [place ⟨63, 0, 3, 5⟩ cache_63, place ⟨261, 4, 5, 4⟩ cache_261, place ⟨471, 0, 5, 1⟩ cache_471, place ⟨442, 0, 4, 5⟩ cache_442, place ⟨504, 0, 3, 3⟩ cache_504, place ⟨180, 0, 4, 5⟩ cache_180] = cache_553 := by
  decide +kernel

theorem load_entry_553 : entryAt 553 = entry_553 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_553 : CacheEquation 553 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(553 < 6)), load_entry_553]
  change forkRow [placeRow ⟨63, 0, 3, 5⟩ (denote cache_63), placeRow ⟨261, 4, 5, 4⟩ (denote cache_261), placeRow ⟨471, 0, 5, 1⟩ (denote cache_471), placeRow ⟨442, 0, 4, 5⟩ (denote cache_442), placeRow ⟨504, 0, 3, 3⟩ (denote cache_504), placeRow ⟨180, 0, 4, 5⟩ (denote cache_180)] = denote cache_553
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_553

theorem verified_row_554 : fork [place ⟨30, 6, 5, 4⟩ cache_30, place ⟨96, 7, 4, 5⟩ cache_96, place ⟨474, 0, 4, 5⟩ cache_474] = cache_554 := by
  decide +kernel

theorem load_entry_554 : entryAt 554 = entry_554 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_554 : CacheEquation 554 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(554 < 6)), load_entry_554]
  change forkRow [placeRow ⟨30, 6, 5, 4⟩ (denote cache_30), placeRow ⟨96, 7, 4, 5⟩ (denote cache_96), placeRow ⟨474, 0, 4, 5⟩ (denote cache_474)] = denote cache_554
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_554

theorem verified_row_555 : fork [place ⟨504, 5, 3, 5⟩ cache_504, place ⟨513, 0, 1, 5⟩ cache_513, place ⟨55, 0, 5, 4⟩ cache_55, place ⟨443, 4, 1, 5⟩ cache_443, place ⟨471, 1, 1, 5⟩ cache_471] = cache_555 := by
  decide +kernel

theorem load_entry_555 : entryAt 555 = entry_555 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_555 : CacheEquation 555 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(555 < 6)), load_entry_555]
  change forkRow [placeRow ⟨504, 5, 3, 5⟩ (denote cache_504), placeRow ⟨513, 0, 1, 5⟩ (denote cache_513), placeRow ⟨55, 0, 5, 4⟩ (denote cache_55), placeRow ⟨443, 4, 1, 5⟩ (denote cache_443), placeRow ⟨471, 1, 1, 5⟩ (denote cache_471)] = denote cache_555
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_555

theorem verified_row_556 : fork [place ⟨34, 1, 4, 2⟩ cache_34, place ⟨549, 0, 3, 4⟩ cache_549] = cache_556 := by
  decide +kernel

theorem load_entry_556 : entryAt 556 = entry_556 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_556 : CacheEquation 556 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(556 < 6)), load_entry_556]
  change forkRow [placeRow ⟨34, 1, 4, 2⟩ (denote cache_34), placeRow ⟨549, 0, 3, 4⟩ (denote cache_549)] = denote cache_556
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_556

theorem verified_row_557 : fork [place ⟨460, 0, 5, 4⟩ cache_460, place ⟨460, 4, 2, 4⟩ cache_460, place ⟨460, 2, 5, 4⟩ cache_460, place ⟨411, 4, 5, 4⟩ cache_411, place ⟨531, 0, 3, 6⟩ cache_531, place ⟨531, 4, 4, 6⟩ cache_531, place ⟨406, 5, 5, 4⟩ cache_406] = cache_557 := by
  decide +kernel

theorem load_entry_557 : entryAt 557 = entry_557 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_557 : CacheEquation 557 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(557 < 6)), load_entry_557]
  change forkRow [placeRow ⟨460, 0, 5, 4⟩ (denote cache_460), placeRow ⟨460, 4, 2, 4⟩ (denote cache_460), placeRow ⟨460, 2, 5, 4⟩ (denote cache_460), placeRow ⟨411, 4, 5, 4⟩ (denote cache_411), placeRow ⟨531, 0, 3, 6⟩ (denote cache_531), placeRow ⟨531, 4, 4, 6⟩ (denote cache_531), placeRow ⟨406, 5, 5, 4⟩ (denote cache_406)] = denote cache_557
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_557

theorem verified_row_558 : fork [place ⟨180, 5, 5, 4⟩ cache_180, place ⟨443, 4, 1, 5⟩ cache_443, place ⟨513, 0, 1, 5⟩ cache_513, place ⟨442, 1, 5, 4⟩ cache_442] = cache_558 := by
  decide +kernel

theorem load_entry_558 : entryAt 558 = entry_558 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_558 : CacheEquation 558 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(558 < 6)), load_entry_558]
  change forkRow [placeRow ⟨180, 5, 5, 4⟩ (denote cache_180), placeRow ⟨443, 4, 1, 5⟩ (denote cache_443), placeRow ⟨513, 0, 1, 5⟩ (denote cache_513), placeRow ⟨442, 1, 5, 4⟩ (denote cache_442)] = denote cache_558
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_558

theorem verified_row_559 : fork [place ⟨228, 4, 5, 2⟩ cache_228, place ⟨7, 3, 3, 4⟩ cache_7, place ⟨155, 4, 4, 5⟩ cache_155, place ⟨538, 5, 4, 5⟩ cache_538] = cache_559 := by
  decide +kernel

theorem load_entry_559 : entryAt 559 = entry_559 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_559 : CacheEquation 559 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(559 < 6)), load_entry_559]
  change forkRow [placeRow ⟨228, 4, 5, 2⟩ (denote cache_228), placeRow ⟨7, 3, 3, 4⟩ (denote cache_7), placeRow ⟨155, 4, 4, 5⟩ (denote cache_155), placeRow ⟨538, 5, 4, 5⟩ (denote cache_538)] = denote cache_559
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_559

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_Equations14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

theorem verified_row_560 : fork [place ⟨517, 5, 5, 4⟩ cache_517, place ⟨416, 5, 4, 3⟩ cache_416, place ⟨359, 5, 3, 4⟩ cache_359, place ⟨356, 6, 3, 4⟩ cache_356, place ⟨483, 0, 4, 6⟩ cache_483] = cache_560 := by
  decide +kernel

theorem load_entry_560 : entryAt 560 = entry_560 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_560 : CacheEquation 560 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(560 < 6)), load_entry_560]
  change forkRow [placeRow ⟨517, 5, 5, 4⟩ (denote cache_517), placeRow ⟨416, 5, 4, 3⟩ (denote cache_416), placeRow ⟨359, 5, 3, 4⟩ (denote cache_359), placeRow ⟨356, 6, 3, 4⟩ (denote cache_356), placeRow ⟨483, 0, 4, 6⟩ (denote cache_483)] = denote cache_560
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_560

theorem verified_row_561 : fork [place ⟨295, 0, 5, 4⟩ cache_295, place ⟨173, 2, 5, 4⟩ cache_173, place ⟨263, 6, 1, 4⟩ cache_263, place ⟨236, 1, 5, 5⟩ cache_236, place ⟨546, 4, 5, 4⟩ cache_546, place ⟨176, 2, 5, 4⟩ cache_176, place ⟨535, 0, 4, 5⟩ cache_535] = cache_561 := by
  decide +kernel

theorem load_entry_561 : entryAt 561 = entry_561 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_561 : CacheEquation 561 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(561 < 6)), load_entry_561]
  change forkRow [placeRow ⟨295, 0, 5, 4⟩ (denote cache_295), placeRow ⟨173, 2, 5, 4⟩ (denote cache_173), placeRow ⟨263, 6, 1, 4⟩ (denote cache_263), placeRow ⟨236, 1, 5, 5⟩ (denote cache_236), placeRow ⟨546, 4, 5, 4⟩ (denote cache_546), placeRow ⟨176, 2, 5, 4⟩ (denote cache_176), placeRow ⟨535, 0, 4, 5⟩ (denote cache_535)] = denote cache_561
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_561

theorem verified_row_562 : fork [place ⟨6, 7, 3, 0⟩ cache_6, place ⟨559, 0, 4, 5⟩ cache_559] = cache_562 := by
  decide +kernel

theorem load_entry_562 : entryAt 562 = entry_562 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_562 : CacheEquation 562 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(562 < 6)), load_entry_562]
  change forkRow [placeRow ⟨6, 7, 3, 0⟩ (denote cache_6), placeRow ⟨559, 0, 4, 5⟩ (denote cache_559)] = denote cache_562
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_562

theorem verified_row_563 : fork [place ⟨167, 0, 7, 4⟩ cache_167, place ⟨538, 0, 3, 4⟩ cache_538, place ⟨514, 0, 7, 4⟩ cache_514, place ⟨330, 4, 3, 4⟩ cache_330, place ⟨545, 0, 5, 5⟩ cache_545] = cache_563 := by
  decide +kernel

theorem load_entry_563 : entryAt 563 = entry_563 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_563 : CacheEquation 563 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(563 < 6)), load_entry_563]
  change forkRow [placeRow ⟨167, 0, 7, 4⟩ (denote cache_167), placeRow ⟨538, 0, 3, 4⟩ (denote cache_538), placeRow ⟨514, 0, 7, 4⟩ (denote cache_514), placeRow ⟨330, 4, 3, 4⟩ (denote cache_330), placeRow ⟨545, 0, 5, 5⟩ (denote cache_545)] = denote cache_563
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_563

theorem verified_row_564 : fork [place ⟨560, 0, 4, 3⟩ cache_560, place ⟨421, 0, 3, 4⟩ cache_421, place ⟨401, 1, 3, 4⟩ cache_401, place ⟨340, 3, 3, 4⟩ cache_340, place ⟨509, 0, 3, 4⟩ cache_509, place ⟨528, 0, 4, 3⟩ cache_528, place ⟨423, 5, 4, 3⟩ cache_423, place ⟨425, 5, 4, 3⟩ cache_425, place ⟨336, 0, 3, 4⟩ cache_336] = cache_564 := by
  decide +kernel

theorem load_entry_564 : entryAt 564 = entry_564 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_564 : CacheEquation 564 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(564 < 6)), load_entry_564]
  change forkRow [placeRow ⟨560, 0, 4, 3⟩ (denote cache_560), placeRow ⟨421, 0, 3, 4⟩ (denote cache_421), placeRow ⟨401, 1, 3, 4⟩ (denote cache_401), placeRow ⟨340, 3, 3, 4⟩ (denote cache_340), placeRow ⟨509, 0, 3, 4⟩ (denote cache_509), placeRow ⟨528, 0, 4, 3⟩ (denote cache_528), placeRow ⟨423, 5, 4, 3⟩ (denote cache_423), placeRow ⟨425, 5, 4, 3⟩ (denote cache_425), placeRow ⟨336, 0, 3, 4⟩ (denote cache_336)] = denote cache_564
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_564

theorem verified_row_565 : fork [place ⟨443, 4, 4, 5⟩ cache_443, place ⟨131, 3, 3, 4⟩ cache_131, place ⟨538, 0, 3, 4⟩ cache_538, place ⟨459, 0, 5, 5⟩ cache_459, place ⟨144, 4, 3, 4⟩ cache_144] = cache_565 := by
  decide +kernel

theorem load_entry_565 : entryAt 565 = entry_565 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_565 : CacheEquation 565 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(565 < 6)), load_entry_565]
  change forkRow [placeRow ⟨443, 4, 4, 5⟩ (denote cache_443), placeRow ⟨131, 3, 3, 4⟩ (denote cache_131), placeRow ⟨538, 0, 3, 4⟩ (denote cache_538), placeRow ⟨459, 0, 5, 5⟩ (denote cache_459), placeRow ⟨144, 4, 3, 4⟩ (denote cache_144)] = denote cache_565
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_565

theorem verified_row_566 : fork [place ⟨314, 0, 3, 4⟩ cache_314, place ⟨180, 0, 4, 5⟩ cache_180, place ⟨442, 0, 4, 5⟩ cache_442, place ⟨466, 0, 6, 3⟩ cache_466, place ⟨504, 0, 3, 3⟩ cache_504] = cache_566 := by
  decide +kernel

theorem load_entry_566 : entryAt 566 = entry_566 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_566 : CacheEquation 566 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(566 < 6)), load_entry_566]
  change forkRow [placeRow ⟨314, 0, 3, 4⟩ (denote cache_314), placeRow ⟨180, 0, 4, 5⟩ (denote cache_180), placeRow ⟨442, 0, 4, 5⟩ (denote cache_442), placeRow ⟨466, 0, 6, 3⟩ (denote cache_466), placeRow ⟨504, 0, 3, 3⟩ (denote cache_504)] = denote cache_566
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_566

theorem verified_row_567 : fork [place ⟨21, 1, 4, 3⟩ cache_21, place ⟨561, 0, 6, 4⟩ cache_561, place ⟨500, 4, 3, 1⟩ cache_500] = cache_567 := by
  decide +kernel

theorem load_entry_567 : entryAt 567 = entry_567 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_567 : CacheEquation 567 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(567 < 6)), load_entry_567]
  change forkRow [placeRow ⟨21, 1, 4, 3⟩ (denote cache_21), placeRow ⟨561, 0, 6, 4⟩ (denote cache_561), placeRow ⟨500, 4, 3, 1⟩ (denote cache_500)] = denote cache_567
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_567

theorem verified_row_568 : fork [place ⟨538, 4, 6, 4⟩ cache_538, place ⟨547, 0, 2, 4⟩ cache_547, place ⟨275, 0, 6, 4⟩ cache_275, place ⟨565, 0, 2, 4⟩ cache_565, place ⟨330, 0, 6, 4⟩ cache_330] = cache_568 := by
  decide +kernel

theorem load_entry_568 : entryAt 568 = entry_568 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_568 : CacheEquation 568 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(568 < 6)), load_entry_568]
  change forkRow [placeRow ⟨538, 4, 6, 4⟩ (denote cache_538), placeRow ⟨547, 0, 2, 4⟩ (denote cache_547), placeRow ⟨275, 0, 6, 4⟩ (denote cache_275), placeRow ⟨565, 0, 2, 4⟩ (denote cache_565), placeRow ⟨330, 0, 6, 4⟩ (denote cache_330)] = denote cache_568
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_568

theorem verified_row_569 : fork [place ⟨34, 3, 4, 2⟩ cache_34, place ⟨568, 4, 5, 4⟩ cache_568] = cache_569 := by
  decide +kernel

theorem load_entry_569 : entryAt 569 = entry_569 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_569 : CacheEquation 569 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(569 < 6)), load_entry_569]
  change forkRow [placeRow ⟨34, 3, 4, 2⟩ (denote cache_34), placeRow ⟨568, 4, 5, 4⟩ (denote cache_568)] = denote cache_569
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_569

theorem verified_row_570 : fork [place ⟨569, 0, 2, 5⟩ cache_569, place ⟨2, 7, 4, 3⟩ cache_2] = cache_570 := by
  decide +kernel

theorem load_entry_570 : entryAt 570 = entry_570 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_570 : CacheEquation 570 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(570 < 6)), load_entry_570]
  change forkRow [placeRow ⟨569, 0, 2, 5⟩ (denote cache_569), placeRow ⟨2, 7, 4, 3⟩ (denote cache_2)] = denote cache_570
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_570

theorem verified_row_571 : fork [place ⟨293, 0, 4, 3⟩ cache_293, place ⟨570, 0, 4, 3⟩ cache_570, place ⟨382, 0, 4, 3⟩ cache_382, place ⟨556, 4, 2, 4⟩ cache_556] = cache_571 := by
  decide +kernel

theorem load_entry_571 : entryAt 571 = entry_571 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_571 : CacheEquation 571 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(571 < 6)), load_entry_571]
  change forkRow [placeRow ⟨293, 0, 4, 3⟩ (denote cache_293), placeRow ⟨570, 0, 4, 3⟩ (denote cache_570), placeRow ⟨382, 0, 4, 3⟩ (denote cache_382), placeRow ⟨556, 4, 2, 4⟩ (denote cache_556)] = denote cache_571
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_571

theorem verified_row_572 : fork [place ⟨564, 1, 6, 6⟩ cache_564, place ⟨465, 3, 3, 4⟩ cache_465, place ⟨385, 4, 3, 4⟩ cache_385, place ⟨364, 7, 3, 4⟩ cache_364, place ⟨499, 1, 6, 5⟩ cache_499] = cache_572 := by
  decide +kernel

theorem load_entry_572 : entryAt 572 = entry_572 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_572 : CacheEquation 572 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(572 < 6)), load_entry_572]
  change forkRow [placeRow ⟨564, 1, 6, 6⟩ (denote cache_564), placeRow ⟨465, 3, 3, 4⟩ (denote cache_465), placeRow ⟨385, 4, 3, 4⟩ (denote cache_385), placeRow ⟨364, 7, 3, 4⟩ (denote cache_364), placeRow ⟨499, 1, 6, 5⟩ (denote cache_499)] = denote cache_572
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_572

theorem verified_row_573 : fork [place ⟨527, 2, 3, 1⟩ cache_527, place ⟨499, 4, 3, 4⟩ cache_499, place ⟨527, 6, 5, 1⟩ cache_527, place ⟨499, 0, 5, 4⟩ cache_499, place ⟨407, 4, 4, 1⟩ cache_407, place ⟨531, 7, 2, 4⟩ cache_531, place ⟨407, 0, 4, 1⟩ cache_407] = cache_573 := by
  decide +kernel

theorem load_entry_573 : entryAt 573 = entry_573 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_573 : CacheEquation 573 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(573 < 6)), load_entry_573]
  change forkRow [placeRow ⟨527, 2, 3, 1⟩ (denote cache_527), placeRow ⟨499, 4, 3, 4⟩ (denote cache_499), placeRow ⟨527, 6, 5, 1⟩ (denote cache_527), placeRow ⟨499, 0, 5, 4⟩ (denote cache_499), placeRow ⟨407, 4, 4, 1⟩ (denote cache_407), placeRow ⟨531, 7, 2, 4⟩ (denote cache_531), placeRow ⟨407, 0, 4, 1⟩ (denote cache_407)] = denote cache_573
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_573

theorem verified_row_574 : fork [place ⟨497, 0, 2, 4⟩ cache_497, place ⟨539, 4, 4, 6⟩ cache_539, place ⟨355, 0, 2, 4⟩ cache_355, place ⟨390, 3, 2, 4⟩ cache_390, place ⟨544, 0, 2, 4⟩ cache_544, place ⟨462, 1, 4, 5⟩ cache_462, place ⟨563, 4, 5, 4⟩ cache_563, place ⟨540, 4, 4, 6⟩ cache_540, place ⟨518, 0, 2, 4⟩ cache_518, place ⟨495, 4, 2, 4⟩ cache_495] = cache_574 := by
  decide +kernel

theorem load_entry_574 : entryAt 574 = entry_574 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_574 : CacheEquation 574 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(574 < 6)), load_entry_574]
  change forkRow [placeRow ⟨497, 0, 2, 4⟩ (denote cache_497), placeRow ⟨539, 4, 4, 6⟩ (denote cache_539), placeRow ⟨355, 0, 2, 4⟩ (denote cache_355), placeRow ⟨390, 3, 2, 4⟩ (denote cache_390), placeRow ⟨544, 0, 2, 4⟩ (denote cache_544), placeRow ⟨462, 1, 4, 5⟩ (denote cache_462), placeRow ⟨563, 4, 5, 4⟩ (denote cache_563), placeRow ⟨540, 4, 4, 6⟩ (denote cache_540), placeRow ⟨518, 0, 2, 4⟩ (denote cache_518), placeRow ⟨495, 4, 2, 4⟩ (denote cache_495)] = denote cache_574
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_574

theorem verified_row_575 : fork [place ⟨314, 4, 5, 4⟩ cache_314, place ⟨504, 4, 5, 3⟩ cache_504, place ⟨180, 4, 4, 5⟩ cache_180, place ⟨442, 4, 4, 5⟩ cache_442, place ⟨559, 0, 4, 5⟩ cache_559] = cache_575 := by
  decide +kernel

theorem load_entry_575 : entryAt 575 = entry_575 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_575 : CacheEquation 575 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(575 < 6)), load_entry_575]
  change forkRow [placeRow ⟨314, 4, 5, 4⟩ (denote cache_314), placeRow ⟨504, 4, 5, 3⟩ (denote cache_504), placeRow ⟨180, 4, 4, 5⟩ (denote cache_180), placeRow ⟨442, 4, 4, 5⟩ (denote cache_442), placeRow ⟨559, 0, 4, 5⟩ (denote cache_559)] = denote cache_575
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_575

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

theorem cache_equations_range_544 : ∀ i, 544 ≤ i → i < 560 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_544
  · exact cache_equation_545
  · exact cache_equation_546
  · exact cache_equation_547
  · exact cache_equation_548
  · exact cache_equation_549
  · exact cache_equation_550
  · exact cache_equation_551
  · exact cache_equation_552
  · exact cache_equation_553
  · exact cache_equation_554
  · exact cache_equation_555
  · exact cache_equation_556
  · exact cache_equation_557
  · exact cache_equation_558
  · exact cache_equation_559

theorem cache_equations_range_560 : ∀ i, 560 ≤ i → i < 576 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_560
  · exact cache_equation_561
  · exact cache_equation_562
  · exact cache_equation_563
  · exact cache_equation_564
  · exact cache_equation_565
  · exact cache_equation_566
  · exact cache_equation_567
  · exact cache_equation_568
  · exact cache_equation_569
  · exact cache_equation_570
  · exact cache_equation_571
  · exact cache_equation_572
  · exact cache_equation_573
  · exact cache_equation_574
  · exact cache_equation_575

theorem cache_equations_range_544_576_oai : ∀ i, 544 ≤ i → i < 576 → CacheEquation i :=
  merge_ranges cache_equations_range_544 cache_equations_range_560

end SnakyCertificate.Check

end OAI
end

theorem solution : type_of% @OAI.SnakyCertificate.Check.cache_equations_range_544_576_oai := @OAI.SnakyCertificate.Check.cache_equations_range_544_576_oai
