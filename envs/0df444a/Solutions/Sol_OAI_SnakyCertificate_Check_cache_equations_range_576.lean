-- Prove2me | solution 1 for OAI.SnakyCertificate.Check.cache_equations_range_576
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T23:58:14.450784+00:00
-- url     : https://prove2.me/submissions/30ff9e59-88bc-4739-9fc3-0a91415675fb

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
-- module Solutions.OAIQ114_SC.SnakyCertificate_Equations14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

theorem verified_row_576 : fork [place ⟨495, 0, 5, 4⟩ cache_495, place ⟨544, 4, 5, 4⟩ cache_544, place ⟨462, 3, 3, 5⟩ cache_462, place ⟨540, 0, 3, 6⟩ cache_540, place ⟨355, 4, 5, 4⟩ cache_355, place ⟨539, 0, 3, 6⟩ cache_539, place ⟨497, 4, 5, 4⟩ cache_497, place ⟨390, 1, 5, 4⟩ cache_390, place ⟨563, 0, 2, 4⟩ cache_563, place ⟨518, 4, 5, 4⟩ cache_518] = cache_576 := by
  decide +kernel

theorem load_entry_576 : entryAt 576 = entry_576 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_576 : CacheEquation 576 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(576 < 6)), load_entry_576]
  change forkRow [placeRow ⟨495, 0, 5, 4⟩ (denote cache_495), placeRow ⟨544, 4, 5, 4⟩ (denote cache_544), placeRow ⟨462, 3, 3, 5⟩ (denote cache_462), placeRow ⟨540, 0, 3, 6⟩ (denote cache_540), placeRow ⟨355, 4, 5, 4⟩ (denote cache_355), placeRow ⟨539, 0, 3, 6⟩ (denote cache_539), placeRow ⟨497, 4, 5, 4⟩ (denote cache_497), placeRow ⟨390, 1, 5, 4⟩ (denote cache_390), placeRow ⟨563, 0, 2, 4⟩ (denote cache_563), placeRow ⟨518, 4, 5, 4⟩ (denote cache_518)] = denote cache_576
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_576

theorem verified_row_577 : fork [place ⟨64, 7, 5, 4⟩ cache_64, place ⟨64, 1, 3, 1⟩ cache_64, place ⟨443, 1, 5, 4⟩ cache_443, place ⟨443, 7, 3, 1⟩ cache_443] = cache_577 := by
  decide +kernel

theorem load_entry_577 : entryAt 577 = entry_577 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_577 : CacheEquation 577 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(577 < 6)), load_entry_577]
  change forkRow [placeRow ⟨64, 7, 5, 4⟩ (denote cache_64), placeRow ⟨64, 1, 3, 1⟩ (denote cache_64), placeRow ⟨443, 1, 5, 4⟩ (denote cache_443), placeRow ⟨443, 7, 3, 1⟩ (denote cache_443)] = denote cache_577
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_577

theorem verified_row_578 : fork [place ⟨574, 4, 4, 5⟩ cache_574, place ⟨2, 1, 4, 3⟩ cache_2] = cache_578 := by
  decide +kernel

theorem load_entry_578 : entryAt 578 = entry_578 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_578 : CacheEquation 578 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(578 < 6)), load_entry_578]
  change forkRow [placeRow ⟨574, 4, 4, 5⟩ (denote cache_574), placeRow ⟨2, 1, 4, 3⟩ (denote cache_2)] = denote cache_578
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_578

theorem verified_row_579 : fork [place ⟨2, 1, 4, 3⟩ cache_2, place ⟨576, 4, 4, 5⟩ cache_576] = cache_579 := by
  decide +kernel

theorem load_entry_579 : entryAt 579 = entry_579 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_579 : CacheEquation 579 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(579 < 6)), load_entry_579]
  change forkRow [placeRow ⟨2, 1, 4, 3⟩ (denote cache_2), placeRow ⟨576, 4, 4, 5⟩ (denote cache_576)] = denote cache_579
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_579

theorem verified_row_580 : fork [place ⟨2, 7, 4, 2⟩ cache_2, place ⟨579, 0, 3, 3⟩ cache_579] = cache_580 := by
  decide +kernel

theorem load_entry_580 : entryAt 580 = entry_580 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_580 : CacheEquation 580 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(580 < 6)), load_entry_580]
  change forkRow [placeRow ⟨2, 7, 4, 2⟩ (denote cache_2), placeRow ⟨579, 0, 3, 3⟩ (denote cache_579)] = denote cache_580
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_580

theorem verified_row_581 : fork [place ⟨578, 4, 5, 3⟩ cache_578, place ⟨2, 5, 4, 2⟩ cache_2] = cache_581 := by
  decide +kernel

theorem load_entry_581 : entryAt 581 = entry_581 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_581 : CacheEquation 581 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(581 < 6)), load_entry_581]
  change forkRow [placeRow ⟨578, 4, 5, 3⟩ (denote cache_578), placeRow ⟨2, 5, 4, 2⟩ (denote cache_2)] = denote cache_581
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_581

theorem verified_row_582 : fork [place ⟨40, 3, 4, 3⟩ cache_40, place ⟨446, 5, 5, 3⟩ cache_446, place ⟨523, 0, 7, 0⟩ cache_523, place ⟨480, 4, 5, 3⟩ cache_480, place ⟨567, 4, 5, 4⟩ cache_567] = cache_582 := by
  decide +kernel

theorem load_entry_582 : entryAt 582 = entry_582 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_582 : CacheEquation 582 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(582 < 6)), load_entry_582]
  change forkRow [placeRow ⟨40, 3, 4, 3⟩ (denote cache_40), placeRow ⟨446, 5, 5, 3⟩ (denote cache_446), placeRow ⟨523, 0, 7, 0⟩ (denote cache_523), placeRow ⟨480, 4, 5, 3⟩ (denote cache_480), placeRow ⟨567, 4, 5, 4⟩ (denote cache_567)] = denote cache_582
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_582

theorem verified_row_583 : fork [place ⟨25, 5, 4, 3⟩ cache_25, place ⟨525, 0, 5, 4⟩ cache_525, place ⟨582, 0, 2, 8⟩ cache_582, place ⟨221, 3, 3, 7⟩ cache_221] = cache_583 := by
  decide +kernel

theorem load_entry_583 : entryAt 583 = entry_583 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_583 : CacheEquation 583 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(583 < 6)), load_entry_583]
  change forkRow [placeRow ⟨25, 5, 4, 3⟩ (denote cache_25), placeRow ⟨525, 0, 5, 4⟩ (denote cache_525), placeRow ⟨582, 0, 2, 8⟩ (denote cache_582), placeRow ⟨221, 3, 3, 7⟩ (denote cache_221)] = denote cache_583
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_583

theorem verified_row_584 : fork [place ⟨263, 1, 4, 5⟩ cache_263, place ⟨236, 4, 3, 5⟩ cache_236, place ⟨548, 3, 3, 4⟩ cache_548, place ⟨295, 3, 4, 5⟩ cache_295, place ⟨577, 0, 4, 5⟩ cache_577, place ⟨173, 1, 4, 5⟩ cache_173] = cache_584 := by
  decide +kernel

theorem load_entry_584 : entryAt 584 = entry_584 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_584 : CacheEquation 584 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(584 < 6)), load_entry_584]
  change forkRow [placeRow ⟨263, 1, 4, 5⟩ (denote cache_263), placeRow ⟨236, 4, 3, 5⟩ (denote cache_236), placeRow ⟨548, 3, 3, 4⟩ (denote cache_548), placeRow ⟨295, 3, 4, 5⟩ (denote cache_295), placeRow ⟨577, 0, 4, 5⟩ (denote cache_577), placeRow ⟨173, 1, 4, 5⟩ (denote cache_173)] = denote cache_584
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_584

theorem verified_row_585 : fork [place ⟨236, 2, 5, 1⟩ cache_236, place ⟨300, 4, 4, 5⟩ cache_300, place ⟨479, 1, 4, 5⟩ cache_479, place ⟨577, 0, 4, 5⟩ cache_577, place ⟨183, 3, 4, 5⟩ cache_183, place ⟨527, 6, 5, 1⟩ cache_527] = cache_585 := by
  decide +kernel

theorem load_entry_585 : entryAt 585 = entry_585 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_585 : CacheEquation 585 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(585 < 6)), load_entry_585]
  change forkRow [placeRow ⟨236, 2, 5, 1⟩ (denote cache_236), placeRow ⟨300, 4, 4, 5⟩ (denote cache_300), placeRow ⟨479, 1, 4, 5⟩ (denote cache_479), placeRow ⟨577, 0, 4, 5⟩ (denote cache_577), placeRow ⟨183, 3, 4, 5⟩ (denote cache_183), placeRow ⟨527, 6, 5, 1⟩ (denote cache_527)] = denote cache_585
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_585

theorem verified_row_586 : fork [place ⟨465, 4, 4, 5⟩ cache_465, place ⟨558, 1, 4, 5⟩ cache_558, place ⟨385, 1, 4, 5⟩ cache_385, place ⟨379, 4, 4, 5⟩ cache_379, place ⟨524, 0, 4, 5⟩ cache_524, place ⟨469, 2, 4, 5⟩ cache_469, place ⟨467, 2, 4, 5⟩ cache_467, place ⟨527, 4, 5, 5⟩ cache_527, place ⟨553, 0, 4, 5⟩ cache_553, place ⟨552, 1, 4, 5⟩ cache_552, place ⟨555, 1, 4, 5⟩ cache_555, place ⟨564, 0, 6, 4⟩ cache_564, place ⟨583, 0, 5, 2⟩ cache_583] = cache_586 := by
  decide +kernel

theorem load_entry_586 : entryAt 586 = entry_586 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_586 : CacheEquation 586 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(586 < 6)), load_entry_586]
  change forkRow [placeRow ⟨465, 4, 4, 5⟩ (denote cache_465), placeRow ⟨558, 1, 4, 5⟩ (denote cache_558), placeRow ⟨385, 1, 4, 5⟩ (denote cache_385), placeRow ⟨379, 4, 4, 5⟩ (denote cache_379), placeRow ⟨524, 0, 4, 5⟩ (denote cache_524), placeRow ⟨469, 2, 4, 5⟩ (denote cache_469), placeRow ⟨467, 2, 4, 5⟩ (denote cache_467), placeRow ⟨527, 4, 5, 5⟩ (denote cache_527), placeRow ⟨553, 0, 4, 5⟩ (denote cache_553), placeRow ⟨552, 1, 4, 5⟩ (denote cache_552), placeRow ⟨555, 1, 4, 5⟩ (denote cache_555), placeRow ⟨564, 0, 6, 4⟩ (denote cache_564), placeRow ⟨583, 0, 5, 2⟩ (denote cache_583)] = denote cache_586
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_586

theorem verified_row_587 : fork [place ⟨300, 2, 4, 1⟩ cache_300, place ⟨479, 1, 4, 5⟩ cache_479, place ⟨319, 3, 5, 5⟩ cache_319, place ⟨477, 6, 4, 1⟩ cache_477, place ⟨252, 3, 4, 5⟩ cache_252, place ⟨467, 2, 4, 5⟩ cache_467] = cache_587 := by
  decide +kernel

theorem load_entry_587 : entryAt 587 = entry_587 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_587 : CacheEquation 587 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(587 < 6)), load_entry_587]
  change forkRow [placeRow ⟨300, 2, 4, 1⟩ (denote cache_300), placeRow ⟨479, 1, 4, 5⟩ (denote cache_479), placeRow ⟨319, 3, 5, 5⟩ (denote cache_319), placeRow ⟨477, 6, 4, 1⟩ (denote cache_477), placeRow ⟨252, 3, 4, 5⟩ (denote cache_252), placeRow ⟨467, 2, 4, 5⟩ (denote cache_467)] = denote cache_587
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_587

theorem verified_row_588 : fork [place ⟨3, 1, 3, 3⟩ cache_3, place ⟨586, 0, 4, 5⟩ cache_586] = cache_588 := by
  decide +kernel

theorem load_entry_588 : entryAt 588 = entry_588 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_588 : CacheEquation 588 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(588 < 6)), load_entry_588]
  change forkRow [placeRow ⟨3, 1, 3, 3⟩ (denote cache_3), placeRow ⟨586, 0, 4, 5⟩ (denote cache_586)] = denote cache_588
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_588

theorem verified_row_589 : fork [place ⟨4, 1, 4, 3⟩ cache_4, place ⟨588, 0, 4, 5⟩ cache_588] = cache_589 := by
  decide +kernel

theorem load_entry_589 : entryAt 589 = entry_589 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_589 : CacheEquation 589 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(589 < 6)), load_entry_589]
  change forkRow [placeRow ⟨4, 1, 4, 3⟩ (denote cache_4), placeRow ⟨588, 0, 4, 5⟩ (denote cache_588)] = denote cache_589
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_589

theorem verified_row_590 : fork [place ⟨295, 7, 4, 3⟩ cache_295, place ⟨173, 7, 4, 3⟩ cache_173, place ⟨577, 0, 4, 7⟩ cache_577, place ⟨490, 0, 4, 7⟩ cache_490, place ⟨217, 5, 4, 3⟩ cache_217] = cache_590 := by
  decide +kernel

theorem load_entry_590 : entryAt 590 = entry_590 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_590 : CacheEquation 590 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(590 < 6)), load_entry_590]
  change forkRow [placeRow ⟨295, 7, 4, 3⟩ (denote cache_295), placeRow ⟨173, 7, 4, 3⟩ (denote cache_173), placeRow ⟨577, 0, 4, 7⟩ (denote cache_577), placeRow ⟨490, 0, 4, 7⟩ (denote cache_490), placeRow ⟨217, 5, 4, 3⟩ (denote cache_217)] = denote cache_590
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_590

theorem verified_row_591 : fork [place ⟨524, 0, 4, 5⟩ cache_524, place ⟨529, 1, 4, 1⟩ cache_529, place ⟨529, 3, 4, 1⟩ cache_529, place ⟨538, 1, 4, 1⟩ cache_538, place ⟨538, 3, 4, 1⟩ cache_538, place ⟨197, 5, 4, 1⟩ cache_197] = cache_591 := by
  decide +kernel

theorem load_entry_591 : entryAt 591 = entry_591 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_591 : CacheEquation 591 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(591 < 6)), load_entry_591]
  change forkRow [placeRow ⟨524, 0, 4, 5⟩ (denote cache_524), placeRow ⟨529, 1, 4, 1⟩ (denote cache_529), placeRow ⟨529, 3, 4, 1⟩ (denote cache_529), placeRow ⟨538, 1, 4, 1⟩ (denote cache_538), placeRow ⟨538, 3, 4, 1⟩ (denote cache_538), placeRow ⟨197, 5, 4, 1⟩ (denote cache_197)] = denote cache_591
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_591

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

theorem cache_equations_range_576_oai : ∀ i, 576 ≤ i → i < 592 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_576
  · exact cache_equation_577
  · exact cache_equation_578
  · exact cache_equation_579
  · exact cache_equation_580
  · exact cache_equation_581
  · exact cache_equation_582
  · exact cache_equation_583
  · exact cache_equation_584
  · exact cache_equation_585
  · exact cache_equation_586
  · exact cache_equation_587
  · exact cache_equation_588
  · exact cache_equation_589
  · exact cache_equation_590
  · exact cache_equation_591

end SnakyCertificate.Check

end OAI
end

theorem solution : type_of% @OAI.SnakyCertificate.Check.cache_equations_range_576_oai := @OAI.SnakyCertificate.Check.cache_equations_range_576_oai
