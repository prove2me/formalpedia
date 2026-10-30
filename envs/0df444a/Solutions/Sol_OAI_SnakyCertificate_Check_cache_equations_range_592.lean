-- Prove2me | solution 1 for OAI.SnakyCertificate.Check.cache_equations_range_592
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T23:58:58.859156+00:00
-- url     : https://prove2.me/submissions/89d4fda4-8acc-4f28-b337-82650a8e65d3

import Mathlib
import Definitions.Def_SnakyCertificate
import Definitions.Def_OAIQ114S000
import Theorems.Thm_OAI_SnakyCertificate_Check_cache_equation_600
import Theorems.Thm_OAI_SnakyCertificate_Check_cache_equation_601
import Theorems.Thm_OAI_SnakyCertificate_Check_cache_equation_602
import Theorems.Thm_OAI_SnakyCertificate_Check_cache_equation_603
import Theorems.Thm_OAI_SnakyCertificate_Check_cache_equation_604
import Theorems.Thm_OAI_SnakyCertificate_Check_cache_equation_605
import Theorems.Thm_OAI_SnakyCertificate_Check_cache_equation_606
import Theorems.Thm_OAI_SnakyCertificate_Check_cache_equation_607

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

theorem verified_row_592 : fork [place ⟨588, 0, 4, 5⟩ cache_588, place ⟨108, 7, 3, 0⟩ cache_108] = cache_592 := by
  decide +kernel

theorem load_entry_592 : entryAt 592 = entry_592 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_592 : CacheEquation 592 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(592 < 6)), load_entry_592]
  change forkRow [placeRow ⟨588, 0, 4, 5⟩ (denote cache_588), placeRow ⟨108, 7, 3, 0⟩ (denote cache_108)] = denote cache_592
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_592

theorem verified_row_593 : fork [place ⟨2, 7, 4, 2⟩ cache_2, place ⟨586, 0, 4, 5⟩ cache_586] = cache_593 := by
  decide +kernel

theorem load_entry_593 : entryAt 593 = entry_593 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_593 : CacheEquation 593 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(593 < 6)), load_entry_593]
  change forkRow [placeRow ⟨2, 7, 4, 2⟩ (denote cache_2), placeRow ⟨586, 0, 4, 5⟩ (denote cache_586)] = denote cache_593
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_593

theorem verified_row_594 : fork [place ⟨30, 1, 4, 3⟩ cache_30, place ⟨476, 1, 4, 3⟩ cache_476, place ⟨588, 0, 4, 5⟩ cache_588] = cache_594 := by
  decide +kernel

theorem load_entry_594 : entryAt 594 = entry_594 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_594 : CacheEquation 594 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(594 < 6)), load_entry_594]
  change forkRow [placeRow ⟨30, 1, 4, 3⟩ (denote cache_30), placeRow ⟨476, 1, 4, 3⟩ (denote cache_476), placeRow ⟨588, 0, 4, 5⟩ (denote cache_588)] = denote cache_594
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_594

theorem verified_row_595 : fork [place ⟨460, 4, 2, 4⟩ cache_460, place ⟨460, 2, 5, 4⟩ cache_460, place ⟨586, 1, 5, 4⟩ cache_586, place ⟨411, 4, 5, 4⟩ cache_411, place ⟨551, 1, 2, 4⟩ cache_551, place ⟨406, 5, 5, 4⟩ cache_406, place ⟨572, 0, 2, 4⟩ cache_572] = cache_595 := by
  decide +kernel

theorem load_entry_595 : entryAt 595 = entry_595 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_595 : CacheEquation 595 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(595 < 6)), load_entry_595]
  change forkRow [placeRow ⟨460, 4, 2, 4⟩ (denote cache_460), placeRow ⟨460, 2, 5, 4⟩ (denote cache_460), placeRow ⟨586, 1, 5, 4⟩ (denote cache_586), placeRow ⟨411, 4, 5, 4⟩ (denote cache_411), placeRow ⟨551, 1, 2, 4⟩ (denote cache_551), placeRow ⟨406, 5, 5, 4⟩ (denote cache_406), placeRow ⟨572, 0, 2, 4⟩ (denote cache_572)] = denote cache_595
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_595

theorem verified_row_596 : fork [place ⟨385, 5, 4, 2⟩ cache_385, place ⟨592, 0, 5, 6⟩ cache_592, place ⟨330, 1, 4, 6⟩ cache_330, place ⟨529, 5, 4, 6⟩ cache_529, place ⟨385, 1, 4, 6⟩ cache_385, place ⟨330, 5, 4, 2⟩ cache_330] = cache_596 := by
  decide +kernel

theorem load_entry_596 : entryAt 596 = entry_596 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_596 : CacheEquation 596 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(596 < 6)), load_entry_596]
  change forkRow [placeRow ⟨385, 5, 4, 2⟩ (denote cache_385), placeRow ⟨592, 0, 5, 6⟩ (denote cache_592), placeRow ⟨330, 1, 4, 6⟩ (denote cache_330), placeRow ⟨529, 5, 4, 6⟩ (denote cache_529), placeRow ⟨385, 1, 4, 6⟩ (denote cache_385), placeRow ⟨330, 5, 4, 2⟩ (denote cache_330)] = denote cache_596
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_596

theorem verified_row_597 : fork [place ⟨24, 6, 2, 3⟩ cache_24, place ⟨221, 0, 6, 4⟩ cache_221, place ⟨199, 3, 2, 4⟩ cache_199, place ⟨594, 1, 6, 5⟩ cache_594] = cache_597 := by
  decide +kernel

theorem load_entry_597 : entryAt 597 = entry_597 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_597 : CacheEquation 597 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(597 < 6)), load_entry_597]
  change forkRow [placeRow ⟨24, 6, 2, 3⟩ (denote cache_24), placeRow ⟨221, 0, 6, 4⟩ (denote cache_221), placeRow ⟨199, 3, 2, 4⟩ (denote cache_199), placeRow ⟨594, 1, 6, 5⟩ (denote cache_594)] = denote cache_597
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_597

theorem verified_row_598 : fork [place ⟨594, 0, 5, 6⟩ cache_594, place ⟨456, 5, 4, 2⟩ cache_456, place ⟨254, 1, 3, 2⟩ cache_254, place ⟨554, 1, 3, 2⟩ cache_554, place ⟨465, 0, 4, 6⟩ cache_465] = cache_598 := by
  decide +kernel

theorem load_entry_598 : entryAt 598 = entry_598 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_598 : CacheEquation 598 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(598 < 6)), load_entry_598]
  change forkRow [placeRow ⟨594, 0, 5, 6⟩ (denote cache_594), placeRow ⟨456, 5, 4, 2⟩ (denote cache_456), placeRow ⟨254, 1, 3, 2⟩ (denote cache_254), placeRow ⟨554, 1, 3, 2⟩ (denote cache_554), placeRow ⟨465, 0, 4, 6⟩ (denote cache_465)] = denote cache_598
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_598

theorem verified_row_599 : fork [place ⟨578, 4, 5, 3⟩ cache_578, place ⟨492, 0, 3, 1⟩ cache_492, place ⟨512, 4, 3, 1⟩ cache_512, place ⟨586, 4, 4, 5⟩ cache_586, place ⟨485, 0, 5, 3⟩ cache_485, place ⟨579, 4, 5, 3⟩ cache_579] = cache_599 := by
  decide +kernel

theorem load_entry_599 : entryAt 599 = entry_599 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_599 : CacheEquation 599 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(599 < 6)), load_entry_599]
  change forkRow [placeRow ⟨578, 4, 5, 3⟩ (denote cache_578), placeRow ⟨492, 0, 3, 1⟩ (denote cache_492), placeRow ⟨512, 4, 3, 1⟩ (denote cache_512), placeRow ⟨586, 4, 4, 5⟩ (denote cache_586), placeRow ⟨485, 0, 5, 3⟩ (denote cache_485), placeRow ⟨579, 4, 5, 3⟩ (denote cache_579)] = denote cache_599
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_599

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

theorem cache_equations_range_592_oai : ∀ i, 592 ≤ i → i < 608 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_592
  · exact cache_equation_593
  · exact cache_equation_594
  · exact cache_equation_595
  · exact cache_equation_596
  · exact cache_equation_597
  · exact cache_equation_598
  · exact cache_equation_599
  · exact cache_equation_600
  · exact cache_equation_601
  · exact cache_equation_602
  · exact cache_equation_603
  · exact cache_equation_604
  · exact cache_equation_605
  · exact cache_equation_606
  · exact cache_equation_607

end SnakyCertificate.Check

end OAI
end

theorem solution : type_of% @OAI.SnakyCertificate.Check.cache_equations_range_592_oai := @OAI.SnakyCertificate.Check.cache_equations_range_592_oai
