-- Prove2me | solution 1 for OAI.SnakyCertificate.Check.cache_equations_range_384_464
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T23:55:41.520581+00:00
-- url     : https://prove2.me/submissions/55347b50-7b7f-49fe-947f-b30529d2daf3

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
-- module Solutions.OAIQ114_SC.SnakyCertificate_Equations09
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

theorem verified_row_384 : fork [place ⟨173, 2, 6, 4⟩ cache_173, place ⟨282, 4, 2, 4⟩ cache_282, place ⟨220, 2, 6, 4⟩ cache_220, place ⟨246, 2, 6, 4⟩ cache_246, place ⟨263, 2, 6, 4⟩ cache_263, place ⟨183, 6, 2, 4⟩ cache_183, place ⟨295, 0, 6, 4⟩ cache_295] = cache_384 := by
  decide +kernel

theorem load_entry_384 : entryAt 384 = entry_384 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_384 : CacheEquation 384 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(384 < 6)), load_entry_384]
  change forkRow [placeRow ⟨173, 2, 6, 4⟩ (denote cache_173), placeRow ⟨282, 4, 2, 4⟩ (denote cache_282), placeRow ⟨220, 2, 6, 4⟩ (denote cache_220), placeRow ⟨246, 2, 6, 4⟩ (denote cache_246), placeRow ⟨263, 2, 6, 4⟩ (denote cache_263), placeRow ⟨183, 6, 2, 4⟩ (denote cache_183), placeRow ⟨295, 0, 6, 4⟩ (denote cache_295)] = denote cache_384
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_384

theorem verified_row_385 : fork [place ⟨63, 1, 5, 3⟩ cache_63, place ⟨64, 2, 1, 5⟩ cache_64, place ⟨55, 0, 5, 4⟩ cache_55, place ⟨369, 4, 1, 5⟩ cache_369] = cache_385 := by
  decide +kernel

theorem load_entry_385 : entryAt 385 = entry_385 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_385 : CacheEquation 385 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(385 < 6)), load_entry_385]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (denote cache_63), placeRow ⟨64, 2, 1, 5⟩ (denote cache_64), placeRow ⟨55, 0, 5, 4⟩ (denote cache_55), placeRow ⟨369, 4, 1, 5⟩ (denote cache_369)] = denote cache_385
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_385

theorem verified_row_386 : fork [place ⟨217, 4, 1, 4⟩ cache_217, place ⟨172, 0, 5, 4⟩ cache_172, place ⟨173, 4, 1, 4⟩ cache_173, place ⟨217, 0, 5, 4⟩ cache_217, place ⟨294, 0, 5, 4⟩ cache_294, place ⟨294, 4, 1, 4⟩ cache_294] = cache_386 := by
  decide +kernel

theorem load_entry_386 : entryAt 386 = entry_386 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_386 : CacheEquation 386 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(386 < 6)), load_entry_386]
  change forkRow [placeRow ⟨217, 4, 1, 4⟩ (denote cache_217), placeRow ⟨172, 0, 5, 4⟩ (denote cache_172), placeRow ⟨173, 4, 1, 4⟩ (denote cache_173), placeRow ⟨217, 0, 5, 4⟩ (denote cache_217), placeRow ⟨294, 0, 5, 4⟩ (denote cache_294), placeRow ⟨294, 4, 1, 4⟩ (denote cache_294)] = denote cache_386
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_386

theorem verified_row_387 : fork [place ⟨14, 1, 4, 6⟩ cache_14, place ⟨370, 0, 5, 4⟩ cache_370] = cache_387 := by
  decide +kernel

theorem load_entry_387 : entryAt 387 = entry_387 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_387 : CacheEquation 387 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(387 < 6)), load_entry_387]
  change forkRow [placeRow ⟨14, 1, 4, 6⟩ (denote cache_14), placeRow ⟨370, 0, 5, 4⟩ (denote cache_370)] = denote cache_387
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_387

theorem verified_row_388 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨374, 0, 3, 4⟩ cache_374] = cache_388 := by
  decide +kernel

theorem load_entry_388 : entryAt 388 = entry_388 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_388 : CacheEquation 388 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(388 < 6)), load_entry_388]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨374, 0, 3, 4⟩ (denote cache_374)] = denote cache_388
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_388

theorem verified_row_389 : fork [place ⟨197, 5, 4, 1⟩ cache_197, place ⟨215, 7, 3, 2⟩ cache_215, place ⟨271, 3, 3, 2⟩ cache_271, place ⟨236, 0, 5, 5⟩ cache_236, place ⟨192, 6, 4, 1⟩ cache_192] = cache_389 := by
  decide +kernel

theorem load_entry_389 : entryAt 389 = entry_389 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_389 : CacheEquation 389 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(389 < 6)), load_entry_389]
  change forkRow [placeRow ⟨197, 5, 4, 1⟩ (denote cache_197), placeRow ⟨215, 7, 3, 2⟩ (denote cache_215), placeRow ⟨271, 3, 3, 2⟩ (denote cache_271), placeRow ⟨236, 0, 5, 5⟩ (denote cache_236), placeRow ⟨192, 6, 4, 1⟩ (denote cache_192)] = denote cache_389
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_389

theorem verified_row_390 : fork [place ⟨372, 2, 5, 0⟩ cache_372, place ⟨167, 5, 4, 1⟩ cache_167, place ⟨12, 7, 3, 1⟩ cache_12] = cache_390 := by
  decide +kernel

theorem load_entry_390 : entryAt 390 = entry_390 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_390 : CacheEquation 390 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(390 < 6)), load_entry_390]
  change forkRow [placeRow ⟨372, 2, 5, 0⟩ (denote cache_372), placeRow ⟨167, 5, 4, 1⟩ (denote cache_167), placeRow ⟨12, 7, 3, 1⟩ (denote cache_12)] = denote cache_390
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_390

theorem verified_row_391 : fork [place ⟨6, 5, 5, 1⟩ cache_6, place ⟨388, 0, 3, 5⟩ cache_388] = cache_391 := by
  decide +kernel

theorem load_entry_391 : entryAt 391 = entry_391 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_391 : CacheEquation 391 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(391 < 6)), load_entry_391]
  change forkRow [placeRow ⟨6, 5, 5, 1⟩ (denote cache_6), placeRow ⟨388, 0, 3, 5⟩ (denote cache_388)] = denote cache_391
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_391

theorem verified_row_392 : fork [place ⟨24, 7, 3, 1⟩ cache_24, place ⟨107, 1, 4, 5⟩ cache_107, place ⟨236, 0, 5, 5⟩ cache_236, place ⟨364, 2, 4, 1⟩ cache_364] = cache_392 := by
  decide +kernel

theorem load_entry_392 : entryAt 392 = entry_392 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_392 : CacheEquation 392 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(392 < 6)), load_entry_392]
  change forkRow [placeRow ⟨24, 7, 3, 1⟩ (denote cache_24), placeRow ⟨107, 1, 4, 5⟩ (denote cache_107), placeRow ⟨236, 0, 5, 5⟩ (denote cache_236), placeRow ⟨364, 2, 4, 1⟩ (denote cache_364)] = denote cache_392
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_392

theorem verified_row_393 : fork [place ⟨107, 3, 4, 5⟩ cache_107, place ⟨348, 0, 6, 3⟩ cache_348, place ⟨65, 3, 4, 5⟩ cache_65, place ⟨303, 0, 4, 5⟩ cache_303] = cache_393 := by
  decide +kernel

theorem load_entry_393 : entryAt 393 = entry_393 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_393 : CacheEquation 393 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(393 < 6)), load_entry_393]
  change forkRow [placeRow ⟨107, 3, 4, 5⟩ (denote cache_107), placeRow ⟨348, 0, 6, 3⟩ (denote cache_348), placeRow ⟨65, 3, 4, 5⟩ (denote cache_65), placeRow ⟨303, 0, 4, 5⟩ (denote cache_303)] = denote cache_393
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_393

theorem verified_row_394 : fork [place ⟨226, 4, 1, 4⟩ cache_226, place ⟨226, 0, 5, 4⟩ cache_226, place ⟨327, 4, 3, 4⟩ cache_327, place ⟨327, 6, 3, 3⟩ cache_327, place ⟨226, 6, 1, 3⟩ cache_226, place ⟨226, 2, 5, 3⟩ cache_226] = cache_394 := by
  decide +kernel

theorem load_entry_394 : entryAt 394 = entry_394 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_394 : CacheEquation 394 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(394 < 6)), load_entry_394]
  change forkRow [placeRow ⟨226, 4, 1, 4⟩ (denote cache_226), placeRow ⟨226, 0, 5, 4⟩ (denote cache_226), placeRow ⟨327, 4, 3, 4⟩ (denote cache_327), placeRow ⟨327, 6, 3, 3⟩ (denote cache_327), placeRow ⟨226, 6, 1, 3⟩ (denote cache_226), placeRow ⟨226, 2, 5, 3⟩ (denote cache_226)] = denote cache_394
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_394

theorem verified_row_395 : fork [place ⟨211, 4, 2, 4⟩ cache_211, place ⟨376, 0, 6, 4⟩ cache_376, place ⟨24, 2, 6, 3⟩ cache_24, place ⟨236, 3, 2, 5⟩ cache_236] = cache_395 := by
  decide +kernel

theorem load_entry_395 : entryAt 395 = entry_395 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_395 : CacheEquation 395 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(395 < 6)), load_entry_395]
  change forkRow [placeRow ⟨211, 4, 2, 4⟩ (denote cache_211), placeRow ⟨376, 0, 6, 4⟩ (denote cache_376), placeRow ⟨24, 2, 6, 3⟩ (denote cache_24), placeRow ⟨236, 3, 2, 5⟩ (denote cache_236)] = denote cache_395
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_395

theorem verified_row_396 : fork [place ⟨107, 3, 4, 5⟩ cache_107, place ⟨365, 1, 7, 3⟩ cache_365, place ⟨303, 0, 4, 5⟩ cache_303, place ⟨65, 3, 4, 5⟩ cache_65] = cache_396 := by
  decide +kernel

theorem load_entry_396 : entryAt 396 = entry_396 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_396 : CacheEquation 396 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(396 < 6)), load_entry_396]
  change forkRow [placeRow ⟨107, 3, 4, 5⟩ (denote cache_107), placeRow ⟨365, 1, 7, 3⟩ (denote cache_365), placeRow ⟨303, 0, 4, 5⟩ (denote cache_303), placeRow ⟨65, 3, 4, 5⟩ (denote cache_65)] = denote cache_396
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_396

theorem verified_row_397 : fork [place ⟨24, 3, 4, 5⟩ cache_24, place ⟨374, 0, 3, 4⟩ cache_374, place ⟨65, 5, 5, 1⟩ cache_65] = cache_397 := by
  decide +kernel

theorem load_entry_397 : entryAt 397 = entry_397 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_397 : CacheEquation 397 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(397 < 6)), load_entry_397]
  change forkRow [placeRow ⟨24, 3, 4, 5⟩ (denote cache_24), placeRow ⟨374, 0, 3, 4⟩ (denote cache_374), placeRow ⟨65, 5, 5, 1⟩ (denote cache_65)] = denote cache_397
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_397

theorem verified_row_398 : fork [place ⟨257, 0, 1, 3⟩ cache_257, place ⟨363, 0, 5, 4⟩ cache_363, place ⟨130, 1, 4, 2⟩ cache_130, place ⟨177, 1, 4, 2⟩ cache_177] = cache_398 := by
  decide +kernel

theorem load_entry_398 : entryAt 398 = entry_398 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_398 : CacheEquation 398 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(398 < 6)), load_entry_398]
  change forkRow [placeRow ⟨257, 0, 1, 3⟩ (denote cache_257), placeRow ⟨363, 0, 5, 4⟩ (denote cache_363), placeRow ⟨130, 1, 4, 2⟩ (denote cache_130), placeRow ⟨177, 1, 4, 2⟩ (denote cache_177)] = denote cache_398
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_398

theorem verified_row_399 : fork [place ⟨192, 6, 4, 1⟩ cache_192, place ⟨271, 3, 3, 2⟩ cache_271, place ⟨173, 1, 4, 5⟩ cache_173, place ⟨319, 1, 3, 5⟩ cache_319, place ⟨215, 7, 3, 2⟩ cache_215] = cache_399 := by
  decide +kernel

theorem load_entry_399 : entryAt 399 = entry_399 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_399 : CacheEquation 399 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(399 < 6)), load_entry_399]
  change forkRow [placeRow ⟨192, 6, 4, 1⟩ (denote cache_192), placeRow ⟨271, 3, 3, 2⟩ (denote cache_271), placeRow ⟨173, 1, 4, 5⟩ (denote cache_173), placeRow ⟨319, 1, 3, 5⟩ (denote cache_319), placeRow ⟨215, 7, 3, 2⟩ (denote cache_215)] = denote cache_399
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_399

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_Equations10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

theorem verified_row_400 : fork [place ⟨283, 4, 2, 4⟩ cache_283, place ⟨252, 4, 2, 4⟩ cache_252, place ⟨176, 4, 2, 4⟩ cache_176, place ⟨197, 0, 6, 4⟩ cache_197, place ⟨283, 0, 6, 4⟩ cache_283, place ⟨245, 4, 2, 4⟩ cache_245] = cache_400 := by
  decide +kernel

theorem load_entry_400 : entryAt 400 = entry_400 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_400 : CacheEquation 400 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(400 < 6)), load_entry_400]
  change forkRow [placeRow ⟨283, 4, 2, 4⟩ (denote cache_283), placeRow ⟨252, 4, 2, 4⟩ (denote cache_252), placeRow ⟨176, 4, 2, 4⟩ (denote cache_176), placeRow ⟨197, 0, 6, 4⟩ (denote cache_197), placeRow ⟨283, 0, 6, 4⟩ (denote cache_283), placeRow ⟨245, 4, 2, 4⟩ (denote cache_245)] = denote cache_400
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_400

theorem verified_row_401 : fork [place ⟨24, 7, 3, 2⟩ cache_24, place ⟨286, 0, 4, 6⟩ cache_286, place ⟨364, 2, 4, 2⟩ cache_364, place ⟨319, 1, 3, 6⟩ cache_319] = cache_401 := by
  decide +kernel

theorem load_entry_401 : entryAt 401 = entry_401 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_401 : CacheEquation 401 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(401 < 6)), load_entry_401]
  change forkRow [placeRow ⟨24, 7, 3, 2⟩ (denote cache_24), placeRow ⟨286, 0, 4, 6⟩ (denote cache_286), placeRow ⟨364, 2, 4, 2⟩ (denote cache_364), placeRow ⟨319, 1, 3, 6⟩ (denote cache_319)] = denote cache_401
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_401

theorem verified_row_402 : fork [place ⟨29, 3, 3, 0⟩ cache_29, place ⟨384, 0, 5, 4⟩ cache_384] = cache_402 := by
  decide +kernel

theorem load_entry_402 : entryAt 402 = entry_402 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_402 : CacheEquation 402 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(402 < 6)), load_entry_402]
  change forkRow [placeRow ⟨29, 3, 3, 0⟩ (denote cache_29), placeRow ⟨384, 0, 5, 4⟩ (denote cache_384)] = denote cache_402
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_402

theorem verified_row_403 : fork [place ⟨202, 1, 4, 5⟩ cache_202, place ⟨180, 0, 4, 5⟩ cache_180, place ⟨314, 4, 5, 4⟩ cache_314, place ⟨63, 0, 3, 5⟩ cache_63, place ⟨388, 0, 3, 4⟩ cache_388] = cache_403 := by
  decide +kernel

theorem load_entry_403 : entryAt 403 = entry_403 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_403 : CacheEquation 403 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(403 < 6)), load_entry_403]
  change forkRow [placeRow ⟨202, 1, 4, 5⟩ (denote cache_202), placeRow ⟨180, 0, 4, 5⟩ (denote cache_180), placeRow ⟨314, 4, 5, 4⟩ (denote cache_314), placeRow ⟨63, 0, 3, 5⟩ (denote cache_63), placeRow ⟨388, 0, 3, 4⟩ (denote cache_388)] = denote cache_403
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_403

theorem verified_row_404 : fork [place ⟨82, 6, 2, 3⟩ cache_82, place ⟨388, 4, 4, 6⟩ cache_388] = cache_404 := by
  decide +kernel

theorem load_entry_404 : entryAt 404 = entry_404 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_404 : CacheEquation 404 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(404 < 6)), load_entry_404]
  change forkRow [placeRow ⟨82, 6, 2, 3⟩ (denote cache_82), placeRow ⟨388, 4, 4, 6⟩ (denote cache_388)] = denote cache_404
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_404

theorem verified_row_405 : fork [place ⟨391, 0, 4, 3⟩ cache_391, place ⟨301, 0, 5, 2⟩ cache_301, place ⟨42, 1, 4, 3⟩ cache_42] = cache_405 := by
  decide +kernel

theorem load_entry_405 : entryAt 405 = entry_405 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_405 : CacheEquation 405 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(405 < 6)), load_entry_405]
  change forkRow [placeRow ⟨391, 0, 4, 3⟩ (denote cache_391), placeRow ⟨301, 0, 5, 2⟩ (denote cache_301), placeRow ⟨42, 1, 4, 3⟩ (denote cache_42)] = denote cache_405
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_405

theorem verified_row_406 : fork [place ⟨295, 1, 4, 5⟩ cache_295, place ⟨172, 7, 4, 1⟩ cache_172, place ⟨245, 3, 4, 5⟩ cache_245, place ⟨197, 5, 4, 1⟩ cache_197, place ⟨236, 0, 5, 5⟩ cache_236, place ⟨176, 3, 4, 5⟩ cache_176, place ⟨364, 2, 4, 1⟩ cache_364] = cache_406 := by
  decide +kernel

theorem load_entry_406 : entryAt 406 = entry_406 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_406 : CacheEquation 406 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(406 < 6)), load_entry_406]
  change forkRow [placeRow ⟨295, 1, 4, 5⟩ (denote cache_295), placeRow ⟨172, 7, 4, 1⟩ (denote cache_172), placeRow ⟨245, 3, 4, 5⟩ (denote cache_245), placeRow ⟨197, 5, 4, 1⟩ (denote cache_197), placeRow ⟨236, 0, 5, 5⟩ (denote cache_236), placeRow ⟨176, 3, 4, 5⟩ (denote cache_176), placeRow ⟨364, 2, 4, 1⟩ (denote cache_364)] = denote cache_406
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_406

theorem verified_row_407 : fork [place ⟨285, 0, 3, 7⟩ cache_285, place ⟨314, 6, 5, 4⟩ cache_314] = cache_407 := by
  decide +kernel

theorem load_entry_407 : entryAt 407 = entry_407 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_407 : CacheEquation 407 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(407 < 6)), load_entry_407]
  change forkRow [placeRow ⟨285, 0, 3, 7⟩ (denote cache_285), placeRow ⟨314, 6, 5, 4⟩ (denote cache_314)] = denote cache_407
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_407

theorem verified_row_408 : fork [place ⟨357, 0, 5, 2⟩ cache_357, place ⟨229, 7, 2, 4⟩ cache_229, place ⟨223, 4, 2, 4⟩ cache_223, place ⟨223, 0, 6, 4⟩ cache_223] = cache_408 := by
  decide +kernel

theorem load_entry_408 : entryAt 408 = entry_408 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_408 : CacheEquation 408 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(408 < 6)), load_entry_408]
  change forkRow [placeRow ⟨357, 0, 5, 2⟩ (denote cache_357), placeRow ⟨229, 7, 2, 4⟩ (denote cache_229), placeRow ⟨223, 4, 2, 4⟩ (denote cache_223), placeRow ⟨223, 0, 6, 4⟩ (denote cache_223)] = denote cache_408
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_408

theorem verified_row_409 : fork [place ⟨136, 6, 4, 3⟩ cache_136, place ⟨384, 0, 5, 4⟩ cache_384, place ⟨133, 4, 4, 3⟩ cache_133, place ⟨110, 3, 4, 3⟩ cache_110] = cache_409 := by
  decide +kernel

theorem load_entry_409 : entryAt 409 = entry_409 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_409 : CacheEquation 409 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(409 < 6)), load_entry_409]
  change forkRow [placeRow ⟨136, 6, 4, 3⟩ (denote cache_136), placeRow ⟨384, 0, 5, 4⟩ (denote cache_384), placeRow ⟨133, 4, 4, 3⟩ (denote cache_133), placeRow ⟨110, 3, 4, 3⟩ (denote cache_110)] = denote cache_409
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_409

theorem verified_row_410 : fork [place ⟨0, 4, 5, 4⟩ cache_0, place ⟨405, 0, 3, 7⟩ cache_405] = cache_410 := by
  decide +kernel

theorem load_entry_410 : entryAt 410 = entry_410 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_410 : CacheEquation 410 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(410 < 6)), load_entry_410]
  change forkRow [placeRow ⟨0, 4, 5, 4⟩ (denote cache_0), placeRow ⟨405, 0, 3, 7⟩ (denote cache_405)] = denote cache_410
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_410

theorem verified_row_411 : fork [place ⟨252, 0, 7, 4⟩ cache_252, place ⟨263, 0, 7, 4⟩ cache_263, place ⟨300, 3, 3, 4⟩ cache_300, place ⟨379, 1, 7, 4⟩ cache_379, place ⟨173, 0, 7, 4⟩ cache_173, place ⟨246, 0, 7, 4⟩ cache_246] = cache_411 := by
  decide +kernel

theorem load_entry_411 : entryAt 411 = entry_411 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_411 : CacheEquation 411 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(411 < 6)), load_entry_411]
  change forkRow [placeRow ⟨252, 0, 7, 4⟩ (denote cache_252), placeRow ⟨263, 0, 7, 4⟩ (denote cache_263), placeRow ⟨300, 3, 3, 4⟩ (denote cache_300), placeRow ⟨379, 1, 7, 4⟩ (denote cache_379), placeRow ⟨173, 0, 7, 4⟩ (denote cache_173), placeRow ⟨246, 0, 7, 4⟩ (denote cache_246)] = denote cache_411
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_411

theorem verified_row_412 : fork [place ⟨0, 0, 0, 3⟩ cache_0, place ⟨403, 4, 3, 6⟩ cache_403] = cache_412 := by
  decide +kernel

theorem load_entry_412 : entryAt 412 = entry_412 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_412 : CacheEquation 412 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(412 < 6)), load_entry_412]
  change forkRow [placeRow ⟨0, 0, 0, 3⟩ (denote cache_0), placeRow ⟨403, 4, 3, 6⟩ (denote cache_403)] = denote cache_412
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_412

theorem verified_row_413 : fork [place ⟨3, 7, 4, 3⟩ cache_3, place ⟨403, 0, 4, 7⟩ cache_403] = cache_413 := by
  decide +kernel

theorem load_entry_413 : entryAt 413 = entry_413 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_413 : CacheEquation 413 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(413 < 6)), load_entry_413]
  change forkRow [placeRow ⟨3, 7, 4, 3⟩ (denote cache_3), placeRow ⟨403, 0, 4, 7⟩ (denote cache_403)] = denote cache_413
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_413

theorem verified_row_414 : fork [place ⟨374, 0, 2, 5⟩ cache_374, place ⟨199, 2, 4, 2⟩ cache_199, place ⟨185, 2, 4, 2⟩ cache_185] = cache_414 := by
  decide +kernel

theorem load_entry_414 : entryAt 414 = entry_414 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_414 : CacheEquation 414 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(414 < 6)), load_entry_414]
  change forkRow [placeRow ⟨374, 0, 2, 5⟩ (denote cache_374), placeRow ⟨199, 2, 4, 2⟩ (denote cache_199), placeRow ⟨185, 2, 4, 2⟩ (denote cache_185)] = denote cache_414
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_414

theorem verified_row_415 : fork [place ⟨177, 1, 4, 2⟩ cache_177, place ⟨164, 1, 4, 2⟩ cache_164, place ⟨205, 1, 5, 2⟩ cache_205, place ⟨384, 0, 3, 4⟩ cache_384, place ⟨371, 0, 5, 4⟩ cache_371] = cache_415 := by
  decide +kernel

theorem load_entry_415 : entryAt 415 = entry_415 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_415 : CacheEquation 415 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(415 < 6)), load_entry_415]
  change forkRow [placeRow ⟨177, 1, 4, 2⟩ (denote cache_177), placeRow ⟨164, 1, 4, 2⟩ (denote cache_164), placeRow ⟨205, 1, 5, 2⟩ (denote cache_205), placeRow ⟨384, 0, 3, 4⟩ (denote cache_384), placeRow ⟨371, 0, 5, 4⟩ (denote cache_371)] = denote cache_415
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_415

theorem verified_row_416 : fork [place ⟨176, 2, 5, 4⟩ cache_176, place ⟨385, 4, 1, 4⟩ cache_385, place ⟨197, 4, 1, 4⟩ cache_197, place ⟨295, 0, 5, 4⟩ cache_295, place ⟨245, 2, 5, 4⟩ cache_245, place ⟨220, 2, 5, 4⟩ cache_220] = cache_416 := by
  decide +kernel

theorem load_entry_416 : entryAt 416 = entry_416 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_416 : CacheEquation 416 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(416 < 6)), load_entry_416]
  change forkRow [placeRow ⟨176, 2, 5, 4⟩ (denote cache_176), placeRow ⟨385, 4, 1, 4⟩ (denote cache_385), placeRow ⟨197, 4, 1, 4⟩ (denote cache_197), placeRow ⟨295, 0, 5, 4⟩ (denote cache_295), placeRow ⟨245, 2, 5, 4⟩ (denote cache_245), placeRow ⟨220, 2, 5, 4⟩ (denote cache_220)] = denote cache_416
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_416

theorem verified_row_417 : fork [place ⟨409, 0, 2, 4⟩ cache_409, place ⟨11, 1, 4, 2⟩ cache_11, place ⟨270, 4, 4, 2⟩ cache_270] = cache_417 := by
  decide +kernel

theorem load_entry_417 : entryAt 417 = entry_417 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_417 : CacheEquation 417 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(417 < 6)), load_entry_417]
  change forkRow [placeRow ⟨409, 0, 2, 4⟩ (denote cache_409), placeRow ⟨11, 1, 4, 2⟩ (denote cache_11), placeRow ⟨270, 4, 4, 2⟩ (denote cache_270)] = denote cache_417
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_417

theorem verified_row_418 : fork [place ⟨68, 4, 1, 3⟩ cache_68, place ⟨62, 6, 1, 3⟩ cache_62, place ⟨147, 6, 1, 3⟩ cache_147, place ⟨413, 0, 4, 2⟩ cache_413] = cache_418 := by
  decide +kernel

theorem load_entry_418 : entryAt 418 = entry_418 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_418 : CacheEquation 418 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(418 < 6)), load_entry_418]
  change forkRow [placeRow ⟨68, 4, 1, 3⟩ (denote cache_68), placeRow ⟨62, 6, 1, 3⟩ (denote cache_62), placeRow ⟨147, 6, 1, 3⟩ (denote cache_147), placeRow ⟨413, 0, 4, 2⟩ (denote cache_413)] = denote cache_418
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_418

theorem verified_row_419 : fork [place ⟨243, 0, 4, 2⟩ cache_243, place ⟨164, 1, 4, 2⟩ cache_164, place ⟨402, 0, 2, 4⟩ cache_402, place ⟨253, 0, 2, 4⟩ cache_253, place ⟨377, 0, 2, 4⟩ cache_377] = cache_419 := by
  decide +kernel

theorem load_entry_419 : entryAt 419 = entry_419 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_419 : CacheEquation 419 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(419 < 6)), load_entry_419]
  change forkRow [placeRow ⟨243, 0, 4, 2⟩ (denote cache_243), placeRow ⟨164, 1, 4, 2⟩ (denote cache_164), placeRow ⟨402, 0, 2, 4⟩ (denote cache_402), placeRow ⟨253, 0, 2, 4⟩ (denote cache_253), placeRow ⟨377, 0, 2, 4⟩ (denote cache_377)] = denote cache_419
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_419

theorem verified_row_420 : fork [place ⟨29, 3, 3, 0⟩ cache_29, place ⟨415, 0, 6, 4⟩ cache_415] = cache_420 := by
  decide +kernel

theorem load_entry_420 : entryAt 420 = entry_420 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_420 : CacheEquation 420 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(420 < 6)), load_entry_420]
  change forkRow [placeRow ⟨29, 3, 3, 0⟩ (denote cache_29), placeRow ⟨415, 0, 6, 4⟩ (denote cache_415)] = denote cache_420
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_420

theorem verified_row_421 : fork [place ⟨24, 6, 2, 3⟩ cache_24, place ⟨397, 1, 5, 3⟩ cache_397, place ⟨25, 6, 2, 3⟩ cache_25, place ⟨241, 4, 2, 4⟩ cache_241] = cache_421 := by
  decide +kernel

theorem load_entry_421 : entryAt 421 = entry_421 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_421 : CacheEquation 421 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(421 < 6)), load_entry_421]
  change forkRow [placeRow ⟨24, 6, 2, 3⟩ (denote cache_24), placeRow ⟨397, 1, 5, 3⟩ (denote cache_397), placeRow ⟨25, 6, 2, 3⟩ (denote cache_25), placeRow ⟨241, 4, 2, 4⟩ (denote cache_241)] = denote cache_421
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_421

theorem verified_row_422 : fork [place ⟨45, 1, 3, 7⟩ cache_45, place ⟨106, 6, 2, 3⟩ cache_106, place ⟨419, 1, 6, 6⟩ cache_419] = cache_422 := by
  decide +kernel

theorem load_entry_422 : entryAt 422 = entry_422 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_422 : CacheEquation 422 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(422 < 6)), load_entry_422]
  change forkRow [placeRow ⟨45, 1, 3, 7⟩ (denote cache_45), placeRow ⟨106, 6, 2, 3⟩ (denote cache_106), placeRow ⟨419, 1, 6, 6⟩ (denote cache_419)] = denote cache_422
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_422

theorem verified_row_423 : fork [place ⟨378, 4, 2, 4⟩ cache_378, place ⟨386, 0, 5, 4⟩ cache_386, place ⟨226, 3, 3, 5⟩ cache_226, place ⟨386, 4, 2, 4⟩ cache_386, place ⟨378, 0, 5, 4⟩ cache_378] = cache_423 := by
  decide +kernel

theorem load_entry_423 : entryAt 423 = entry_423 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_423 : CacheEquation 423 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(423 < 6)), load_entry_423]
  change forkRow [placeRow ⟨378, 4, 2, 4⟩ (denote cache_378), placeRow ⟨386, 0, 5, 4⟩ (denote cache_386), placeRow ⟨226, 3, 3, 5⟩ (denote cache_226), placeRow ⟨386, 4, 2, 4⟩ (denote cache_386), placeRow ⟨378, 0, 5, 4⟩ (denote cache_378)] = denote cache_423
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_423

theorem verified_row_424 : fork [place ⟨55, 1, 4, 5⟩ cache_55, place ⟨394, 0, 6, 4⟩ cache_394, place ⟨216, 3, 4, 5⟩ cache_216] = cache_424 := by
  decide +kernel

theorem load_entry_424 : entryAt 424 = entry_424 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_424 : CacheEquation 424 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(424 < 6)), load_entry_424]
  change forkRow [placeRow ⟨55, 1, 4, 5⟩ (denote cache_55), placeRow ⟨394, 0, 6, 4⟩ (denote cache_394), placeRow ⟨216, 3, 4, 5⟩ (denote cache_216)] = denote cache_424
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_424

theorem verified_row_425 : fork [place ⟨386, 0, 5, 4⟩ cache_386, place ⟨226, 1, 4, 5⟩ cache_226, place ⟨378, 4, 2, 4⟩ cache_378, place ⟨378, 0, 5, 4⟩ cache_378, place ⟨386, 4, 2, 4⟩ cache_386] = cache_425 := by
  decide +kernel

theorem load_entry_425 : entryAt 425 = entry_425 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_425 : CacheEquation 425 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(425 < 6)), load_entry_425]
  change forkRow [placeRow ⟨386, 0, 5, 4⟩ (denote cache_386), placeRow ⟨226, 1, 4, 5⟩ (denote cache_226), placeRow ⟨378, 4, 2, 4⟩ (denote cache_378), placeRow ⟨378, 0, 5, 4⟩ (denote cache_378), placeRow ⟨386, 4, 2, 4⟩ (denote cache_386)] = denote cache_425
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_425

theorem verified_row_426 : fork [place ⟨300, 6, 4, 1⟩ cache_300, place ⟨252, 1, 4, 5⟩ cache_252, place ⟨397, 0, 3, 4⟩ cache_397, place ⟨291, 1, 4, 1⟩ cache_291, place ⟨328, 0, 4, 5⟩ cache_328, place ⟨319, 1, 3, 5⟩ cache_319] = cache_426 := by
  decide +kernel

theorem load_entry_426 : entryAt 426 = entry_426 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_426 : CacheEquation 426 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(426 < 6)), load_entry_426]
  change forkRow [placeRow ⟨300, 6, 4, 1⟩ (denote cache_300), placeRow ⟨252, 1, 4, 5⟩ (denote cache_252), placeRow ⟨397, 0, 3, 4⟩ (denote cache_397), placeRow ⟨291, 1, 4, 1⟩ (denote cache_291), placeRow ⟨328, 0, 4, 5⟩ (denote cache_328), placeRow ⟨319, 1, 3, 5⟩ (denote cache_319)] = denote cache_426
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_426

theorem verified_row_427 : fork [place ⟨45, 1, 3, 7⟩ cache_45, place ⟨106, 6, 2, 3⟩ cache_106, place ⟨420, 1, 6, 4⟩ cache_420] = cache_427 := by
  decide +kernel

theorem load_entry_427 : entryAt 427 = entry_427 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_427 : CacheEquation 427 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(427 < 6)), load_entry_427]
  change forkRow [placeRow ⟨45, 1, 3, 7⟩ (denote cache_45), placeRow ⟨106, 6, 2, 3⟩ (denote cache_106), placeRow ⟨420, 1, 6, 4⟩ (denote cache_420)] = denote cache_427
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_427

theorem verified_row_428 : fork [place ⟨26, 3, 4, 3⟩ cache_26, place ⟨416, 0, 5, 4⟩ cache_416, place ⟨244, 0, 5, 4⟩ cache_244, place ⟨329, 0, 4, 3⟩ cache_329] = cache_428 := by
  decide +kernel

theorem load_entry_428 : entryAt 428 = entry_428 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_428 : CacheEquation 428 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(428 < 6)), load_entry_428]
  change forkRow [placeRow ⟨26, 3, 4, 3⟩ (denote cache_26), placeRow ⟨416, 0, 5, 4⟩ (denote cache_416), placeRow ⟨244, 0, 5, 4⟩ (denote cache_244), placeRow ⟨329, 0, 4, 3⟩ (denote cache_329)] = denote cache_428
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_428

theorem verified_row_429 : fork [place ⟨128, 0, 6, 3⟩ cache_128, place ⟨28, 3, 4, 5⟩ cache_28] = cache_429 := by
  decide +kernel

theorem load_entry_429 : entryAt 429 = entry_429 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_429 : CacheEquation 429 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(429 < 6)), load_entry_429]
  change forkRow [placeRow ⟨128, 0, 6, 3⟩ (denote cache_128), placeRow ⟨28, 3, 4, 5⟩ (denote cache_28)] = denote cache_429
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_429

theorem verified_row_430 : fork [place ⟨277, 7, 1, 3⟩ cache_277, place ⟨338, 4, 3, 4⟩ cache_338, place ⟨336, 1, 4, 3⟩ cache_336, place ⟨375, 2, 4, 3⟩ cache_375, place ⟨277, 6, 3, 1⟩ cache_277] = cache_430 := by
  decide +kernel

theorem load_entry_430 : entryAt 430 = entry_430 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_430 : CacheEquation 430 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(430 < 6)), load_entry_430]
  change forkRow [placeRow ⟨277, 7, 1, 3⟩ (denote cache_277), placeRow ⟨338, 4, 3, 4⟩ (denote cache_338), placeRow ⟨336, 1, 4, 3⟩ (denote cache_336), placeRow ⟨375, 2, 4, 3⟩ (denote cache_375), placeRow ⟨277, 6, 3, 1⟩ (denote cache_277)] = denote cache_430
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_430

theorem verified_row_431 : fork [place ⟨73, 4, 3, 3⟩ cache_73, place ⟨302, 1, 5, 2⟩ cache_302, place ⟨415, 0, 6, 4⟩ cache_415, place ⟨398, 0, 6, 4⟩ cache_398] = cache_431 := by
  decide +kernel

theorem load_entry_431 : entryAt 431 = entry_431 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_431 : CacheEquation 431 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(431 < 6)), load_entry_431]
  change forkRow [placeRow ⟨73, 4, 3, 3⟩ (denote cache_73), placeRow ⟨302, 1, 5, 2⟩ (denote cache_302), placeRow ⟨415, 0, 6, 4⟩ (denote cache_415), placeRow ⟨398, 0, 6, 4⟩ (denote cache_398)] = denote cache_431
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_431

theorem verified_row_432 : fork [place ⟨42, 3, 4, 3⟩ cache_42, place ⟨428, 0, 5, 4⟩ cache_428, place ⟨274, 0, 4, 3⟩ cache_274] = cache_432 := by
  decide +kernel

theorem load_entry_432 : entryAt 432 = entry_432 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_432 : CacheEquation 432 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(432 < 6)), load_entry_432]
  change forkRow [placeRow ⟨42, 3, 4, 3⟩ (denote cache_42), placeRow ⟨428, 0, 5, 4⟩ (denote cache_428), placeRow ⟨274, 0, 4, 3⟩ (denote cache_274)] = denote cache_432
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_432

theorem verified_row_433 : fork [place ⟨63, 0, 3, 5⟩ cache_63, place ⟨7, 3, 3, 4⟩ cache_7, place ⟨427, 0, 5, 2⟩ cache_427, place ⟨422, 0, 5, 2⟩ cache_422] = cache_433 := by
  decide +kernel

theorem load_entry_433 : entryAt 433 = entry_433 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_433 : CacheEquation 433 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(433 < 6)), load_entry_433]
  change forkRow [placeRow ⟨63, 0, 3, 5⟩ (denote cache_63), placeRow ⟨7, 3, 3, 4⟩ (denote cache_7), placeRow ⟨427, 0, 5, 2⟩ (denote cache_427), placeRow ⟨422, 0, 5, 2⟩ (denote cache_422)] = denote cache_433
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_433

theorem verified_row_434 : fork [place ⟨418, 0, 4, 5⟩ cache_418, place ⟨263, 2, 5, 4⟩ cache_263, place ⟨295, 0, 5, 4⟩ cache_295, place ⟨176, 2, 5, 4⟩ cache_176, place ⟨116, 0, 4, 3⟩ cache_116] = cache_434 := by
  decide +kernel

theorem load_entry_434 : entryAt 434 = entry_434 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_434 : CacheEquation 434 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(434 < 6)), load_entry_434]
  change forkRow [placeRow ⟨418, 0, 4, 5⟩ (denote cache_418), placeRow ⟨263, 2, 5, 4⟩ (denote cache_263), placeRow ⟨295, 0, 5, 4⟩ (denote cache_295), placeRow ⟨176, 2, 5, 4⟩ (denote cache_176), placeRow ⟨116, 0, 4, 3⟩ (denote cache_116)] = denote cache_434
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_434

theorem verified_row_435 : fork [place ⟨6, 4, 3, 4⟩ cache_6, place ⟨431, 0, 5, 6⟩ cache_431] = cache_435 := by
  decide +kernel

theorem load_entry_435 : entryAt 435 = entry_435 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_435 : CacheEquation 435 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(435 < 6)), load_entry_435]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (denote cache_6), placeRow ⟨431, 0, 5, 6⟩ (denote cache_431)] = denote cache_435
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_435

theorem verified_row_436 : fork [place ⟨51, 1, 5, 4⟩ cache_51, place ⟨60, 3, 4, 3⟩ cache_60, place ⟨274, 4, 4, 3⟩ cache_274, place ⟨428, 0, 5, 4⟩ cache_428] = cache_436 := by
  decide +kernel

theorem load_entry_436 : entryAt 436 = entry_436 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_436 : CacheEquation 436 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(436 < 6)), load_entry_436]
  change forkRow [placeRow ⟨51, 1, 5, 4⟩ (denote cache_51), placeRow ⟨60, 3, 4, 3⟩ (denote cache_60), placeRow ⟨274, 4, 4, 3⟩ (denote cache_274), placeRow ⟨428, 0, 5, 4⟩ (denote cache_428)] = denote cache_436
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_436

theorem verified_row_437 : fork [place ⟨55, 7, 4, 0⟩ cache_55, place ⟨427, 0, 5, 2⟩ cache_427, place ⟨63, 0, 3, 5⟩ cache_63, place ⟨422, 0, 5, 2⟩ cache_422] = cache_437 := by
  decide +kernel

theorem load_entry_437 : entryAt 437 = entry_437 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_437 : CacheEquation 437 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(437 < 6)), load_entry_437]
  change forkRow [placeRow ⟨55, 7, 4, 0⟩ (denote cache_55), placeRow ⟨427, 0, 5, 2⟩ (denote cache_427), placeRow ⟨63, 0, 3, 5⟩ (denote cache_63), placeRow ⟨422, 0, 5, 2⟩ (denote cache_422)] = denote cache_437
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_437

theorem verified_row_438 : fork [place ⟨0, 0, 1, 3⟩ cache_0, place ⟨432, 0, 4, 6⟩ cache_432] = cache_438 := by
  decide +kernel

theorem load_entry_438 : entryAt 438 = entry_438 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_438 : CacheEquation 438 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(438 < 6)), load_entry_438]
  change forkRow [placeRow ⟨0, 0, 1, 3⟩ (denote cache_0), placeRow ⟨432, 0, 4, 6⟩ (denote cache_432)] = denote cache_438
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_438

theorem verified_row_439 : fork [place ⟨176, 2, 5, 4⟩ cache_176, place ⟨295, 0, 5, 4⟩ cache_295, place ⟨263, 2, 5, 4⟩ cache_263, place ⟨418, 0, 4, 5⟩ cache_418, place ⟨149, 0, 4, 3⟩ cache_149] = cache_439 := by
  decide +kernel

theorem load_entry_439 : entryAt 439 = entry_439 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_439 : CacheEquation 439 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(439 < 6)), load_entry_439]
  change forkRow [placeRow ⟨176, 2, 5, 4⟩ (denote cache_176), placeRow ⟨295, 0, 5, 4⟩ (denote cache_295), placeRow ⟨263, 2, 5, 4⟩ (denote cache_263), placeRow ⟨418, 0, 4, 5⟩ (denote cache_418), placeRow ⟨149, 0, 4, 3⟩ (denote cache_149)] = denote cache_439
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_439

end SnakyCertificate.Check

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

theorem verified_row_440 : fork [place ⟨6, 6, 1, 3⟩ cache_6, place ⟨435, 0, 2, 5⟩ cache_435] = cache_440 := by
  decide +kernel

theorem load_entry_440 : entryAt 440 = entry_440 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_440 : CacheEquation 440 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(440 < 6)), load_entry_440]
  change forkRow [placeRow ⟨6, 6, 1, 3⟩ (denote cache_6), placeRow ⟨435, 0, 2, 5⟩ (denote cache_435)] = denote cache_440
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_440

theorem verified_row_441 : fork [place ⟨6, 6, 3, 4⟩ cache_6, place ⟨435, 0, 4, 6⟩ cache_435] = cache_441 := by
  decide +kernel

theorem load_entry_441 : entryAt 441 = entry_441 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_441 : CacheEquation 441 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(441 < 6)), load_entry_441]
  change forkRow [placeRow ⟨6, 6, 3, 4⟩ (denote cache_6), placeRow ⟨435, 0, 4, 6⟩ (denote cache_435)] = denote cache_441
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_441

theorem verified_row_442 : fork [place ⟨63, 0, 3, 5⟩ cache_63, place ⟨7, 1, 5, 4⟩ cache_7, place ⟨433, 0, 4, 5⟩ cache_433, place ⟨201, 0, 3, 2⟩ cache_201] = cache_442 := by
  decide +kernel

theorem load_entry_442 : entryAt 442 = entry_442 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_442 : CacheEquation 442 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(442 < 6)), load_entry_442]
  change forkRow [placeRow ⟨63, 0, 3, 5⟩ (denote cache_63), placeRow ⟨7, 1, 5, 4⟩ (denote cache_7), placeRow ⟨433, 0, 4, 5⟩ (denote cache_433), placeRow ⟨201, 0, 3, 2⟩ (denote cache_201)] = denote cache_442
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_442

theorem verified_row_443 : fork [place ⟨6, 0, 5, 4⟩ cache_6, place ⟨438, 0, 3, 4⟩ cache_438] = cache_443 := by
  decide +kernel

theorem load_entry_443 : entryAt 443 = entry_443 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_443 : CacheEquation 443 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(443 < 6)), load_entry_443]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (denote cache_6), placeRow ⟨438, 0, 3, 4⟩ (denote cache_438)] = denote cache_443
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_443

theorem verified_row_444 : fork [place ⟨194, 0, 5, 3⟩ cache_194, place ⟨160, 3, 4, 1⟩ cache_160, place ⟨142, 7, 4, 1⟩ cache_142, place ⟨236, 0, 5, 5⟩ cache_236, place ⟨353, 4, 1, 2⟩ cache_353, place ⟨412, 0, 5, 3⟩ cache_412] = cache_444 := by
  decide +kernel

theorem load_entry_444 : entryAt 444 = entry_444 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_444 : CacheEquation 444 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(444 < 6)), load_entry_444]
  change forkRow [placeRow ⟨194, 0, 5, 3⟩ (denote cache_194), placeRow ⟨160, 3, 4, 1⟩ (denote cache_160), placeRow ⟨142, 7, 4, 1⟩ (denote cache_142), placeRow ⟨236, 0, 5, 5⟩ (denote cache_236), placeRow ⟨353, 4, 1, 2⟩ (denote cache_353), placeRow ⟨412, 0, 5, 3⟩ (denote cache_412)] = denote cache_444
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_444

theorem verified_row_445 : fork [place ⟨9, 4, 3, 4⟩ cache_9, place ⟨432, 0, 5, 7⟩ cache_432] = cache_445 := by
  decide +kernel

theorem load_entry_445 : entryAt 445 = entry_445 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_445 : CacheEquation 445 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(445 < 6)), load_entry_445]
  change forkRow [placeRow ⟨9, 4, 3, 4⟩ (denote cache_9), placeRow ⟨432, 0, 5, 7⟩ (denote cache_432)] = denote cache_445
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_445

theorem verified_row_446 : fork [place ⟨4, 6, 4, 3⟩ cache_4, place ⟨438, 0, 6, 5⟩ cache_438] = cache_446 := by
  decide +kernel

theorem load_entry_446 : entryAt 446 = entry_446 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_446 : CacheEquation 446 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(446 < 6)), load_entry_446]
  change forkRow [placeRow ⟨4, 6, 4, 3⟩ (denote cache_4), placeRow ⟨438, 0, 6, 5⟩ (denote cache_438)] = denote cache_446
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_446

theorem verified_row_447 : fork [place ⟨0, 0, 0, 3⟩ cache_0, place ⟨436, 4, 4, 6⟩ cache_436] = cache_447 := by
  decide +kernel

theorem load_entry_447 : entryAt 447 = entry_447 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_447 : CacheEquation 447 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(447 < 6)), load_entry_447]
  change forkRow [placeRow ⟨0, 0, 0, 3⟩ (denote cache_0), placeRow ⟨436, 4, 4, 6⟩ (denote cache_436)] = denote cache_447
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_447

theorem verified_row_448 : fork [place ⟨9, 4, 1, 3⟩ cache_9, place ⟨436, 0, 3, 6⟩ cache_436] = cache_448 := by
  decide +kernel

theorem load_entry_448 : entryAt 448 = entry_448 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_448 : CacheEquation 448 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(448 < 6)), load_entry_448]
  change forkRow [placeRow ⟨9, 4, 1, 3⟩ (denote cache_9), placeRow ⟨436, 0, 3, 6⟩ (denote cache_436)] = denote cache_448
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_448

theorem verified_row_449 : fork [place ⟨26, 3, 4, 3⟩ cache_26, place ⟨244, 0, 5, 4⟩ cache_244, place ⟨439, 0, 5, 4⟩ cache_439, place ⟨307, 0, 4, 3⟩ cache_307] = cache_449 := by
  decide +kernel

theorem load_entry_449 : entryAt 449 = entry_449 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_449 : CacheEquation 449 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(449 < 6)), load_entry_449]
  change forkRow [placeRow ⟨26, 3, 4, 3⟩ (denote cache_26), placeRow ⟨244, 0, 5, 4⟩ (denote cache_244), placeRow ⟨439, 0, 5, 4⟩ (denote cache_439), placeRow ⟨307, 0, 4, 3⟩ (denote cache_307)] = denote cache_449
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_449

theorem verified_row_450 : fork [place ⟨6, 1, 5, 5⟩ cache_6, place ⟨440, 0, 6, 4⟩ cache_440] = cache_450 := by
  decide +kernel

theorem load_entry_450 : entryAt 450 = entry_450 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_450 : CacheEquation 450 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(450 < 6)), load_entry_450]
  change forkRow [placeRow ⟨6, 1, 5, 5⟩ (denote cache_6), placeRow ⟨440, 0, 6, 4⟩ (denote cache_440)] = denote cache_450
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_450

theorem verified_row_451 : fork [place ⟨1, 5, 4, 3⟩ cache_1, place ⟨449, 0, 5, 4⟩ cache_449] = cache_451 := by
  decide +kernel

theorem load_entry_451 : entryAt 451 = entry_451 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_451 : CacheEquation 451 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(451 < 6)), load_entry_451]
  change forkRow [placeRow ⟨1, 5, 4, 3⟩ (denote cache_1), placeRow ⟨449, 0, 5, 4⟩ (denote cache_449)] = denote cache_451
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_451

theorem verified_row_452 : fork [place ⟨24, 1, 5, 7⟩ cache_24, place ⟨451, 0, 3, 8⟩ cache_451, place ⟨25, 3, 3, 7⟩ cache_25] = cache_452 := by
  decide +kernel

theorem load_entry_452 : entryAt 452 = entry_452 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_452 : CacheEquation 452 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(452 < 6)), load_entry_452]
  change forkRow [placeRow ⟨24, 1, 5, 7⟩ (denote cache_24), placeRow ⟨451, 0, 3, 8⟩ (denote cache_451), placeRow ⟨25, 3, 3, 7⟩ (denote cache_25)] = denote cache_452
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_452

theorem verified_row_453 : fork [place ⟨359, 0, 4, 3⟩ cache_359, place ⟨226, 7, 3, 1⟩ cache_226, place ⟨386, 4, 2, 4⟩ cache_386, place ⟨389, 1, 5, 4⟩ cache_389, place ⟨414, 4, 3, 3⟩ cache_414] = cache_453 := by
  decide +kernel

theorem load_entry_453 : entryAt 453 = entry_453 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_453 : CacheEquation 453 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(453 < 6)), load_entry_453]
  change forkRow [placeRow ⟨359, 0, 4, 3⟩ (denote cache_359), placeRow ⟨226, 7, 3, 1⟩ (denote cache_226), placeRow ⟨386, 4, 2, 4⟩ (denote cache_386), placeRow ⟨389, 1, 5, 4⟩ (denote cache_389), placeRow ⟨414, 4, 3, 3⟩ (denote cache_414)] = denote cache_453
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_453

theorem verified_row_454 : fork [place ⟨58, 0, 6, 3⟩ cache_58, place ⟨436, 0, 3, 6⟩ cache_436] = cache_454 := by
  decide +kernel

theorem load_entry_454 : entryAt 454 = entry_454 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_454 : CacheEquation 454 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(454 < 6)), load_entry_454]
  change forkRow [placeRow ⟨58, 0, 6, 3⟩ (denote cache_58), placeRow ⟨436, 0, 3, 6⟩ (denote cache_436)] = denote cache_454
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_454

theorem verified_row_455 : fork [place ⟨20, 2, 4, 5⟩ cache_20, place ⟨118, 3, 0, 5⟩ cache_118, place ⟨39, 2, 3, 4⟩ cache_39] = cache_455 := by
  decide +kernel

theorem load_entry_455 : entryAt 455 = entry_455 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_455 : CacheEquation 455 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(455 < 6)), load_entry_455]
  change forkRow [placeRow ⟨20, 2, 4, 5⟩ (denote cache_20), placeRow ⟨118, 3, 0, 5⟩ (denote cache_118), placeRow ⟨39, 2, 3, 4⟩ (denote cache_39)] = denote cache_455
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_455

theorem verified_row_456 : fork [place ⟨308, 4, 4, 3⟩ cache_308, place ⟨64, 2, 1, 5⟩ cache_64, place ⟨63, 1, 5, 3⟩ cache_63, place ⟨55, 0, 5, 4⟩ cache_55] = cache_456 := by
  decide +kernel

theorem load_entry_456 : entryAt 456 = entry_456 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_456 : CacheEquation 456 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(456 < 6)), load_entry_456]
  change forkRow [placeRow ⟨308, 4, 4, 3⟩ (denote cache_308), placeRow ⟨64, 2, 1, 5⟩ (denote cache_64), placeRow ⟨63, 1, 5, 3⟩ (denote cache_63), placeRow ⟨55, 0, 5, 4⟩ (denote cache_55)] = denote cache_456
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_456

theorem verified_row_457 : fork [place ⟨28, 7, 3, 2⟩ cache_28, place ⟨454, 0, 5, 4⟩ cache_454] = cache_457 := by
  decide +kernel

theorem load_entry_457 : entryAt 457 = entry_457 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_457 : CacheEquation 457 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(457 < 6)), load_entry_457]
  change forkRow [placeRow ⟨28, 7, 3, 2⟩ (denote cache_28), placeRow ⟨454, 0, 5, 4⟩ (denote cache_454)] = denote cache_457
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_457

theorem verified_row_458 : fork [place ⟨130, 1, 4, 2⟩ cache_130, place ⟨177, 1, 4, 2⟩ cache_177, place ⟨450, 0, 1, 4⟩ cache_450] = cache_458 := by
  decide +kernel

theorem load_entry_458 : entryAt 458 = entry_458 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_458 : CacheEquation 458 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(458 < 6)), load_entry_458]
  change forkRow [placeRow ⟨130, 1, 4, 2⟩ (denote cache_130), placeRow ⟨177, 1, 4, 2⟩ (denote cache_177), placeRow ⟨450, 0, 1, 4⟩ (denote cache_450)] = denote cache_458
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_458

theorem verified_row_459 : fork [place ⟨97, 2, 7, 3⟩ cache_97, place ⟨448, 0, 5, 4⟩ cache_448, place ⟨65, 2, 7, 3⟩ cache_65] = cache_459 := by
  decide +kernel

theorem load_entry_459 : entryAt 459 = entry_459 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_459 : CacheEquation 459 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(459 < 6)), load_entry_459]
  change forkRow [placeRow ⟨97, 2, 7, 3⟩ (denote cache_97), placeRow ⟨448, 0, 5, 4⟩ (denote cache_448), placeRow ⟨65, 2, 7, 3⟩ (denote cache_65)] = denote cache_459
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_459

theorem verified_row_460 : fork [place ⟨183, 6, 1, 4⟩ cache_183, place ⟨173, 2, 5, 4⟩ cache_173, place ⟨295, 0, 5, 4⟩ cache_295, place ⟨282, 4, 1, 4⟩ cache_282, place ⟨246, 2, 5, 4⟩ cache_246, place ⟨263, 2, 5, 4⟩ cache_263, place ⟨220, 2, 5, 4⟩ cache_220] = cache_460 := by
  decide +kernel

theorem load_entry_460 : entryAt 460 = entry_460 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_460 : CacheEquation 460 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(460 < 6)), load_entry_460]
  change forkRow [placeRow ⟨183, 6, 1, 4⟩ (denote cache_183), placeRow ⟨173, 2, 5, 4⟩ (denote cache_173), placeRow ⟨295, 0, 5, 4⟩ (denote cache_295), placeRow ⟨282, 4, 1, 4⟩ (denote cache_282), placeRow ⟨246, 2, 5, 4⟩ (denote cache_246), placeRow ⟨263, 2, 5, 4⟩ (denote cache_263), placeRow ⟨220, 2, 5, 4⟩ (denote cache_220)] = denote cache_460
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_460

theorem verified_row_461 : fork [place ⟨4, 1, 4, 3⟩ cache_4, place ⟨458, 0, 6, 4⟩ cache_458] = cache_461 := by
  decide +kernel

theorem load_entry_461 : entryAt 461 = entry_461 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_461 : CacheEquation 461 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(461 < 6)), load_entry_461]
  change forkRow [placeRow ⟨4, 1, 4, 3⟩ (denote cache_4), placeRow ⟨458, 0, 6, 4⟩ (denote cache_458)] = denote cache_461
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_461

theorem verified_row_462 : fork [place ⟨452, 0, 3, 2⟩ cache_452, place ⟨86, 0, 5, 4⟩ cache_86, place ⟨328, 1, 5, 4⟩ cache_328] = cache_462 := by
  decide +kernel

theorem load_entry_462 : entryAt 462 = entry_462 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_462 : CacheEquation 462 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(462 < 6)), load_entry_462]
  change forkRow [placeRow ⟨452, 0, 3, 2⟩ (denote cache_452), placeRow ⟨86, 0, 5, 4⟩ (denote cache_86), placeRow ⟨328, 1, 5, 4⟩ (denote cache_328)] = denote cache_462
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_462

theorem verified_row_463 : fork [place ⟨170, 0, 6, 3⟩ cache_170, place ⟨76, 1, 3, 2⟩ cache_76, place ⟨447, 0, 5, 4⟩ cache_447] = cache_463 := by
  decide +kernel

theorem load_entry_463 : entryAt 463 = entry_463 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_463 : CacheEquation 463 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(463 < 6)), load_entry_463]
  change forkRow [placeRow ⟨170, 0, 6, 3⟩ (denote cache_170), placeRow ⟨76, 1, 3, 2⟩ (denote cache_76), placeRow ⟨447, 0, 5, 4⟩ (denote cache_447)] = denote cache_463
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_463

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

theorem cache_equations_range_384 : ∀ i, 384 ≤ i → i < 400 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_384
  · exact cache_equation_385
  · exact cache_equation_386
  · exact cache_equation_387
  · exact cache_equation_388
  · exact cache_equation_389
  · exact cache_equation_390
  · exact cache_equation_391
  · exact cache_equation_392
  · exact cache_equation_393
  · exact cache_equation_394
  · exact cache_equation_395
  · exact cache_equation_396
  · exact cache_equation_397
  · exact cache_equation_398
  · exact cache_equation_399

theorem cache_equations_range_400 : ∀ i, 400 ≤ i → i < 416 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_400
  · exact cache_equation_401
  · exact cache_equation_402
  · exact cache_equation_403
  · exact cache_equation_404
  · exact cache_equation_405
  · exact cache_equation_406
  · exact cache_equation_407
  · exact cache_equation_408
  · exact cache_equation_409
  · exact cache_equation_410
  · exact cache_equation_411
  · exact cache_equation_412
  · exact cache_equation_413
  · exact cache_equation_414
  · exact cache_equation_415

theorem cache_equations_range_416 : ∀ i, 416 ≤ i → i < 432 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_416
  · exact cache_equation_417
  · exact cache_equation_418
  · exact cache_equation_419
  · exact cache_equation_420
  · exact cache_equation_421
  · exact cache_equation_422
  · exact cache_equation_423
  · exact cache_equation_424
  · exact cache_equation_425
  · exact cache_equation_426
  · exact cache_equation_427
  · exact cache_equation_428
  · exact cache_equation_429
  · exact cache_equation_430
  · exact cache_equation_431

theorem cache_equations_range_432 : ∀ i, 432 ≤ i → i < 448 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_432
  · exact cache_equation_433
  · exact cache_equation_434
  · exact cache_equation_435
  · exact cache_equation_436
  · exact cache_equation_437
  · exact cache_equation_438
  · exact cache_equation_439
  · exact cache_equation_440
  · exact cache_equation_441
  · exact cache_equation_442
  · exact cache_equation_443
  · exact cache_equation_444
  · exact cache_equation_445
  · exact cache_equation_446
  · exact cache_equation_447

theorem cache_equations_range_448 : ∀ i, 448 ≤ i → i < 464 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_448
  · exact cache_equation_449
  · exact cache_equation_450
  · exact cache_equation_451
  · exact cache_equation_452
  · exact cache_equation_453
  · exact cache_equation_454
  · exact cache_equation_455
  · exact cache_equation_456
  · exact cache_equation_457
  · exact cache_equation_458
  · exact cache_equation_459
  · exact cache_equation_460
  · exact cache_equation_461
  · exact cache_equation_462
  · exact cache_equation_463

theorem cache_equations_range_384_416 : ∀ i, 384 ≤ i → i < 416 → CacheEquation i :=
  merge_ranges cache_equations_range_384 cache_equations_range_400

theorem cache_equations_range_432_464 : ∀ i, 432 ≤ i → i < 464 → CacheEquation i :=
  merge_ranges cache_equations_range_432 cache_equations_range_448

theorem cache_equations_range_416_464 : ∀ i, 416 ≤ i → i < 464 → CacheEquation i :=
  merge_ranges cache_equations_range_416 cache_equations_range_432_464

theorem cache_equations_range_384_464_oai : ∀ i, 384 ≤ i → i < 464 → CacheEquation i :=
  merge_ranges cache_equations_range_384_416 cache_equations_range_416_464

end SnakyCertificate.Check

end OAI
end

theorem solution : type_of% @OAI.SnakyCertificate.Check.cache_equations_range_384_464_oai := @OAI.SnakyCertificate.Check.cache_equations_range_384_464_oai
