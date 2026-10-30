-- Prove2me | solution 1 for OAI.SnakyCertificate.Check.cache_equations_range_304_464
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T23:54:36.302575+00:00
-- url     : https://prove2.me/submissions/afde5428-f37d-4e79-839b-13d5779def21

import Mathlib
import Definitions.Def_SnakyCertificate
import Definitions.Def_OAIQ114S000
import Theorems.Thm_OAI_SnakyCertificate_Check_cache_equations_range_384_464

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
-- module Solutions.OAIQ114_SC.SnakyCertificate_Equations07
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

theorem verified_row_304 : fork [place ⟨55, 4, 3, 4⟩ cache_55, place ⟨202, 0, 8, 4⟩ cache_202, place ⟨131, 3, 3, 4⟩ cache_131] = cache_304 := by
  decide +kernel

theorem load_entry_304 : entryAt 304 = entry_304 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_304 : CacheEquation 304 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(304 < 6)), load_entry_304]
  change forkRow [placeRow ⟨55, 4, 3, 4⟩ (denote cache_55), placeRow ⟨202, 0, 8, 4⟩ (denote cache_202), placeRow ⟨131, 3, 3, 4⟩ (denote cache_131)] = denote cache_304
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_304

theorem verified_row_305 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨278, 0, 1, 4⟩ cache_278] = cache_305 := by
  decide +kernel

theorem load_entry_305 : entryAt 305 = entry_305 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_305 : CacheEquation 305 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(305 < 6)), load_entry_305]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨278, 0, 1, 4⟩ (denote cache_278)] = denote cache_305
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_305

theorem verified_row_306 : fork [place ⟨4, 1, 4, 3⟩ cache_4, place ⟨288, 0, 6, 4⟩ cache_288] = cache_306 := by
  decide +kernel

theorem load_entry_306 : entryAt 306 = entry_306 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_306 : CacheEquation 306 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(306 < 6)), load_entry_306]
  change forkRow [placeRow ⟨4, 1, 4, 3⟩ (denote cache_4), placeRow ⟨288, 0, 6, 4⟩ (denote cache_288)] = denote cache_306
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_306

theorem verified_row_307 : fork [place ⟨0, 7, 4, 6⟩ cache_0, place ⟨273, 0, 5, 5⟩ cache_273] = cache_307 := by
  decide +kernel

theorem load_entry_307 : entryAt 307 = entry_307 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_307 : CacheEquation 307 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(307 < 6)), load_entry_307]
  change forkRow [placeRow ⟨0, 7, 4, 6⟩ (denote cache_0), placeRow ⟨273, 0, 5, 5⟩ (denote cache_273)] = denote cache_307
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_307

theorem verified_row_308 : fork [place ⟨6, 6, 3, 4⟩ cache_6, place ⟨299, 0, 4, 6⟩ cache_299] = cache_308 := by
  decide +kernel

theorem load_entry_308 : entryAt 308 = entry_308 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_308 : CacheEquation 308 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(308 < 6)), load_entry_308]
  change forkRow [placeRow ⟨6, 6, 3, 4⟩ (denote cache_6), placeRow ⟨299, 0, 4, 6⟩ (denote cache_299)] = denote cache_308
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_308

theorem verified_row_309 : fork [place ⟨28, 6, 3, 4⟩ cache_28, place ⟨268, 1, 5, 7⟩ cache_268] = cache_309 := by
  decide +kernel

theorem load_entry_309 : entryAt 309 = entry_309 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_309 : CacheEquation 309 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(309 < 6)), load_entry_309]
  change forkRow [placeRow ⟨28, 6, 3, 4⟩ (denote cache_28), placeRow ⟨268, 1, 5, 7⟩ (denote cache_268)] = denote cache_309
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_309

theorem verified_row_310 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨281, 0, 5, 3⟩ cache_281] = cache_310 := by
  decide +kernel

theorem load_entry_310 : entryAt 310 = entry_310 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_310 : CacheEquation 310 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(310 < 6)), load_entry_310]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨281, 0, 5, 3⟩ (denote cache_281)] = denote cache_310
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_310

theorem verified_row_311 : fork [place ⟨6, 3, 3, 5⟩ cache_6, place ⟨278, 0, 2, 4⟩ cache_278] = cache_311 := by
  decide +kernel

theorem load_entry_311 : entryAt 311 = entry_311 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_311 : CacheEquation 311 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(311 < 6)), load_entry_311]
  change forkRow [placeRow ⟨6, 3, 3, 5⟩ (denote cache_6), placeRow ⟨278, 0, 2, 4⟩ (denote cache_278)] = denote cache_311
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_311

theorem verified_row_312 : fork [place ⟨9, 2, 5, 4⟩ cache_9, place ⟨272, 0, 4, 5⟩ cache_272] = cache_312 := by
  decide +kernel

theorem load_entry_312 : entryAt 312 = entry_312 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_312 : CacheEquation 312 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(312 < 6)), load_entry_312]
  change forkRow [placeRow ⟨9, 2, 5, 4⟩ (denote cache_9), placeRow ⟨272, 0, 4, 5⟩ (denote cache_272)] = denote cache_312
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_312

theorem verified_row_313 : fork [place ⟨162, 4, 4, 5⟩ cache_162, place ⟨148, 5, 6, 3⟩ cache_148] = cache_313 := by
  decide +kernel

theorem load_entry_313 : entryAt 313 = entry_313 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_313 : CacheEquation 313 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(313 < 6)), load_entry_313]
  change forkRow [placeRow ⟨162, 4, 4, 5⟩ (denote cache_162), placeRow ⟨148, 5, 6, 3⟩ (denote cache_148)] = denote cache_313
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_313

theorem verified_row_314 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨305, 0, 6, 4⟩ cache_305] = cache_314 := by
  decide +kernel

theorem load_entry_314 : entryAt 314 = entry_314 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_314 : CacheEquation 314 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(314 < 6)), load_entry_314]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨305, 0, 6, 4⟩ (denote cache_305)] = denote cache_314
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_314

theorem verified_row_315 : fork [place ⟨6, 0, 5, 4⟩ cache_6, place ⟨296, 0, 4, 5⟩ cache_296] = cache_315 := by
  decide +kernel

theorem load_entry_315 : entryAt 315 = entry_315 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_315 : CacheEquation 315 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(315 < 6)), load_entry_315]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (denote cache_6), placeRow ⟨296, 0, 4, 5⟩ (denote cache_296)] = denote cache_315
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_315

theorem verified_row_316 : fork [place ⟨6, 6, 3, 4⟩ cache_6, place ⟨306, 0, 5, 8⟩ cache_306] = cache_316 := by
  decide +kernel

theorem load_entry_316 : entryAt 316 = entry_316 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_316 : CacheEquation 316 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(316 < 6)), load_entry_316]
  change forkRow [placeRow ⟨6, 6, 3, 4⟩ (denote cache_6), placeRow ⟨306, 0, 5, 8⟩ (denote cache_306)] = denote cache_316
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_316

theorem verified_row_317 : fork [place ⟨263, 2, 6, 4⟩ cache_263, place ⟨26, 3, 4, 3⟩ cache_26, place ⟨99, 0, 5, 5⟩ cache_99] = cache_317 := by
  decide +kernel

theorem load_entry_317 : entryAt 317 = entry_317 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_317 : CacheEquation 317 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(317 < 6)), load_entry_317]
  change forkRow [placeRow ⟨263, 2, 6, 4⟩ (denote cache_263), placeRow ⟨26, 3, 4, 3⟩ (denote cache_26), placeRow ⟨99, 0, 5, 5⟩ (denote cache_99)] = denote cache_317
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_317

theorem verified_row_318 : fork [place ⟨64, 3, 5, 1⟩ cache_64, place ⟨63, 0, 3, 5⟩ cache_63, place ⟨261, 0, 3, 4⟩ cache_261, place ⟨55, 1, 4, 5⟩ cache_55] = cache_318 := by
  decide +kernel

theorem load_entry_318 : entryAt 318 = entry_318 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_318 : CacheEquation 318 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(318 < 6)), load_entry_318]
  change forkRow [placeRow ⟨64, 3, 5, 1⟩ (denote cache_64), placeRow ⟨63, 0, 3, 5⟩ (denote cache_63), placeRow ⟨261, 0, 3, 4⟩ (denote cache_261), placeRow ⟨55, 1, 4, 5⟩ (denote cache_55)] = denote cache_318
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_318

theorem verified_row_319 : fork [place ⟨39, 2, 3, 4⟩ cache_39, place ⟨109, 4, 0, 5⟩ cache_109, place ⟨266, 1, 4, 5⟩ cache_266, place ⟨122, 4, 4, 5⟩ cache_122] = cache_319 := by
  decide +kernel

theorem load_entry_319 : entryAt 319 = entry_319 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_319 : CacheEquation 319 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(319 < 6)), load_entry_319]
  change forkRow [placeRow ⟨39, 2, 3, 4⟩ (denote cache_39), placeRow ⟨109, 4, 0, 5⟩ (denote cache_109), placeRow ⟨266, 1, 4, 5⟩ (denote cache_266), placeRow ⟨122, 4, 4, 5⟩ (denote cache_122)] = denote cache_319
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_319

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_Equations08
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

theorem verified_row_320 : fork [place ⟨19, 1, 4, 3⟩ cache_19, place ⟨267, 2, 6, 4⟩ cache_267, place ⟨115, 7, 4, 3⟩ cache_115] = cache_320 := by
  decide +kernel

theorem load_entry_320 : entryAt 320 = entry_320 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_320 : CacheEquation 320 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(320 < 6)), load_entry_320]
  change forkRow [placeRow ⟨19, 1, 4, 3⟩ (denote cache_19), placeRow ⟨267, 2, 6, 4⟩ (denote cache_267), placeRow ⟨115, 7, 4, 3⟩ (denote cache_115)] = denote cache_320
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_320

theorem verified_row_321 : fork [place ⟨165, 1, 3, 4⟩ cache_165, place ⟨97, 0, 7, 5⟩ cache_97, place ⟨223, 3, 4, 7⟩ cache_223] = cache_321 := by
  decide +kernel

theorem load_entry_321 : entryAt 321 = entry_321 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_321 : CacheEquation 321 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(321 < 6)), load_entry_321]
  change forkRow [placeRow ⟨165, 1, 3, 4⟩ (denote cache_165), placeRow ⟨97, 0, 7, 5⟩ (denote cache_97), placeRow ⟨223, 3, 4, 7⟩ (denote cache_223)] = denote cache_321
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_321

theorem verified_row_322 : fork [place ⟨96, 0, 1, 4⟩ cache_96, place ⟨205, 1, 5, 2⟩ cache_205] = cache_322 := by
  decide +kernel

theorem load_entry_322 : entryAt 322 = entry_322 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_322 : CacheEquation 322 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(322 < 6)), load_entry_322]
  change forkRow [placeRow ⟨96, 0, 1, 4⟩ (denote cache_96), placeRow ⟨205, 1, 5, 2⟩ (denote cache_205)] = denote cache_322
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_322

theorem verified_row_323 : fork [place ⟨165, 6, 4, 5⟩ cache_165, place ⟨278, 0, 1, 4⟩ cache_278, place ⟨25, 1, 4, 5⟩ cache_25] = cache_323 := by
  decide +kernel

theorem load_entry_323 : entryAt 323 = entry_323 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_323 : CacheEquation 323 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(323 < 6)), load_entry_323]
  change forkRow [placeRow ⟨165, 6, 4, 5⟩ (denote cache_165), placeRow ⟨278, 0, 1, 4⟩ (denote cache_278), placeRow ⟨25, 1, 4, 5⟩ (denote cache_25)] = denote cache_323
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_323

theorem verified_row_324 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨298, 0, 3, 4⟩ cache_298] = cache_324 := by
  decide +kernel

theorem load_entry_324 : entryAt 324 = entry_324 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_324 : CacheEquation 324 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(324 < 6)), load_entry_324]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨298, 0, 3, 4⟩ (denote cache_298)] = denote cache_324
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_324

theorem verified_row_325 : fork [place ⟨25, 0, 6, 5⟩ cache_25, place ⟨313, 1, 6, 4⟩ cache_313, place ⟨24, 2, 6, 3⟩ cache_24] = cache_325 := by
  decide +kernel

theorem load_entry_325 : entryAt 325 = entry_325 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_325 : CacheEquation 325 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(325 < 6)), load_entry_325]
  change forkRow [placeRow ⟨25, 0, 6, 5⟩ (denote cache_25), placeRow ⟨313, 1, 6, 4⟩ (denote cache_313), placeRow ⟨24, 2, 6, 3⟩ (denote cache_24)] = denote cache_325
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_325

theorem verified_row_326 : fork [place ⟨63, 1, 5, 3⟩ cache_63, place ⟨255, 7, 0, 4⟩ cache_255] = cache_326 := by
  decide +kernel

theorem load_entry_326 : entryAt 326 = entry_326 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_326 : CacheEquation 326 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(326 < 6)), load_entry_326]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (denote cache_63), placeRow ⟨255, 7, 0, 4⟩ (denote cache_255)] = denote cache_326
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_326

theorem verified_row_327 : fork [place ⟨24, 2, 6, 3⟩ cache_24, place ⟨195, 4, 2, 4⟩ cache_195, place ⟨195, 0, 6, 4⟩ cache_195, place ⟨24, 6, 2, 3⟩ cache_24] = cache_327 := by
  decide +kernel

theorem load_entry_327 : entryAt 327 = entry_327 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_327 : CacheEquation 327 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(327 < 6)), load_entry_327]
  change forkRow [placeRow ⟨24, 2, 6, 3⟩ (denote cache_24), placeRow ⟨195, 4, 2, 4⟩ (denote cache_195), placeRow ⟨195, 0, 6, 4⟩ (denote cache_195), placeRow ⟨24, 6, 2, 3⟩ (denote cache_24)] = denote cache_327
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_327

theorem verified_row_328 : fork [place ⟨49, 0, 4, 5⟩ cache_49, place ⟨44, 3, 4, 5⟩ cache_44, place ⟨285, 0, 3, 4⟩ cache_285] = cache_328 := by
  decide +kernel

theorem load_entry_328 : entryAt 328 = entry_328 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_328 : CacheEquation 328 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(328 < 6)), load_entry_328]
  change forkRow [placeRow ⟨49, 0, 4, 5⟩ (denote cache_49), placeRow ⟨44, 3, 4, 5⟩ (denote cache_44), placeRow ⟨285, 0, 3, 4⟩ (denote cache_285)] = denote cache_328
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_328

theorem verified_row_329 : fork [place ⟨0, 7, 4, 6⟩ cache_0, place ⟨305, 0, 5, 5⟩ cache_305] = cache_329 := by
  decide +kernel

theorem load_entry_329 : entryAt 329 = entry_329 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_329 : CacheEquation 329 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(329 < 6)), load_entry_329]
  change forkRow [placeRow ⟨0, 7, 4, 6⟩ (denote cache_0), placeRow ⟨305, 0, 5, 5⟩ (denote cache_305)] = denote cache_329
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_329

theorem verified_row_330 : fork [place ⟨63, 1, 5, 3⟩ cache_63, place ⟨268, 0, 4, 5⟩ cache_268, place ⟨144, 0, 5, 4⟩ cache_144, place ⟨154, 4, 5, 4⟩ cache_154, place ⟨155, 5, 5, 4⟩ cache_155] = cache_330 := by
  decide +kernel

theorem load_entry_330 : entryAt 330 = entry_330 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_330 : CacheEquation 330 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(330 < 6)), load_entry_330]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (denote cache_63), placeRow ⟨268, 0, 4, 5⟩ (denote cache_268), placeRow ⟨144, 0, 5, 4⟩ (denote cache_144), placeRow ⟨154, 4, 5, 4⟩ (denote cache_154), placeRow ⟨155, 5, 5, 4⟩ (denote cache_155)] = denote cache_330
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_330

theorem verified_row_331 : fork [place ⟨113, 0, 1, 4⟩ cache_113, place ⟨15, 0, 3, 4⟩ cache_15, place ⟨298, 4, 4, 5⟩ cache_298, place ⟨90, 2, 5, 4⟩ cache_90] = cache_331 := by
  decide +kernel

theorem load_entry_331 : entryAt 331 = entry_331 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_331 : CacheEquation 331 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(331 < 6)), load_entry_331]
  change forkRow [placeRow ⟨113, 0, 1, 4⟩ (denote cache_113), placeRow ⟨15, 0, 3, 4⟩ (denote cache_15), placeRow ⟨298, 4, 4, 5⟩ (denote cache_298), placeRow ⟨90, 2, 5, 4⟩ (denote cache_90)] = denote cache_331
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_331

theorem verified_row_332 : fork [place ⟨67, 4, 3, 4⟩ cache_67, place ⟨289, 2, 5, 1⟩ cache_289] = cache_332 := by
  decide +kernel

theorem load_entry_332 : entryAt 332 = entry_332 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_332 : CacheEquation 332 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(332 < 6)), load_entry_332]
  change forkRow [placeRow ⟨67, 4, 3, 4⟩ (denote cache_67), placeRow ⟨289, 2, 5, 1⟩ (denote cache_289)] = denote cache_332
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_332

theorem verified_row_333 : fork [place ⟨317, 0, 5, 4⟩ cache_317, place ⟨1, 5, 4, 3⟩ cache_1] = cache_333 := by
  decide +kernel

theorem load_entry_333 : entryAt 333 = entry_333 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_333 : CacheEquation 333 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(333 < 6)), load_entry_333]
  change forkRow [placeRow ⟨317, 0, 5, 4⟩ (denote cache_317), placeRow ⟨1, 5, 4, 3⟩ (denote cache_1)] = denote cache_333
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_333

theorem verified_row_334 : fork [place ⟨67, 6, 3, 2⟩ cache_67, place ⟨289, 0, 5, 5⟩ cache_289] = cache_334 := by
  decide +kernel

theorem load_entry_334 : entryAt 334 = entry_334 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_334 : CacheEquation 334 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(334 < 6)), load_entry_334]
  change forkRow [placeRow ⟨67, 6, 3, 2⟩ (denote cache_67), placeRow ⟨289, 0, 5, 5⟩ (denote cache_289)] = denote cache_334
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_334

theorem verified_row_335 : fork [place ⟨196, 3, 1, 3⟩ cache_196, place ⟨162, 1, 5, 4⟩ cache_162] = cache_335 := by
  decide +kernel

theorem load_entry_335 : entryAt 335 = entry_335 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_335 : CacheEquation 335 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(335 < 6)), load_entry_335]
  change forkRow [placeRow ⟨196, 3, 1, 3⟩ (denote cache_196), placeRow ⟨162, 1, 5, 4⟩ (denote cache_162)] = denote cache_335
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_335

theorem verified_row_336 : fork [place ⟨25, 6, 2, 3⟩ cache_25, place ⟨199, 3, 2, 4⟩ cache_199, place ⟨65, 0, 6, 4⟩ cache_65, place ⟨304, 0, 2, 4⟩ cache_304] = cache_336 := by
  decide +kernel

theorem load_entry_336 : entryAt 336 = entry_336 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_336 : CacheEquation 336 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(336 < 6)), load_entry_336]
  change forkRow [placeRow ⟨25, 6, 2, 3⟩ (denote cache_25), placeRow ⟨199, 3, 2, 4⟩ (denote cache_199), placeRow ⟨65, 0, 6, 4⟩ (denote cache_65), placeRow ⟨304, 0, 2, 4⟩ (denote cache_304)] = denote cache_336
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_336

theorem verified_row_337 : fork [place ⟨107, 3, 3, 7⟩ cache_107, place ⟨230, 2, 1, 5⟩ cache_230] = cache_337 := by
  decide +kernel

theorem load_entry_337 : entryAt 337 = entry_337 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_337 : CacheEquation 337 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(337 < 6)), load_entry_337]
  change forkRow [placeRow ⟨107, 3, 3, 7⟩ (denote cache_107), placeRow ⟨230, 2, 1, 5⟩ (denote cache_230)] = denote cache_337
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_337

theorem verified_row_338 : fork [place ⟨241, 0, 6, 4⟩ cache_241, place ⟨275, 4, 2, 4⟩ cache_275, place ⟨107, 4, 2, 4⟩ cache_107] = cache_338 := by
  decide +kernel

theorem load_entry_338 : entryAt 338 = entry_338 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_338 : CacheEquation 338 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(338 < 6)), load_entry_338]
  change forkRow [placeRow ⟨241, 0, 6, 4⟩ (denote cache_241), placeRow ⟨275, 4, 2, 4⟩ (denote cache_275), placeRow ⟨107, 4, 2, 4⟩ (denote cache_107)] = denote cache_338
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_338

theorem verified_row_339 : fork [place ⟨4, 1, 4, 3⟩ cache_4, place ⟨322, 0, 6, 4⟩ cache_322] = cache_339 := by
  decide +kernel

theorem load_entry_339 : entryAt 339 = entry_339 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_339 : CacheEquation 339 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(339 < 6)), load_entry_339]
  change forkRow [placeRow ⟨4, 1, 4, 3⟩ (denote cache_4), placeRow ⟨322, 0, 6, 4⟩ (denote cache_322)] = denote cache_339
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_339

theorem verified_row_340 : fork [place ⟨25, 3, 3, 6⟩ cache_25, place ⟨300, 4, 4, 6⟩ cache_300, place ⟨24, 3, 3, 6⟩ cache_24] = cache_340 := by
  decide +kernel

theorem load_entry_340 : entryAt 340 = entry_340 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_340 : CacheEquation 340 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(340 < 6)), load_entry_340]
  change forkRow [placeRow ⟨25, 3, 3, 6⟩ (denote cache_25), placeRow ⟨300, 4, 4, 6⟩ (denote cache_300), placeRow ⟨24, 3, 3, 6⟩ (denote cache_24)] = denote cache_340
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_340

theorem verified_row_341 : fork [place ⟨162, 5, 5, 4⟩ cache_162, place ⟨259, 4, 4, 5⟩ cache_259, place ⟨208, 2, 5, 4⟩ cache_208, place ⟨143, 0, 1, 3⟩ cache_143] = cache_341 := by
  decide +kernel

theorem load_entry_341 : entryAt 341 = entry_341 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_341 : CacheEquation 341 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(341 < 6)), load_entry_341]
  change forkRow [placeRow ⟨162, 5, 5, 4⟩ (denote cache_162), placeRow ⟨259, 4, 4, 5⟩ (denote cache_259), placeRow ⟨208, 2, 5, 4⟩ (denote cache_208), placeRow ⟨143, 0, 1, 3⟩ (denote cache_143)] = denote cache_341
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_341

theorem verified_row_342 : fork [place ⟨210, 0, 5, 2⟩ cache_210, place ⟨88, 1, 4, 3⟩ cache_88, place ⟨260, 4, 4, 3⟩ cache_260, place ⟨290, 0, 4, 3⟩ cache_290] = cache_342 := by
  decide +kernel

theorem load_entry_342 : entryAt 342 = entry_342 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_342 : CacheEquation 342 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(342 < 6)), load_entry_342]
  change forkRow [placeRow ⟨210, 0, 5, 2⟩ (denote cache_210), placeRow ⟨88, 1, 4, 3⟩ (denote cache_88), placeRow ⟨260, 4, 4, 3⟩ (denote cache_260), placeRow ⟨290, 0, 4, 3⟩ (denote cache_290)] = denote cache_342
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_342

theorem verified_row_343 : fork [place ⟨0, 5, 4, 5⟩ cache_0, place ⟨250, 0, 5, 4⟩ cache_250] = cache_343 := by
  decide +kernel

theorem load_entry_343 : entryAt 343 = entry_343 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_343 : CacheEquation 343 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(343 < 6)), load_entry_343]
  change forkRow [placeRow ⟨0, 5, 4, 5⟩ (denote cache_0), placeRow ⟨250, 0, 5, 4⟩ (denote cache_250)] = denote cache_343
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_343

theorem verified_row_344 : fork [place ⟨7, 1, 5, 4⟩ cache_7, place ⟨108, 3, 4, 5⟩ cache_108, place ⟨262, 4, 5, 2⟩ cache_262] = cache_344 := by
  decide +kernel

theorem load_entry_344 : entryAt 344 = entry_344 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_344 : CacheEquation 344 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(344 < 6)), load_entry_344]
  change forkRow [placeRow ⟨7, 1, 5, 4⟩ (denote cache_7), placeRow ⟨108, 3, 4, 5⟩ (denote cache_108), placeRow ⟨262, 4, 5, 2⟩ (denote cache_262)] = denote cache_344
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_344

theorem verified_row_345 : fork [place ⟨6, 0, 5, 5⟩ cache_6, place ⟨320, 4, 4, 7⟩ cache_320] = cache_345 := by
  decide +kernel

theorem load_entry_345 : entryAt 345 = entry_345 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_345 : CacheEquation 345 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(345 < 6)), load_entry_345]
  change forkRow [placeRow ⟨6, 0, 5, 5⟩ (denote cache_6), placeRow ⟨320, 4, 4, 7⟩ (denote cache_320)] = denote cache_345
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_345

theorem verified_row_346 : fork [place ⟨60, 1, 4, 3⟩ cache_60, place ⟨255, 0, 1, 4⟩ cache_255, place ⟨276, 0, 1, 4⟩ cache_276] = cache_346 := by
  decide +kernel

theorem load_entry_346 : entryAt 346 = entry_346 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_346 : CacheEquation 346 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(346 < 6)), load_entry_346]
  change forkRow [placeRow ⟨60, 1, 4, 3⟩ (denote cache_60), placeRow ⟨255, 0, 1, 4⟩ (denote cache_255), placeRow ⟨276, 0, 1, 4⟩ (denote cache_276)] = denote cache_346
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_346

theorem verified_row_347 : fork [place ⟨6, 6, 3, 4⟩ cache_6, place ⟨339, 0, 5, 8⟩ cache_339] = cache_347 := by
  decide +kernel

theorem load_entry_347 : entryAt 347 = entry_347 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_347 : CacheEquation 347 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(347 < 6)), load_entry_347]
  change forkRow [placeRow ⟨6, 6, 3, 4⟩ (denote cache_6), placeRow ⟨339, 0, 5, 8⟩ (denote cache_339)] = denote cache_347
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_347

theorem verified_row_348 : fork [place ⟨312, 1, 5, 5⟩ cache_312, place ⟨114, 4, 3, 4⟩ cache_114, place ⟨139, 3, 4, 5⟩ cache_139] = cache_348 := by
  decide +kernel

theorem load_entry_348 : entryAt 348 = entry_348 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_348 : CacheEquation 348 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(348 < 6)), load_entry_348]
  change forkRow [placeRow ⟨312, 1, 5, 5⟩ (denote cache_312), placeRow ⟨114, 4, 3, 4⟩ (denote cache_114), placeRow ⟨139, 3, 4, 5⟩ (denote cache_139)] = denote cache_348
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_348

theorem verified_row_349 : fork [place ⟨14, 1, 4, 5⟩ cache_14, place ⟨17, 1, 4, 5⟩ cache_17, place ⟨332, 0, 3, 4⟩ cache_332] = cache_349 := by
  decide +kernel

theorem load_entry_349 : entryAt 349 = entry_349 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_349 : CacheEquation 349 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(349 < 6)), load_entry_349]
  change forkRow [placeRow ⟨14, 1, 4, 5⟩ (denote cache_14), placeRow ⟨17, 1, 4, 5⟩ (denote cache_17), placeRow ⟨332, 0, 3, 4⟩ (denote cache_332)] = denote cache_349
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_349

theorem verified_row_350 : fork [place ⟨24, 4, 2, 5⟩ cache_24, place ⟨107, 2, 6, 4⟩ cache_107, place ⟨271, 4, 5, 5⟩ cache_271, place ⟨215, 0, 5, 5⟩ cache_215] = cache_350 := by
  decide +kernel

theorem load_entry_350 : entryAt 350 = entry_350 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_350 : CacheEquation 350 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(350 < 6)), load_entry_350]
  change forkRow [placeRow ⟨24, 4, 2, 5⟩ (denote cache_24), placeRow ⟨107, 2, 6, 4⟩ (denote cache_107), placeRow ⟨271, 4, 5, 5⟩ (denote cache_271), placeRow ⟨215, 0, 5, 5⟩ (denote cache_215)] = denote cache_350
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_350

theorem verified_row_351 : fork [place ⟨163, 0, 5, 4⟩ cache_163, place ⟨287, 4, 1, 4⟩ cache_287, place ⟨25, 4, 1, 5⟩ cache_25] = cache_351 := by
  decide +kernel

theorem load_entry_351 : entryAt 351 = entry_351 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_351 : CacheEquation 351 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(351 < 6)), load_entry_351]
  change forkRow [placeRow ⟨163, 0, 5, 4⟩ (denote cache_163), placeRow ⟨287, 4, 1, 4⟩ (denote cache_287), placeRow ⟨25, 4, 1, 5⟩ (denote cache_25)] = denote cache_351
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_351

theorem verified_row_352 : fork [place ⟨214, 0, 4, 5⟩ cache_214, place ⟨91, 0, 3, 4⟩ cache_91, place ⟨63, 0, 3, 5⟩ cache_63, place ⟨344, 0, 4, 5⟩ cache_344, place ⟨180, 4, 4, 5⟩ cache_180] = cache_352 := by
  decide +kernel

theorem load_entry_352 : entryAt 352 = entry_352 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_352 : CacheEquation 352 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(352 < 6)), load_entry_352]
  change forkRow [placeRow ⟨214, 0, 4, 5⟩ (denote cache_214), placeRow ⟨91, 0, 3, 4⟩ (denote cache_91), placeRow ⟨63, 0, 3, 5⟩ (denote cache_63), placeRow ⟨344, 0, 4, 5⟩ (denote cache_344), placeRow ⟨180, 4, 4, 5⟩ (denote cache_180)] = denote cache_352
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_352

theorem verified_row_353 : fork [place ⟨6, 4, 0, 5⟩ cache_6, place ⟨347, 0, 1, 3⟩ cache_347] = cache_353 := by
  decide +kernel

theorem load_entry_353 : entryAt 353 = entry_353 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_353 : CacheEquation 353 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(353 < 6)), load_entry_353]
  change forkRow [placeRow ⟨6, 4, 0, 5⟩ (denote cache_6), placeRow ⟨347, 0, 1, 3⟩ (denote cache_347)] = denote cache_353
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_353

theorem verified_row_354 : fork [place ⟨138, 2, 5, 4⟩ cache_138, place ⟨114, 5, 4, 3⟩ cache_114, place ⟨312, 0, 5, 5⟩ cache_312, place ⟨182, 2, 2, 4⟩ cache_182] = cache_354 := by
  decide +kernel

theorem load_entry_354 : entryAt 354 = entry_354 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_354 : CacheEquation 354 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(354 < 6)), load_entry_354]
  change forkRow [placeRow ⟨138, 2, 5, 4⟩ (denote cache_138), placeRow ⟨114, 5, 4, 3⟩ (denote cache_114), placeRow ⟨312, 0, 5, 5⟩ (denote cache_312), placeRow ⟨182, 2, 2, 4⟩ (denote cache_182)] = denote cache_354
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_354

theorem verified_row_355 : fork [place ⟨12, 2, 7, 3⟩ cache_12, place ⟨167, 0, 7, 4⟩ cache_167, place ⟨342, 0, 6, 6⟩ cache_342] = cache_355 := by
  decide +kernel

theorem load_entry_355 : entryAt 355 = entry_355 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_355 : CacheEquation 355 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(355 < 6)), load_entry_355]
  change forkRow [placeRow ⟨12, 2, 7, 3⟩ (denote cache_12), placeRow ⟨167, 0, 7, 4⟩ (denote cache_167), placeRow ⟨342, 0, 6, 6⟩ (denote cache_342)] = denote cache_355
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_355

theorem verified_row_356 : fork [place ⟨24, 2, 6, 3⟩ cache_24, place ⟨24, 6, 2, 3⟩ cache_24, place ⟨211, 4, 2, 4⟩ cache_211, place ⟨179, 0, 6, 4⟩ cache_179] = cache_356 := by
  decide +kernel

theorem load_entry_356 : entryAt 356 = entry_356 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_356 : CacheEquation 356 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(356 < 6)), load_entry_356]
  change forkRow [placeRow ⟨24, 2, 6, 3⟩ (denote cache_24), placeRow ⟨24, 6, 2, 3⟩ (denote cache_24), placeRow ⟨211, 4, 2, 4⟩ (denote cache_211), placeRow ⟨179, 0, 6, 4⟩ (denote cache_179)] = denote cache_356
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_356

theorem verified_row_357 : fork [place ⟨82, 6, 2, 3⟩ cache_82, place ⟨283, 0, 5, 6⟩ cache_283] = cache_357 := by
  decide +kernel

theorem load_entry_357 : entryAt 357 = entry_357 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_357 : CacheEquation 357 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(357 < 6)), load_entry_357]
  change forkRow [placeRow ⟨82, 6, 2, 3⟩ (denote cache_82), placeRow ⟨283, 0, 5, 6⟩ (denote cache_283)] = denote cache_357
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_357

theorem verified_row_358 : fork [place ⟨6, 0, 5, 4⟩ cache_6, place ⟨346, 0, 4, 6⟩ cache_346] = cache_358 := by
  decide +kernel

theorem load_entry_358 : entryAt 358 = entry_358 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_358 : CacheEquation 358 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(358 < 6)), load_entry_358]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (denote cache_6), placeRow ⟨346, 0, 4, 6⟩ (denote cache_346)] = denote cache_358
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_358

theorem verified_row_359 : fork [place ⟨134, 0, 4, 6⟩ cache_134, place ⟨24, 7, 3, 2⟩ cache_24, place ⟨323, 0, 5, 5⟩ cache_323] = cache_359 := by
  decide +kernel

theorem load_entry_359 : entryAt 359 = entry_359 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_359 : CacheEquation 359 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(359 < 6)), load_entry_359]
  change forkRow [placeRow ⟨134, 0, 4, 6⟩ (denote cache_134), placeRow ⟨24, 7, 3, 2⟩ (denote cache_24), placeRow ⟨323, 0, 5, 5⟩ (denote cache_323)] = denote cache_359
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_359

end SnakyCertificate.Check

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

theorem verified_row_360 : fork [place ⟨155, 4, 4, 5⟩ cache_155, place ⟨7, 3, 3, 4⟩ cache_7, place ⟨337, 0, 5, 2⟩ cache_337, place ⟨228, 4, 5, 2⟩ cache_228] = cache_360 := by
  decide +kernel

theorem load_entry_360 : entryAt 360 = entry_360 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_360 : CacheEquation 360 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(360 < 6)), load_entry_360]
  change forkRow [placeRow ⟨155, 4, 4, 5⟩ (denote cache_155), placeRow ⟨7, 3, 3, 4⟩ (denote cache_7), placeRow ⟨337, 0, 5, 2⟩ (denote cache_337), placeRow ⟨228, 4, 5, 2⟩ (denote cache_228)] = denote cache_360
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_360

theorem verified_row_361 : fork [place ⟨6, 4, 3, 4⟩ cache_6, place ⟨352, 0, 4, 5⟩ cache_352] = cache_361 := by
  decide +kernel

theorem load_entry_361 : entryAt 361 = entry_361 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_361 : CacheEquation 361 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(361 < 6)), load_entry_361]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (denote cache_6), placeRow ⟨352, 0, 4, 5⟩ (denote cache_352)] = denote cache_361
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_361

theorem verified_row_362 : fork [place ⟨4, 0, 3, 4⟩ cache_4, place ⟨345, 0, 4, 3⟩ cache_345] = cache_362 := by
  decide +kernel

theorem load_entry_362 : entryAt 362 = entry_362 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_362 : CacheEquation 362 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(362 < 6)), load_entry_362]
  change forkRow [placeRow ⟨4, 0, 3, 4⟩ (denote cache_4), placeRow ⟨345, 0, 4, 3⟩ (denote cache_345)] = denote cache_362
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_362

theorem verified_row_363 : fork [place ⟨137, 1, 4, 2⟩ cache_137, place ⟨248, 0, 2, 4⟩ cache_248] = cache_363 := by
  decide +kernel

theorem load_entry_363 : entryAt 363 = entry_363 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_363 : CacheEquation 363 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(363 < 6)), load_entry_363]
  change forkRow [placeRow ⟨137, 1, 4, 2⟩ (denote cache_137), placeRow ⟨248, 0, 2, 4⟩ (denote cache_248)] = denote cache_363
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_363

theorem verified_row_364 : fork [place ⟨63, 0, 3, 5⟩ cache_63, place ⟨314, 2, 3, 1⟩ cache_314] = cache_364 := by
  decide +kernel

theorem load_entry_364 : entryAt 364 = entry_364 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_364 : CacheEquation 364 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(364 < 6)), load_entry_364]
  change forkRow [placeRow ⟨63, 0, 3, 5⟩ (denote cache_63), placeRow ⟨314, 2, 3, 1⟩ (denote cache_314)] = denote cache_364
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_364

theorem verified_row_365 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨354, 0, 4, 3⟩ cache_354] = cache_365 := by
  decide +kernel

theorem load_entry_365 : entryAt 365 = entry_365 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_365 : CacheEquation 365 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(365 < 6)), load_entry_365]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨354, 0, 4, 3⟩ (denote cache_354)] = denote cache_365
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_365

theorem verified_row_366 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨357, 0, 6, 2⟩ cache_357] = cache_366 := by
  decide +kernel

theorem load_entry_366 : entryAt 366 = entry_366 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_366 : CacheEquation 366 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(366 < 6)), load_entry_366]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨357, 0, 6, 2⟩ (denote cache_357)] = denote cache_366
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_366

theorem verified_row_367 : fork [place ⟨6, 2, 5, 4⟩ cache_6, place ⟨361, 4, 4, 6⟩ cache_361] = cache_367 := by
  decide +kernel

theorem load_entry_367 : entryAt 367 = entry_367 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_367 : CacheEquation 367 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(367 < 6)), load_entry_367]
  change forkRow [placeRow ⟨6, 2, 5, 4⟩ (denote cache_6), placeRow ⟨361, 4, 4, 6⟩ (denote cache_361)] = denote cache_367
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_367

theorem verified_row_368 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨366, 0, 2, 4⟩ cache_366] = cache_368 := by
  decide +kernel

theorem load_entry_368 : entryAt 368 = entry_368 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_368 : CacheEquation 368 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(368 < 6)), load_entry_368]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨366, 0, 2, 4⟩ (denote cache_366)] = denote cache_368
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_368

theorem verified_row_369 : fork [place ⟨6, 0, 5, 4⟩ cache_6, place ⟨367, 4, 1, 2⟩ cache_367] = cache_369 := by
  decide +kernel

theorem load_entry_369 : entryAt 369 = entry_369 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_369 : CacheEquation 369 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(369 < 6)), load_entry_369]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (denote cache_6), placeRow ⟨367, 4, 1, 2⟩ (denote cache_367)] = denote cache_369
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_369

theorem verified_row_370 : fork [place ⟨199, 3, 1, 4⟩ cache_199, place ⟨286, 1, 5, 4⟩ cache_286, place ⟨24, 6, 1, 3⟩ cache_24, place ⟨319, 0, 5, 3⟩ cache_319] = cache_370 := by
  decide +kernel

theorem load_entry_370 : entryAt 370 = entry_370 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_370 : CacheEquation 370 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(370 < 6)), load_entry_370]
  change forkRow [placeRow ⟨199, 3, 1, 4⟩ (denote cache_199), placeRow ⟨286, 1, 5, 4⟩ (denote cache_286), placeRow ⟨24, 6, 1, 3⟩ (denote cache_24), placeRow ⟨319, 0, 5, 3⟩ (denote cache_319)] = denote cache_370
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_370

theorem verified_row_371 : fork [place ⟨267, 6, 2, 4⟩ cache_267, place ⟨137, 1, 4, 2⟩ cache_137] = cache_371 := by
  decide +kernel

theorem load_entry_371 : entryAt 371 = entry_371 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_371 : CacheEquation 371 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(371 < 6)), load_entry_371]
  change forkRow [placeRow ⟨267, 6, 2, 4⟩ (denote cache_267), placeRow ⟨137, 1, 4, 2⟩ (denote cache_137)] = denote cache_371
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_371

theorem verified_row_372 : fork [place ⟨40, 1, 4, 3⟩ cache_40, place ⟨333, 0, 2, 4⟩ cache_333, place ⟨120, 1, 3, 3⟩ cache_120, place ⟨161, 0, 4, 2⟩ cache_161] = cache_372 := by
  decide +kernel

theorem load_entry_372 : entryAt 372 = entry_372 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_372 : CacheEquation 372 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(372 < 6)), load_entry_372]
  change forkRow [placeRow ⟨40, 1, 4, 3⟩ (denote cache_40), placeRow ⟨333, 0, 2, 4⟩ (denote cache_333), placeRow ⟨120, 1, 3, 3⟩ (denote cache_120), placeRow ⟨161, 0, 4, 2⟩ (denote cache_161)] = denote cache_372
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_372

theorem verified_row_373 : fork [place ⟨156, 2, 7, 4⟩ cache_156, place ⟨226, 4, 3, 5⟩ cache_226, place ⟨80, 0, 5, 4⟩ cache_80, place ⟨327, 0, 5, 5⟩ cache_327, place ⟨156, 6, 3, 4⟩ cache_156] = cache_373 := by
  decide +kernel

theorem load_entry_373 : entryAt 373 = entry_373 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_373 : CacheEquation 373 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(373 < 6)), load_entry_373]
  change forkRow [placeRow ⟨156, 2, 7, 4⟩ (denote cache_156), placeRow ⟨226, 4, 3, 5⟩ (denote cache_226), placeRow ⟨80, 0, 5, 4⟩ (denote cache_80), placeRow ⟨327, 0, 5, 5⟩ (denote cache_327), placeRow ⟨156, 6, 3, 4⟩ (denote cache_156)] = denote cache_373
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_373

theorem verified_row_374 : fork [place ⟨65, 4, 3, 4⟩ cache_65, place ⟨335, 0, 7, 4⟩ cache_335, place ⟨24, 2, 7, 3⟩ cache_24, place ⟨163, 4, 3, 4⟩ cache_163] = cache_374 := by
  decide +kernel

theorem load_entry_374 : entryAt 374 = entry_374 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_374 : CacheEquation 374 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(374 < 6)), load_entry_374]
  change forkRow [placeRow ⟨65, 4, 3, 4⟩ (denote cache_65), placeRow ⟨335, 0, 7, 4⟩ (denote cache_335), placeRow ⟨24, 2, 7, 3⟩ (denote cache_24), placeRow ⟨163, 4, 3, 4⟩ (denote cache_163)] = denote cache_374
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_374

theorem verified_row_375 : fork [place ⟨24, 3, 3, 6⟩ cache_24, place ⟨327, 6, 3, 3⟩ cache_327] = cache_375 := by
  decide +kernel

theorem load_entry_375 : entryAt 375 = entry_375 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_375 : CacheEquation 375 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(375 < 6)), load_entry_375]
  change forkRow [placeRow ⟨24, 3, 3, 6⟩ (denote cache_24), placeRow ⟨327, 6, 3, 3⟩ (denote cache_327)] = denote cache_375
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_375

theorem verified_row_376 : fork [place ⟨162, 1, 5, 4⟩ cache_162, place ⟨285, 3, 1, 3⟩ cache_285] = cache_376 := by
  decide +kernel

theorem load_entry_376 : entryAt 376 = entry_376 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_376 : CacheEquation 376 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(376 < 6)), load_entry_376]
  change forkRow [placeRow ⟨162, 1, 5, 4⟩ (denote cache_162), placeRow ⟨285, 3, 1, 3⟩ (denote cache_285)] = denote cache_376
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_376

theorem verified_row_377 : fork [place ⟨29, 3, 3, 0⟩ cache_29, place ⟨362, 0, 7, 2⟩ cache_362] = cache_377 := by
  decide +kernel

theorem load_entry_377 : entryAt 377 = entry_377 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_377 : CacheEquation 377 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(377 < 6)), load_entry_377]
  change forkRow [placeRow ⟨29, 3, 3, 0⟩ (denote cache_29), placeRow ⟨362, 0, 7, 2⟩ (denote cache_362)] = denote cache_377
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_377

theorem verified_row_378 : fork [place ⟨295, 0, 5, 4⟩ cache_295, place ⟨176, 4, 1, 4⟩ cache_176, place ⟨183, 4, 1, 4⟩ cache_183, place ⟨172, 6, 1, 4⟩ cache_172, place ⟨294, 4, 1, 4⟩ cache_294] = cache_378 := by
  decide +kernel

theorem load_entry_378 : entryAt 378 = entry_378 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_378 : CacheEquation 378 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(378 < 6)), load_entry_378]
  change forkRow [placeRow ⟨295, 0, 5, 4⟩ (denote cache_295), placeRow ⟨176, 4, 1, 4⟩ (denote cache_176), placeRow ⟨183, 4, 1, 4⟩ (denote cache_183), placeRow ⟨172, 6, 1, 4⟩ (denote cache_172), placeRow ⟨294, 4, 1, 4⟩ (denote cache_294)] = denote cache_378
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_378

theorem verified_row_379 : fork [place ⟨63, 0, 3, 5⟩ cache_63, place ⟨64, 1, 3, 1⟩ cache_64, place ⟨55, 3, 4, 5⟩ cache_55, place ⟨368, 0, 5, 4⟩ cache_368] = cache_379 := by
  decide +kernel

theorem load_entry_379 : entryAt 379 = entry_379 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_379 : CacheEquation 379 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(379 < 6)), load_entry_379]
  change forkRow [placeRow ⟨63, 0, 3, 5⟩ (denote cache_63), placeRow ⟨64, 1, 3, 1⟩ (denote cache_64), placeRow ⟨55, 3, 4, 5⟩ (denote cache_55), placeRow ⟨368, 0, 5, 4⟩ (denote cache_368)] = denote cache_379
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_379

theorem verified_row_380 : fork [place ⟨101, 4, 2, 5⟩ cache_101, place ⟨271, 0, 2, 5⟩ cache_271, place ⟨223, 0, 5, 4⟩ cache_223, place ⟨192, 3, 1, 4⟩ cache_192] = cache_380 := by
  decide +kernel

theorem load_entry_380 : entryAt 380 = entry_380 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_380 : CacheEquation 380 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(380 < 6)), load_entry_380]
  change forkRow [placeRow ⟨101, 4, 2, 5⟩ (denote cache_101), placeRow ⟨271, 0, 2, 5⟩ (denote cache_271), placeRow ⟨223, 0, 5, 4⟩ (denote cache_223), placeRow ⟨192, 3, 1, 4⟩ (denote cache_192)] = denote cache_380
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_380

theorem verified_row_381 : fork [place ⟨211, 6, 3, 4⟩ cache_211, place ⟨24, 0, 7, 5⟩ cache_24, place ⟨163, 4, 3, 4⟩ cache_163, place ⟨341, 0, 7, 4⟩ cache_341] = cache_381 := by
  decide +kernel

theorem load_entry_381 : entryAt 381 = entry_381 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_381 : CacheEquation 381 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(381 < 6)), load_entry_381]
  change forkRow [placeRow ⟨211, 6, 3, 4⟩ (denote cache_211), placeRow ⟨24, 0, 7, 5⟩ (denote cache_24), placeRow ⟨163, 4, 3, 4⟩ (denote cache_163), placeRow ⟨341, 0, 7, 4⟩ (denote cache_341)] = denote cache_381
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_381

theorem verified_row_382 : fork [place ⟨124, 1, 5, 3⟩ cache_124, place ⟨2, 7, 4, 3⟩ cache_2] = cache_382 := by
  decide +kernel

theorem load_entry_382 : entryAt 382 = entry_382 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_382 : CacheEquation 382 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(382 < 6)), load_entry_382]
  change forkRow [placeRow ⟨124, 1, 5, 3⟩ (denote cache_124), placeRow ⟨2, 7, 4, 3⟩ (denote cache_2)] = denote cache_382
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_382

theorem verified_row_383 : fork [place ⟨192, 3, 2, 4⟩ cache_192, place ⟨271, 0, 3, 5⟩ cache_271, place ⟨197, 0, 6, 4⟩ cache_197, place ⟨172, 0, 6, 4⟩ cache_172, place ⟨215, 4, 3, 5⟩ cache_215] = cache_383 := by
  decide +kernel

theorem load_entry_383 : entryAt 383 = entry_383 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_383 : CacheEquation 383 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(383 < 6)), load_entry_383]
  change forkRow [placeRow ⟨192, 3, 2, 4⟩ (denote cache_192), placeRow ⟨271, 0, 3, 5⟩ (denote cache_271), placeRow ⟨197, 0, 6, 4⟩ (denote cache_197), placeRow ⟨172, 0, 6, 4⟩ (denote cache_172), placeRow ⟨215, 4, 3, 5⟩ (denote cache_215)] = denote cache_383
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_383

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

theorem cache_equations_range_304 : ∀ i, 304 ≤ i → i < 320 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_304
  · exact cache_equation_305
  · exact cache_equation_306
  · exact cache_equation_307
  · exact cache_equation_308
  · exact cache_equation_309
  · exact cache_equation_310
  · exact cache_equation_311
  · exact cache_equation_312
  · exact cache_equation_313
  · exact cache_equation_314
  · exact cache_equation_315
  · exact cache_equation_316
  · exact cache_equation_317
  · exact cache_equation_318
  · exact cache_equation_319

theorem cache_equations_range_320 : ∀ i, 320 ≤ i → i < 336 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_320
  · exact cache_equation_321
  · exact cache_equation_322
  · exact cache_equation_323
  · exact cache_equation_324
  · exact cache_equation_325
  · exact cache_equation_326
  · exact cache_equation_327
  · exact cache_equation_328
  · exact cache_equation_329
  · exact cache_equation_330
  · exact cache_equation_331
  · exact cache_equation_332
  · exact cache_equation_333
  · exact cache_equation_334
  · exact cache_equation_335

theorem cache_equations_range_336 : ∀ i, 336 ≤ i → i < 352 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_336
  · exact cache_equation_337
  · exact cache_equation_338
  · exact cache_equation_339
  · exact cache_equation_340
  · exact cache_equation_341
  · exact cache_equation_342
  · exact cache_equation_343
  · exact cache_equation_344
  · exact cache_equation_345
  · exact cache_equation_346
  · exact cache_equation_347
  · exact cache_equation_348
  · exact cache_equation_349
  · exact cache_equation_350
  · exact cache_equation_351

theorem cache_equations_range_352 : ∀ i, 352 ≤ i → i < 368 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_352
  · exact cache_equation_353
  · exact cache_equation_354
  · exact cache_equation_355
  · exact cache_equation_356
  · exact cache_equation_357
  · exact cache_equation_358
  · exact cache_equation_359
  · exact cache_equation_360
  · exact cache_equation_361
  · exact cache_equation_362
  · exact cache_equation_363
  · exact cache_equation_364
  · exact cache_equation_365
  · exact cache_equation_366
  · exact cache_equation_367

theorem cache_equations_range_368 : ∀ i, 368 ≤ i → i < 384 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_368
  · exact cache_equation_369
  · exact cache_equation_370
  · exact cache_equation_371
  · exact cache_equation_372
  · exact cache_equation_373
  · exact cache_equation_374
  · exact cache_equation_375
  · exact cache_equation_376
  · exact cache_equation_377
  · exact cache_equation_378
  · exact cache_equation_379
  · exact cache_equation_380
  · exact cache_equation_381
  · exact cache_equation_382
  · exact cache_equation_383

theorem cache_equations_range_304_336 : ∀ i, 304 ≤ i → i < 336 → CacheEquation i :=
  merge_ranges cache_equations_range_304 cache_equations_range_320

theorem cache_equations_range_352_384 : ∀ i, 352 ≤ i → i < 384 → CacheEquation i :=
  merge_ranges cache_equations_range_352 cache_equations_range_368

theorem cache_equations_range_336_384 : ∀ i, 336 ≤ i → i < 384 → CacheEquation i :=
  merge_ranges cache_equations_range_336 cache_equations_range_352_384

theorem cache_equations_range_304_384 : ∀ i, 304 ≤ i → i < 384 → CacheEquation i :=
  merge_ranges cache_equations_range_304_336 cache_equations_range_336_384

theorem cache_equations_range_304_464_oai : ∀ i, 304 ≤ i → i < 464 → CacheEquation i :=
  merge_ranges cache_equations_range_304_384 cache_equations_range_384_464

end SnakyCertificate.Check

end OAI
end

theorem solution : type_of% @OAI.SnakyCertificate.Check.cache_equations_range_304_464_oai := @OAI.SnakyCertificate.Check.cache_equations_range_304_464_oai
