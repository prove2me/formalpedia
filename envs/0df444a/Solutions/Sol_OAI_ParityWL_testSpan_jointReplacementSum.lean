-- Prove2me | solution 1 for OAI.ParityWL.testSpan_jointReplacementSum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:41:50.758552+00:00
-- url     : https://prove2.me/submissions/fcaab1cd-1cc1-4714-83d3-86354b9422b2

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/Interpolation.lean:L120-L156
-- (upload_full_project.md Phase 4): solution for node OAI.ParityWL.testSpan_jointReplacementSum. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BaseLabels
import Definitions.Def_OAI_Combinatorics_ParityLifts_BalancedBags
import Definitions.Def_OAI_Combinatorics_ParityLifts_DecompositionCuts
import Definitions.Def_OAI_Combinatorics_ParityLifts_Witnesses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BagTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_TagSizes
import Definitions.Def_OAI_Combinatorics_ParityLifts_Detection
import Definitions.Def_OAI_Combinatorics_ParityLifts_RankedTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_RootedTests
import Definitions.Def_OAI_Combinatorics_ParityLifts_GlueTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_GlueVertices
import Definitions.Def_OAI_Combinatorics_ParityLifts_Rerooting
import Definitions.Def_OAI_Combinatorics_ParityLifts_TestAlgebra
import Definitions.Def_OAI_Combinatorics_ParityLifts_Interpolation
import Theorems.Thm_OAI_ParityWL_testSpan_reindex
import Theorems.Thm_OAI_ParityWL_testSpan_sumInsert

-- ---- from OAI.Combinatorics.ParityLifts.Interpolation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace ParityWL

open scoped BigOperators

section FiniteInterpolation

open scoped Classical

end FiniteInterpolation

section RefinementOperators

open scoped Classical

variable {V W : Type} [Fintype V] [Fintype W]
variable (G : SimpleGraph V) (H : SimpleGraph W)

lemma insertNth_replaceEmbedding {k : ℕ} {A : Type} (i : Fin k) (y : A) (x : Fin k → A) :
    ((Fin.last k).insertNth y x) ∘ replaceEmbedding i = Function.update x i y := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [replaceEmbedding]
  · simp only [Function.comp_apply, replaceEmbedding, ite_eq_right hj, Function.update_of_ne hj]
    rw [← Fin.succAbove_last_apply j, Fin.insertNth_apply_succAbove]

lemma testSpan_jointReplacementSum {k t : ℕ} (hkt : k + 1 ≤ t)
    {f : Fin k → TuplePair V W k → ℚ} (hf : ∀ i, f i ∈ testSpan G H k t) :
    jointReplacementSum f ∈ testSpan G H k t := by
  have hp : (∏ i : Fin k, reindexLinear (replaceEmbedding i) (f i)) ∈
      testSpan G H (k + 1) t :=
    (testAlgebra G H (k + 1) t hkt).prod_mem
      (fun i _ => testSpan_reindex G H hkt (replaceEmbedding i) (hf i))
  have hs := testSpan_sumInsert G H (by omega) (Fin.last k) hp
  have he : jointReplacementSum f = sumInsertLinear (Fin.last k)
      (∏ i : Fin k, reindexLinear (replaceEmbedding i) (f i)) := by
    funext a
    cases a with
    | inl x =>
      change (∑ y : V, ∏ i : Fin k, f i (.inl (Function.update x i y))) =
        ∑ y : V, (∏ i : Fin k, reindexLinear (replaceEmbedding i) (f i))
          (.inl ((Fin.last k).insertNth y x))
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.prod_apply]
      apply Finset.prod_congr rfl
      intro i _
      change f i (.inl (Function.update x i y)) =
        f i (.inl (((Fin.last k).insertNth y x) ∘ replaceEmbedding i))
      rw [insertNth_replaceEmbedding]
    | inr x =>
      change (∑ y : W, ∏ i : Fin k, f i (.inr (Function.update x i y))) =
        ∑ y : W, (∏ i : Fin k, reindexLinear (replaceEmbedding i) (f i))
          (.inr ((Fin.last k).insertNth y x))
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.prod_apply]
      apply Finset.prod_congr rfl
      intro i _
      change f i (.inr (Function.update x i y)) =
        f i (.inr (((Fin.last k).insertNth y x) ∘ replaceEmbedding i))
      rw [insertNth_replaceEmbedding]
  rwa [← he] at hs

end RefinementOperators

end ParityWL

end OAI

-- ---- platform node ----
open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical


theorem solution : type_of% @_root_.OAI.ParityWL.testSpan_jointReplacementSum := @_root_.OAI.ParityWL.testSpan_jointReplacementSum
