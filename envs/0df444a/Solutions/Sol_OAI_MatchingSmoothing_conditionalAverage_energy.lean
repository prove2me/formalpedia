-- Prove2me | solution 1 for OAI.MatchingSmoothing.conditionalAverage_energy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:06:55.573817+00:00
-- url     : https://prove2.me/submissions/de55d96a-6a43-4aba-8b9f-3a2a2d0c7f65

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/IncidenceKernels.lean:L149-L166
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingSmoothing.conditionalAverage_energy. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels

-- ---- from OAI.Combinatorics.MatchingPSD.IncidenceKernels ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace MatchingSmoothing
open Matrix

section FiniteSums
variable {G : Type u_1} {X : Type u_2} [Fintype G] [Group G] [Fintype X] [MulAction G X]

end FiniteSums

section KernelTrace
variable {G : Type u_3} {X : Type u_4} [Fintype G] [Group G] [Fintype X] [DecidableEq X]
  [MulAction G X]

end KernelTrace

section Incidence
variable {X : Type u_5} {Z : Type u_6} [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq Z]

omit [Fintype X] [DecidableEq X] [DecidableEq Z] in
lemma commonIncidence_eq (P : X → Z → Prop) (x y : X) :
    commonIncidence P x y = ∑ z, incidence P z x * incidence P z y := by
  classical
  simp only [commonIncidence, Fintype.card_subtype, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hx : P x z <;> by_cases hy : P y z <;> simp [incidence, hx, hy]

omit [DecidableEq X] [DecidableEq Z] in
lemma incidenceOperator_eq (P : X → Z → Prop) (D : ℝ) :
    incidenceOperator P D =
      ((Fintype.card Z : ℝ) / (D ^ 2 * Fintype.card X)) •
        ((incidence P).transpose * incidence P) := by
  ext x y
  simp only [incidenceOperator, incidenceKernel, commonIncidence_eq, Matrix.smul_apply,
    smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply]
  ring

omit [DecidableEq X] [DecidableEq Z] in
lemma conditionalAverage_energy [Nonempty X] [Nonempty Z]
    (P : X → Z → Prop) (D : ℝ) (hD : D ≠ 0) (f : X → ℝ) :
    (∑ z, conditionalAverage P ((Fintype.card X : ℝ) * D / Fintype.card Z) f z ^ 2) /
      Fintype.card Z =
    (∑ x, f x * (incidenceOperator P D *ᵥ f) x) / Fintype.card X := by
  have hx : (Fintype.card X : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hz : (Fintype.card Z : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  change _ = (f ⬝ᵥ (incidenceOperator P D *ᵥ f)) / Fintype.card X
  rw [incidenceOperator_eq, Matrix.smul_mulVec, dotProduct_smul,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  simp only [conditionalAverage, div_pow, ← Finset.sum_div, smul_eq_mul]
  change (∑ z, ((incidence P *ᵥ f) z) ^ 2) /
    (((Fintype.card X : ℝ) * D) ^ 2 / (Fintype.card Z : ℝ) ^ 2) / Fintype.card Z =
    ((Fintype.card Z : ℝ) / (D ^ 2 * Fintype.card X)) *
      (∑ z, (incidence P *ᵥ f) z * (incidence P *ᵥ f) z) / Fintype.card X
  simp only [← pow_two]
  field_simp

end Incidence
end MatchingSmoothing

end OAI

-- ---- platform node ----
open OAI OAI.MatchingSmoothing
open Matrix


theorem solution : type_of% @_root_.OAI.MatchingSmoothing.conditionalAverage_energy := @_root_.OAI.MatchingSmoothing.conditionalAverage_energy
