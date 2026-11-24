-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ThW.GaussOrth.measurableEmbedding_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:35:08.768451+00:00
-- url     : https://prove2.me/submissions/5fb8dec8-50d2-4e78-afff-d27525337a01

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussianChangeOfVariablesIsometry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ThW GlobalTheory.CompanionTheory.SW.ThW.GaussOrth
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
namespace GlobalTheory.CompanionTheory.SW.ThW.GaussOrth
theorem _root_.solution {W ι : Type} [Fintype W] [Fintype ι] [DecidableEq ι]
    {g : W → Matrix ι ι ℝ} (h : ∀ w, (g w).det ≠ 0) :
    MeasurableEmbedding (fun (x : W → ι → ℝ) (w : W) => g w *ᵥ x w) := by
  have hu : ∀ w, IsUnit (g w).det := fun w => isUnit_iff_ne_zero.mpr (h w)
  let e : (W → ι → ℝ) ≃ᵐ (W → ι → ℝ) :=
    { toFun := fun x w => g w *ᵥ x w
      invFun := fun x w => (g w)⁻¹ *ᵥ x w
      left_inv := by
        intro x
        funext w
        simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hu w), Matrix.one_mulVec]
      right_inv := by
        intro x
        funext w
        simp only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hu w), Matrix.one_mulVec]
      measurable_toFun := by
        refine Continuous.measurable (continuous_pi fun w => ?_)
        exact Continuous.matrix_mulVec continuous_const (continuous_apply w)
      measurable_invFun := by
        refine Continuous.measurable (continuous_pi fun w => ?_)
        exact Continuous.matrix_mulVec continuous_const (continuous_apply w) }
  exact e.measurableEmbedding
end GlobalTheory.CompanionTheory.SW.ThW.GaussOrth
