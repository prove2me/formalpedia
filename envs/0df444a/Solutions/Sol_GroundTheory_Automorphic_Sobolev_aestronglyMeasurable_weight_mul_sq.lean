-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.aestronglyMeasurable_weight_mul_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:14:04.534073+00:00
-- url     : https://prove2.me/submissions/fe6a6f7e-bbfe-4919-a646-1ccf862459df

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMollifier
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevFriedrichs
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourierFun_aestronglyMeasurable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {s : ℝ} (u : SobolevSpace E F s) (g : E → ℝ)
    (hg : Continuous g) :
    AEStronglyMeasurable (fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ s * g ξ * ‖fourierFun u ξ‖ ^ 2)
      (volume : Measure E) := by
  have hc : Continuous (fun ξ : E ↦ (1 + ‖ξ‖ ^ 2) ^ s) :=
    (continuous_const.add (continuous_norm.pow 2)).rpow_const
      fun ξ ↦ Or.inl (by positivity : (0 : ℝ) < 1 + ‖ξ‖ ^ 2).ne'
  exact ((hc.mul hg).aestronglyMeasurable).mul ((fourierFun_aestronglyMeasurable u).norm.pow 2)
end GroundTheory.Automorphic.Sobolev
