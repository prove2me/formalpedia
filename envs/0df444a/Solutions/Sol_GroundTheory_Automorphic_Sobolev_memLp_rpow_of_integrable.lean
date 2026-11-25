-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.memLp_rpow_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:13:27.319466+00:00
-- url     : https://prove2.me/submissions/7284e763-a174-4ded-9a9b-a02cdf269aaa

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevFriedrichs
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevInterpolation
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_convolutionCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_lineDerivCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_sub
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_convolutionCLM
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_lineDerivCLM
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_sub
attribute [local simp] GroundTheory.Automorphic.Sobolev.dualEquiv_apply



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
theorem _root_.solution {A : E → ℝ} (hA : Integrable A (volume : Measure E))
    (h0 : ∀ ξ, 0 ≤ A ξ) {a : ℝ} (ha : 0 < a) :
    MemLp (fun ξ ↦ A ξ ^ a) (ENNReal.ofReal (1 / a)) (volume : Measure E) := by
  have hm : AEStronglyMeasurable (fun ξ ↦ A ξ ^ a) (volume : Measure E) :=
    (hA.1.aemeasurable.pow_const a).aestronglyMeasurable
  have hq0 : ENNReal.ofReal (1 / a) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  rw [← memLp_norm_rpow_iff hm hq0 ENNReal.ofReal_ne_top,
    ENNReal.div_self hq0 ENNReal.ofReal_ne_top, memLp_one_iff_integrable]
  refine hA.congr (ae_of_all _ fun ξ ↦ ?_)
  simp only
  rw [ENNReal.toReal_ofReal (by positivity), Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (h0 ξ) a), ← Real.rpow_mul (h0 ξ), mul_one_div_cancel ha.ne',
    Real.rpow_one]
end GroundTheory.Automorphic.Sobolev
