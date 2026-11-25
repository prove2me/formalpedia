-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.SobolevSpace.norm_multiplier_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:06:00.794397+00:00
-- url     : https://prove2.me/submissions/1a697d01-14ca-4f87-85a1-98a6a8eca5a0

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_norm_multiplier_le

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
variable {m : E → ℂ} {C s t : ℝ}
open GroundTheory.Automorphic.Sobolev.SobolevSpace
namespace GroundTheory.Automorphic.Sobolev.SobolevSpace
theorem _root_.solution (hm : m.HasTemperateGrowth)
    (hC : ∀ ξ, ‖m ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((s - t) / 2)) (u : SobolevSpace E F s) :
    ‖multiplier hm hC u‖ ≤ C * ‖u‖ :=
  ((multiplier hm hC).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right (norm_multiplier_le hm hC) (norm_nonneg _))
end GroundTheory.Automorphic.Sobolev.SobolevSpace
