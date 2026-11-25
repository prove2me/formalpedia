-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.norm_inclusion_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:19:54.680145+00:00
-- url     : https://prove2.me/submissions/f370335e-82c1-4dfb-9e67-1f74c3fbcbd9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevFriedrichs
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevInterpolation
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourierFun_inclusion
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_sq_eq_integral


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
theorem _root_.solution {s t : ℝ} (h : t ≤ s) (v : SobolevSpace E F s) :
    ‖SobolevSpace.inclusion h v‖ ^ 2 = ∫ ξ, (1 + ‖ξ‖ ^ 2) ^ t * ‖fourierFun v ξ‖ ^ 2 := by
  rw [norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [fourierFun_inclusion h v] with ξ hξ
  rw [hξ]
end GroundTheory.Automorphic.Sobolev
