-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.fourierFun_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:55:23.464041+00:00
-- url     : https://prove2.me/submissions/d3bcdebb-6e54-458e-a862-33d7ce35139a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevFriedrichs
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevInterpolation
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourierFun_multiplier


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
    fourierFun (SobolevSpace.inclusion h v) =ᵐ[volume] fourierFun v := by
  have := (fourierFun_multiplier (m := fun _ ↦ (1 : ℂ)) (Function.HasTemperateGrowth.const 1)
    (SobolevSpace.one_bound h) v).1
  filter_upwards [this] with ξ hξ
  rw [one_smul] at hξ
  exact hξ
end GroundTheory.Automorphic.Sobolev
