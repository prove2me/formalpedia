-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.SobolevSpace.norm_inclusion_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:12:46.565626+00:00
-- url     : https://prove2.me/submissions/d47c6770-b1aa-4307-9c80-607e8b19c0a0

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_norm_multiplier_apply_le

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
variable {s t : ℝ}
namespace GroundTheory.Automorphic.Sobolev.SobolevSpace
theorem _root_.solution (h : t ≤ s) (u : SobolevSpace E F s) :
    ‖inclusion h u‖ ≤ ‖u‖ := by
  have := norm_multiplier_apply_le (m := fun _ ↦ (1 : ℂ)) (F := F)
    (Function.HasTemperateGrowth.const 1) (one_bound h) u
  rw [one_mul] at this
  exact this
end GroundTheory.Automorphic.Sobolev.SobolevSpace
