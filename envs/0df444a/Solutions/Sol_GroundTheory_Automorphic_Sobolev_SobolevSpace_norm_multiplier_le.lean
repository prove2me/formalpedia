-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.SobolevSpace.norm_multiplier_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:59:33.18867+00:00
-- url     : https://prove2.me/submissions/d16cdf5b-ab39-4c4b-a0dd-e9ff0219496c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_bound_nonneg

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
    (hC : ∀ ξ, ‖m ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((s - t) / 2)) :
    ‖multiplier (E := E) (F := F) hm hC‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ (bound_nonneg hC) _
end GroundTheory.Automorphic.Sobolev.SobolevSpace
