-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.integral_smul_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:00:14.181054+00:00
-- url     : https://prove2.me/submissions/ed741112-6e9c-4b49-a3d3-f9d1dd63b0b7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev

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
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (r : ℝ) (φ : 𝓢(E, ℂ)) (g : Lp F 2 (volume : Measure E)) :
    (g : 𝓢'(E, F)) (SchwartzMap.smulLeftCLM ℂ (weight r) φ) =
      ∫ ξ, φ ξ • (weight r ξ • g ξ) := by
  rw [Lp.toTemperedDistribution_apply]
  congr 1; ext ξ
  rw [SchwartzMap.smulLeftCLM_apply_apply (weight_hasTemperateGrowth r)]
  simp only [smul_smul, smul_eq_mul, mul_comm]
end GroundTheory.Automorphic.Sobolev
