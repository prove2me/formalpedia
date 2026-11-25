-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.eLpNorm_le_of_le_conv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:18:23.318855+00:00
-- url     : https://prove2.me/submissions/e8c5456e-b186-4912-a242-054fbd3188f5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_lintegral_conv_sq_le_mul

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {h g : E → ℂ} {K : E → ℝ≥0∞} (hK : Measurable K)
    (hg : Measurable g) (hh : ∀ ξ, ‖h ξ‖ₑ ≤ ∫⁻ η, K (ξ - η) * ‖g η‖ₑ) :
    eLpNorm h 2 volume ≤ (∫⁻ ζ, K ζ) * eLpNorm g 2 volume := by
  have hsq : eLpNorm h 2 volume ^ 2 ≤ ((∫⁻ ζ, K ζ) * eLpNorm g 2 volume) ^ 2 := by
    rw [L2Kernel.eLpNorm_two_sq, mul_pow, L2Kernel.eLpNorm_two_sq]
    calc ∫⁻ ξ, ‖h ξ‖ₑ ^ 2 ≤ ∫⁻ ξ, (∫⁻ η, K (ξ - η) * ‖g η‖ₑ) ^ 2 :=
          lintegral_mono fun ξ ↦ by gcongr; exact hh ξ
      _ ≤ _ := lintegral_conv_sq_le_mul hK hg.enorm
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 hsq
end GroundTheory.Automorphic.Sobolev
