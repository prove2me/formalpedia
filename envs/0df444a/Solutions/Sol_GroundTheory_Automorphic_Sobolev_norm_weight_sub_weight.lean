-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.norm_weight_sub_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:22:10.734462+00:00
-- url     : https://prove2.me/submissions/bd8ec0b9-d2ca-4e23-a32a-586b1a26d4ce

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication

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
variable (χ : 𝓢(E, ℂ))
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (r : ℝ) (ξ η : E) :
    ‖weight r ξ - weight r η‖ = |(1 + ‖ξ‖ ^ 2) ^ (r / 2) - (1 + ‖η‖ ^ 2) ^ (r / 2)| := by
  unfold weight
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
end GroundTheory.Automorphic.Sobolev
