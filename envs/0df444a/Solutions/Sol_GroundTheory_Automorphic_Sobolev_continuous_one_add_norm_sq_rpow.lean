-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.continuous_one_add_norm_sq_rpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:54:16.654177+00:00
-- url     : https://prove2.me/submissions/7e399582-1af8-4666-b160-45eabdb702e6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Theorems.Thm_GroundTheory_Automorphic_IsHilbertSchmidt_add


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
theorem _root_.solution (c : ℝ) : Continuous fun ζ : E ↦ (1 + ‖ζ‖ ^ 2) ^ c :=
  (continuous_const.add (continuous_norm.pow 2)).rpow_const
    fun ζ ↦ Or.inl (by positivity : (0 : ℝ) < 1 + ‖ζ‖ ^ 2).ne'
end GroundTheory.Automorphic.Sobolev
