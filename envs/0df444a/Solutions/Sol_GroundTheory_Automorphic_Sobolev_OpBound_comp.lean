-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.OpBound.comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:16:26.488528+00:00
-- url     : https://prove2.me/submissions/5c09d638-a7b3-4cd0-97bb-1d4bffbc0044

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_OpBound_memSobolev
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_memSobolev


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
open GroundTheory.Automorphic.Sobolev.OpBound
variable {A B : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {s t r C D : ℝ}
namespace GroundTheory.Automorphic.Sobolev.OpBound
theorem _root_.solution (hA : OpBound A t r C) (hB : OpBound B s t D) (hC : 0 ≤ C) :
    OpBound (A ∘L B) s r (C * D) := fun u hu ↦ by
  rw [ContinuousLinearMap.comp_apply, ENNReal.ofReal_mul hC, mul_assoc]
  exact (hA _ (hB.memSobolev hu)).trans (mul_le_mul_right (hB u hu) _)
end GroundTheory.Automorphic.Sobolev.OpBound
