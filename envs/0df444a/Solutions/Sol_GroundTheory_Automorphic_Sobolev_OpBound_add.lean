-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.OpBound.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:17:34.355575+00:00
-- url     : https://prove2.me/submissions/d081d1f9-e847-4c47-9426-17698a34d77d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_add_le


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
theorem _root_.solution (hA : OpBound A s t C) (hB : OpBound B s t D) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    OpBound (A + B) s t (C + D) := fun u hu ↦ by
  rw [add_apply, ENNReal.ofReal_add hC hD, add_mul]
  exact (sob_add_le _ _).trans (add_le_add (hA u hu) (hB u hu))
end GroundTheory.Automorphic.Sobolev.OpBound
