-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.OpBound.congr_idx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:56:24.38514+00:00
-- url     : https://prove2.me/submissions/dc2e36aa-76b5-4464-99cb-326c22549d78

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal

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
theorem _root_.solution (hA : OpBound A s t C) {s' t' : ℝ} (hs : s' = s) (ht : t' = t) :
    OpBound A s' t' C := by subst hs ht; exact hA
end GroundTheory.Automorphic.Sobolev.OpBound
