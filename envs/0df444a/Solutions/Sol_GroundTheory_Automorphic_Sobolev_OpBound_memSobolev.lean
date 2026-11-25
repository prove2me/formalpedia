-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.OpBound.memSobolev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:55:33.430856+00:00
-- url     : https://prove2.me/submissions/b09a4880-e840-4662-8ab0-ef446016db8a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_memSobolev_of_sob_le


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
theorem _root_.solution (h : OpBound A s t C) {u : 𝓢'(E, ℂ)} (hu : MemSobolev s 2 u) :
    MemSobolev t 2 (A u) :=
  memSobolev_of_sob_le ENNReal.ofReal_ne_top (h u hu) hu
end GroundTheory.Automorphic.Sobolev.OpBound
