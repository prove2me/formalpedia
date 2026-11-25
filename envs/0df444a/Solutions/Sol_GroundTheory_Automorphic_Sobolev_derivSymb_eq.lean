-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.derivSymb_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:23:32.701483+00:00
-- url     : https://prove2.me/submissions/57583d58-b5e2-401b-9da2-9dbdd83c1bc6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators

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
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {k : ℕ} (w : Fin k → E) (ξ : E) :
    derivSymb w ξ = (2 * Real.pi * Complex.I) ^ k * ∏ j, ((inner ℝ ξ (w j) : ℝ) : ℂ) := by
  rw [derivSymb, Finset.prod_mul_distrib, Fin.prod_const]
end GroundTheory.Automorphic.Sobolev
