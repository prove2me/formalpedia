-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.derivSymb_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:04:54.565516+00:00
-- url     : https://prove2.me/submissions/a856c2e1-d1f3-411c-aea0-3eac43a39b63

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
theorem _root_.solution {k : ℕ} (w : Fin (k + 1) → E) (ξ : E) :
    derivSymb w ξ = derivSymb (Fin.tail w) ξ * ((2 * Real.pi * Complex.I) * ((inner ℝ ξ (w 0) : ℝ) : ℂ)) := by
  rw [derivSymb, Fin.prod_univ_succ, mul_comm]; rfl
end GroundTheory.Automorphic.Sobolev
