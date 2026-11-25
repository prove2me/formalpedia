-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.sqrt_one_add_norm_sq_le_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:56:31.378185+00:00
-- url     : https://prove2.me/submissions/bbcf5734-c5c7-425e-898c-d316ae1b9a89

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
variable {ι : Type*} [Fintype ι] {m : ℕ} (c : ι → ℂ) (w : ι → Fin m → E) {cl Cu : ℝ}
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {ξ : E} (h : 1 ≤ ‖ξ‖) :
    Real.sqrt (1 + ‖ξ‖ ^ 2) ≤ 2 * ‖ξ‖ := by
  rw [Real.sqrt_le_iff]; constructor
  · positivity
  · nlinarith
end GroundTheory.Automorphic.Sobolev
