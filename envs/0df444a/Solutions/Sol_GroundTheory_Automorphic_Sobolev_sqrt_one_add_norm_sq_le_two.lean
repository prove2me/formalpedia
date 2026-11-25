-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.sqrt_one_add_norm_sq_le_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:56:26.484403+00:00
-- url     : https://prove2.me/submissions/9d56f5b6-31b7-4d1a-8061-f7d2c9a3b152

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
theorem _root_.solution {ξ : E} (h : ‖ξ‖ ≤ 1) : Real.sqrt (1 + ‖ξ‖ ^ 2) ≤ 2 := by
  rw [Real.sqrt_le_iff]; constructor
  · norm_num
  · nlinarith [norm_nonneg ξ]
end GroundTheory.Automorphic.Sobolev
