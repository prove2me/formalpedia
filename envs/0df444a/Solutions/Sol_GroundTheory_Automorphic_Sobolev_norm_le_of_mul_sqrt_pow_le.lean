-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.norm_le_of_mul_sqrt_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:29:14.889311+00:00
-- url     : https://prove2.me/submissions/c2b52210-03bf-456c-aec4-26fb09e2a921

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_one_le_sqrt_one_add_norm_sq
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_rpow_eq_sqrt_pow

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
theorem _root_.solution {f : E → ℂ} {C : ℝ} {k : ℕ}
    (h : ∀ ξ, ‖f ξ‖ * Real.sqrt (1 + ‖ξ‖ ^ 2) ^ k ≤ C) (ξ : E) :
    ‖f ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-(k : ℝ) / 2) := by
  have hp : 0 < Real.sqrt (1 + ‖ξ‖ ^ 2) ^ k :=
    pow_pos (lt_of_lt_of_le one_pos (one_le_sqrt_one_add_norm_sq ξ)) k
  rw [neg_div, Real.rpow_neg (by positivity), rpow_eq_sqrt_pow, ← div_eq_mul_inv,
    le_div_iff₀ hp]
  exact h ξ
end GroundTheory.Automorphic.Sobolev
