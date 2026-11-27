-- Prove2me | solution 1 for GlobalTheory.T.tendsto_sub_of_one_sided_increment_bound_derivative
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:33:47.12573+00:00
-- url     : https://prove2.me/submissions/a806da5e-63da-49ed-b78b-d39d2a658e7f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RiemannSumOfOneSidedIncrements
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RiemannSumOfOneSidedIncrementsStatement
import Theorems.Thm_GlobalTheory_riemann_sum_of_one_sided_increments


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (s : Polynomial ℝ) (ℓ : ℚ → ℕ → ℝ), (∀ t t' : ℚ, 0 ≤ t → t ≤ 1 → 0 ≤ t' → t' ≤ 1 → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, ℓ t m - ℓ t' m ≤ ((t' : ℝ) - t) * s.derivative.eval (t : ℝ) + ε) → Tendsto (fun m => ℓ 0 m - ℓ 1 m) atTop (𝓝 (s.eval 1 - s.eval 0)) := by
  first | exact @GlobalTheory.riemann_sum_of_one_sided_increments | exact GlobalTheory.riemann_sum_of_one_sided_increments | (intros; apply GlobalTheory.riemann_sum_of_one_sided_increments <;> assumption)
end _root_.GlobalTheory.T
