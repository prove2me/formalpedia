-- Prove2me | solution 1 for GlobalTheory.entire_exists_coeff_of_poly_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:28:44.382316+00:00
-- url     : https://prove2.me/submissions/1f649537-82fa-481c-825f-3a82444d4567

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Theorems.Thm_GlobalTheory_entire_eq_taylor_sum_of_poly_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Metric Filter Topology
open scoped Nat
open GlobalTheory
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
namespace GlobalTheory
theorem _root_.solution {F : ℂ → V} (hF : Differentiable ℂ F) {C : ℝ}
    {m : ℕ} (hb : ∀ z, ‖F z‖ ≤ C * (1 + ‖z‖) ^ m) :
    ∃ a : ℕ → V, ∀ z, F z = ∑ k ∈ Finset.range (m + 1), z ^ k • a k :=
  ⟨_, entire_eq_taylor_sum_of_poly_bound hF hb⟩
end GlobalTheory
