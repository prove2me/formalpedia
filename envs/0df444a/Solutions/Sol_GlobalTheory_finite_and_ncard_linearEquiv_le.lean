-- Prove2me | solution 1 for GlobalTheory.finite_and_ncard_linearEquiv_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:41:14.316453+00:00
-- url     : https://prove2.me/submissions/aaae6fb0-2926-4081-9240-657c0fe6d781

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe
import Theorems.Thm_GlobalTheory_finite_and_ncard_le_of_norm_map_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
open MeasureTheory Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace GlobalTheory
theorem _root_.solution (L : Submodule ℤ E) [Module.Finite ℤ L] {n : ℕ}
    (hn : finrank ℤ L = n) {v : Fin n → L} (hv : LinearIndependent ℤ v) {lam1 lamN c : ℝ}
    (h1 : 0 < lam1) (hc : 0 ≤ c) (hL : ∀ x ∈ L, x ≠ 0 → lam1 ≤ ‖x‖)
    (hvN : ∀ i, ‖(v i : E)‖ ≤ lamN) (G : Set (L ≃ₗ[ℤ] L))
    (hG : ∀ g ∈ G, ∀ x : L, ‖(g x : E)‖ ≤ c * ‖(x : E)‖) :
    G.Finite ∧ (G.ncard : ℝ) ≤ (1 + 2 * c * lamN / lam1) ^ (n ^ 2) :=
  finite_and_ncard_le_of_norm_map_le L hn hv h1 hc hL hvN G LinearEquiv.toLinearMap
    LinearEquiv.toLinearMap_injective.injOn hG
end GlobalTheory
