-- Prove2me | solution 1 for GlobalTheory.finite_and_ncard_le_of_norm_map_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:34:42.33321+00:00
-- url     : https://prove2.me/submissions/8b44e24a-14d5-4ed8-bc5e-a2e88ef98d71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe
import Theorems.Thm_GlobalTheory_finite_and_ncard_le_of_norm_apply_le

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
    (hvN : ∀ i, ‖(v i : E)‖ ≤ lamN) {Γ : Type*} (G : Set Γ)
    (φ : Γ → L →ₗ[ℤ] L) (hφ : Set.InjOn φ G)
    (hG : ∀ g ∈ G, ∀ x : L, ‖(φ g x : E)‖ ≤ c * ‖(x : E)‖) :
    G.Finite ∧ (G.ncard : ℝ) ≤ (1 + 2 * c * lamN / lam1) ^ (n ^ 2) := by
  have h := finite_and_ncard_le_of_norm_apply_le L hn hv h1
    (R := c * max lamN 0) (by positivity) hL G φ hφ fun g hg i =>
      (hG g hg _).trans (mul_le_mul_of_nonneg_left ((hvN i).trans (le_max_left _ _)) hc)
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simpa using h
  · rwa [max_eq_left ((norm_nonneg _).trans (hvN ⟨0, hn0⟩)), ← mul_assoc] at h
end GlobalTheory
