-- Prove2me | solution 1 for GlobalTheory.isSquare_one_add_of_pow_two_pow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:11:18.225233+00:00
-- url     : https://prove2.me/submissions/44b0d7ca-7a4e-434d-9768-5da381cf7aab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitsModSqFiniteOfFields

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {A : Type} [CommRing A] (c : A)
    (hc : 2 * c = 1) : ∀ (m : ℕ) (n : A), n ^ (2 ^ m) = 0 → IsSquare (1 + n) := by
  intro m
  induction m with
  | zero =>
    intro n hn
    simp only [pow_zero, pow_one] at hn
    exact ⟨1, by rw [hn]; ring⟩
  | succ m ih =>
    intro n hn
    have hnil : IsNilpotent (c * n) := ⟨2 ^ (m + 1), by rw [mul_pow, hn, mul_zero]⟩
    obtain ⟨v, hv⟩ := (hnil.isUnit_one_add).exists_right_inv
    have hn' : (-(c ^ 2 * n ^ 2 * v ^ 2)) ^ (2 ^ m) = 0 := by
      have : -(c ^ 2 * n ^ 2 * v ^ 2) = n ^ 2 * (-(c ^ 2 * v ^ 2)) := by ring
      rw [this, mul_pow, ← pow_mul, ← pow_succ', hn, zero_mul]
    obtain ⟨z, hz⟩ := ih _ hn'
    refine ⟨(1 + c * n) * z, ?_⟩
    linear_combination (1 + c * n) ^ 2 * hz + (c ^ 2 * n ^ 2 * ((1 + c * n) * v + 1)) * hv
      + (-n) * hc
end GlobalTheory
