-- Prove2me | solution 1 for GlobalTheory.RationalIntegralCoordinates.int_of_prime_mul_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:48:36.098278+00:00
-- url     : https://prove2.me/submissions/f587b1fb-16eb-4ad8-ada1-194f57cca2cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IntOfPrimeMulSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RationalIntegralCoordinates
namespace GlobalTheory.RationalIntegralCoordinates
theorem _root_.solution {d : ℕ} (hd : d.Prime) {q : ℚ} {n : ℤ}
    (h : (d : ℚ) * q ^ 2 = n) : ∃ k : ℤ, (k : ℚ) = q := by
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hz : (d : ℤ) * q.num ^ 2 = (q.den : ℤ) ^ 2 * n := by
    have hq : q = q.num / q.den := (Rat.num_div_den q).symm
    rw [hq, div_pow] at h
    field_simp at h
    exact_mod_cast h
  have hcop : IsCoprime ((q.den : ℤ) ^ 2) (q.num ^ 2) := by
    apply IsCoprime.pow
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    exact q.reduced
  have hdvd : (q.den : ℤ) ^ 2 ∣ d := hcop.dvd_of_dvd_mul_right ⟨n, hz⟩
  have hdvd' : q.den ∣ d := by
    have : q.den ^ 2 ∣ d := by exact_mod_cast hdvd
    exact (dvd_pow_self _ two_ne_zero).trans this
  rcases hd.eq_one_or_self_of_dvd _ hdvd' with h1 | h1
  · exact ⟨q.num, by rw [← Rat.den_eq_one_iff]; exact h1⟩
  · exfalso
    have h2 : q.den ^ 2 ∣ d := by exact_mod_cast hdvd
    rw [h1] at h2
    have h3 := Nat.le_of_dvd hd.pos h2
    have h4 := hd.two_le
    nlinarith
end GlobalTheory.RationalIntegralCoordinates
