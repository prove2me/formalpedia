-- Prove2me | solution 1 for GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:43:49.275021+00:00
-- url     : https://prove2.me/submissions/a1de996d-0406-4f28-9a0d-33f7085c9980

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimeGtDvdEval
import Theorems.Thm_GlobalTheory_PrimeDivisorOfPolynomialValue_exists_eval_mul_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PrimeDivisorOfPolynomialValue
open Polynomial
namespace GlobalTheory.PrimeDivisorOfPolynomialValue
theorem _root_.solution :
    ∀ (f : Polynomial ℤ), (0 : ℕ) < Polynomial.natDegree f → ∀ (n : ℕ),
      ∃ (p : ℕ), Nat.Prime p ∧ n < p ∧ ∃ (x : ℤ), (↑p : ℤ) ∣ Polynomial.eval x f := by
  intro f hf n

  have of_root : ∀ x, f.eval x = 0 → ∃ p, Nat.Prime p ∧ n < p ∧ ∃ x : ℤ, (p : ℤ) ∣ f.eval x := by
    intro x hx
    obtain ⟨p, hnp, hp⟩ := Nat.exists_infinite_primes (n + 1)
    exact ⟨p, hp, hnp, x, by rw [hx]; exact dvd_zero _⟩
  by_cases h0 : f.eval 0 = 0
  · exact of_root 0 h0
  have hfac : ((n.factorial : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  obtain ⟨k, hk1, hk2⟩ := exists_eval_mul_ne f hf (f.eval 0) _ (mul_ne_zero h0 hfac)
  by_cases hx : f.eval (f.eval 0 * n.factorial * k) = 0
  · exact of_root _ hx

  obtain ⟨q, hq⟩ := Polynomial.sub_dvd_eval_sub (f.eval 0 * n.factorial * k) 0 f
  have hft : f.eval (f.eval 0 * n.factorial * k) = f.eval 0 * (1 + n.factorial * k * q) := by
    linear_combination hq
  have ht1 : (1 + (n.factorial : ℤ) * k * q) ≠ 1 := fun h => hk1 (by rw [hft, h, mul_one])
  have ht2 : (1 + (n.factorial : ℤ) * k * q) ≠ -1 := fun h => hk2 (by rw [hft, h, mul_neg_one])
  have hnat : (1 + (n.factorial : ℤ) * k * q).natAbs ≠ 1 := by
    intro h
    rcases Int.natAbs_eq_iff.1 h with h | h
    · exact ht1 (by simpa using h)
    · exact ht2 (by simpa using h)
  have hp := Nat.minFac_prime hnat
  have hpt : ((1 + (n.factorial : ℤ) * k * q).natAbs.minFac : ℤ) ∣ (1 + (n.factorial : ℤ) * k * q) :=
    Int.ofNat_dvd_left.2 (Nat.minFac_dvd _)
  refine ⟨_, hp, ?_, _, by rw [hft]; exact dvd_mul_of_dvd_right hpt _⟩

  by_contra hle
  rw [not_lt] at hle
  have h3 : ((1 + (n.factorial : ℤ) * k * q).natAbs.minFac : ℤ) ∣ (n.factorial : ℤ) * k * q :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.2 (Nat.dvd_factorial hp.pos hle)) _) _
  have h4 := dvd_sub hpt h3
  rw [add_sub_cancel_right] at h4
  exact hp.not_dvd_one (Int.natCast_dvd_natCast.1 (by simpa using h4))
end GlobalTheory.PrimeDivisorOfPolynomialValue
