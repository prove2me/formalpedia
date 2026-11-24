-- Prove2me | solution 1 for GlobalTheory.sep_int_poly_root_mod_prime_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:32:39.876158+00:00
-- url     : https://prove2.me/submissions/1b855d0f-af99-4cd8-9f3d-6be30918027a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLargePrimeDvdIntPolynomialEvalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SepIntPolyRootModPrimeSq
import Theorems.Thm_GlobalTheory_int_bezout_derivative_of_separable
import Theorems.Thm_GlobalTheory_T_exists_large_prime_dvd_int_polynomial_eval


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Polynomial
open GlobalTheory
open Polynomial
namespace GlobalTheory
theorem _root_.solution :
    ∀ f : ℤ[X], 0 < f.natDegree → (f.map (Int.castRingHom ℚ)).Separable →
      ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ n < p ∧ ∃ x : ℤ, ((p : ℤ) ^ 2) ∣ f.eval x := by
  intro f hdeg hsep n
  obtain ⟨A, B, N, hN, hAB⟩ := int_bezout_derivative_of_separable f hsep
  obtain ⟨p, hp, hnp, x, hx⟩ := GlobalTheory.T.exists_large_prime_dvd_int_polynomial_eval f hdeg (max n N.natAbs)
  refine ⟨p, hp, lt_of_le_of_lt (le_max_left _ _) hnp, ?_⟩
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hev : A.eval x * f.eval x + B.eval x * (derivative f).eval x = N := by
    have := congrArg (Polynomial.eval x) hAB
    simpa using this
  have hpN : ¬ (p : ℤ) ∣ N := by
    intro h
    have h1 := Int.natAbs_dvd_natAbs.mpr h
    simp only [Int.natAbs_natCast] at h1
    have h2 := Nat.le_of_dvd (Int.natAbs_pos.mpr hN) h1
    have h3 := lt_of_le_of_lt (le_max_right n N.natAbs) hnp
    omega
  have hpd : ¬ (p : ℤ) ∣ (derivative f).eval x := by
    intro h
    apply hpN
    rw [← hev]
    exact dvd_add (dvd_mul_of_dvd_right hx _) (dvd_mul_of_dvd_right h _)
  have hcop : IsCoprime ((derivative f).eval x) (p : ℤ) := by
    rw [isCoprime_comm]
    exact (Prime.coprime_iff_not_dvd hpZ).mpr hpd
  obtain ⟨u, v, huv⟩ := hcop
  obtain ⟨k, hk⟩ := hx
  obtain ⟨K, hK⟩ := Polynomial.binomExpansion f x ((p : ℤ) * (-(k * u)))
  refine ⟨x + (p : ℤ) * (-(k * u)), ?_⟩
  rw [hK, hk]
  refine ⟨k * v + K * (k * u) ^ 2, ?_⟩
  have : k = k * (u * (derivative f).eval x + v * p) := by rw [huv, mul_one]
  linear_combination (p : ℤ) * this
end GlobalTheory
