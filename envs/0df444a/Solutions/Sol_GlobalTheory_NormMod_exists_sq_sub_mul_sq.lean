-- Prove2me | solution 1 for GlobalTheory.NormMod.exists_sq_sub_mul_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:14:42.302179+00:00
-- url     : https://prove2.me/submissions/f676e224-c30d-4389-a584-19e6d4d7c055

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHostNormModCoprimeLevelHalf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NormMod
variable {R : Type*} [CommRing R] [Finite R]
namespace GlobalTheory.NormMod
theorem _root_.solution {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h0 : (p : R) = 0) {D ν : R}
    (hD : IsUnit D) (hν : IsUnit ν) : ∃ x y : R, x ^ 2 - D * y ^ 2 = ν := by
  obtain ⟨j, hj⟩ := hp.odd_of_ne_two hp2
  have loc : ∀ m : MaximalSpectrum R, ∃ a b : R ⧸ m.asIdeal,
      a ^ 2 - Ideal.Quotient.mk _ D * b ^ 2 = Ideal.Quotient.mk _ ν := by
    intro m
    haveI := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    haveI : Finite (R ⧸ m.asIdeal) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
    letI : Fintype (R ⧸ m.asIdeal) := Fintype.ofFinite _
    have hp0 : (p : R ⧸ m.asIdeal) = 0 := by
      have := congrArg (Ideal.Quotient.mk m.asIdeal) h0
      simpa using this
    have hchar : ringChar (R ⧸ m.asIdeal) ≠ 2 := by
      intro h
      have h2 : ((2 : ℕ) : R ⧸ m.asIdeal) = 0 := by rw [← h]; exact ringChar.Nat.cast_ringChar
      rw [hj] at hp0
      push_cast at hp0 h2
      rw [h2] at hp0
      simp at hp0
    have hD' : Ideal.Quotient.mk m.asIdeal D ≠ 0 := (hD.map _).ne_zero
    obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
      (f := (Polynomial.X ^ 2 : Polynomial (R ⧸ m.asIdeal)))
      (g := Polynomial.C (-Ideal.Quotient.mk m.asIdeal D) * Polynomial.X ^ 2
        + Polynomial.C 0 * Polynomial.X + Polynomial.C (-Ideal.Quotient.mk m.asIdeal ν))
      (Polynomial.degree_X_pow 2) (Polynomial.degree_quadratic (neg_ne_zero.2 hD'))
      (FiniteField.odd_card_of_char_ne_two hchar)
    refine ⟨a, b, ?_⟩
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C] at hab
    linear_combination hab
  choose a b hab using loc
  have hsurj : Function.Surjective
      (fun (x : R) (m : MaximalSpectrum R) => Ideal.Quotient.mk m.asIdeal x) :=
    fun f => by
      obtain ⟨x, hx⟩ := Ideal.pi_quotient_surjective
        (I := fun m : MaximalSpectrum R => m.asIdeal)
        (fun m m' h => MaximalSpectrum.isCoprime_of_ne h) f
      exact ⟨x, funext hx⟩
  obtain ⟨x, hx⟩ := hsurj a
  obtain ⟨y, hy⟩ := hsurj b
  have hnil : IsNilpotent (x ^ 2 - D * y ^ 2 - ν) := by
    rw [nilpotent_iff_mem_prime]
    intro J hJ
    have hm : J.IsMaximal := IsArtinianRing.isMaximal_of_isPrime J
    have := hab ⟨J, hm⟩
    rw [← hx, ← hy] at this
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [map_sub, map_mul, map_pow]
    exact sub_eq_zero.2 this
  obtain ⟨μ, hμ⟩ := hν.exists_right_inv
  obtain ⟨k, hk⟩ := hnil
  set e := μ * (x ^ 2 - D * y ^ 2 - ν) with he
  have hek : e ^ p ^ k = 0 := by
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le (Nat.lt_pow_self (n := k) hp.one_lt).le
    rw [hc, pow_add, he, mul_pow, hk]
    ring
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp (1 : R) e k
  rw [h0, hek] at hr
  obtain ⟨i, hi⟩ := (hp.odd_of_ne_two hp2).pow (n := k)
  rw [hi] at hr
  refine ⟨x * (1 + e) ^ i, y * (1 + e) ^ i, ?_⟩
  have h1 : x ^ 2 - D * y ^ 2 = ν * (1 + e) := by
    rw [he]; linear_combination (-(x ^ 2 - D * y ^ 2 - ν)) * hμ
  linear_combination ((1 + e) ^ i) ^ 2 * h1 + ν * hr
end GlobalTheory.NormMod
