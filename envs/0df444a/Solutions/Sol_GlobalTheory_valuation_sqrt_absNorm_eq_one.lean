-- Prove2me | solution 1 for GlobalTheory.valuation_sqrt_absNorm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:55:23.991077+00:00
-- url     : https://prove2.me/submissions/12f373d3-1520-4c18-9890-8fa1fc24801c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValuationSqrtAbsNormEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K] [NumberField K] (A : ValuationSubring ℂ) (p : ℕ), p.Prime →
      (p : ℂ) ∈ A.nonunits → ∀ (P : HeightOneSpectrum (𝓞 K)), (p : 𝓞 K) ∉ P.asIdeal →
        A.valuation (((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ)) = 1 := by
  intro K _ _ A p hp hpA P hpP
  set N : ℕ := Ideal.absNorm P.asIdeal with hNdef

  have hNcard : N = Nat.card (𝓞 K ⧸ P.asIdeal) := by
    rw [hNdef, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hN0 : N ≠ 0 := by
    rw [hNdef, Ne, Ideal.absNorm_eq_zero_iff]; exact P.ne_bot
  have hpN : ¬ p ∣ N := by
    intro hdvd
    haveI : Finite (𝓞 K ⧸ P.asIdeal) := Nat.finite_of_card_ne_zero (hNcard ▸ hN0)
    haveI : Fact p.Prime := ⟨hp⟩
    letI : Field (𝓞 K ⧸ P.asIdeal) := Ideal.Quotient.field _
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 K ⧸ P.asIdeal) p (hNcard ▸ hdvd)
    have hx0 : x ≠ 0 := by
      rintro rfl; rw [addOrderOf_zero] at hx; exact hp.one_lt.ne' hx.symm
    have hpx : (p : 𝓞 K ⧸ P.asIdeal) * x = 0 := by
      rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
    have hp0 : (p : 𝓞 K ⧸ P.asIdeal) = 0 := (mul_eq_zero.mp hpx).resolve_right hx0
    apply hpP
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact hp0
  have hcop : Nat.Coprime N p := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpN))

  have hbez : (N : ℤ) * Nat.gcdA N p + (p : ℤ) * Nat.gcdB N p = 1 := by
    have := Nat.gcd_eq_gcd_ab N p
    rw [hcop] at this; simpa using this.symm
  have hbezA : ((N : A) * ((Nat.gcdA N p : ℤ) : A)) + ((p : A) * ((Nat.gcdB N p : ℤ) : A)) = 1 := by
    have := congrArg (Int.cast : ℤ → A) hbez
    push_cast at this; exact this
  have hpnu : ¬ IsUnit (p : A) := by
    rw [ValuationSubring.valuation_eq_one_iff]
    have := (ValuationSubring.mem_nonunits_iff A).mp hpA
    push_cast; exact this.ne
  have hNu : IsUnit (N : A) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one hbezA with h | h
    · exact isUnit_of_mul_isUnit_left h
    · exact absurd (isUnit_of_mul_isUnit_left h) hpnu
  have hvN : A.valuation (N : ℂ) = 1 := by
    have := (ValuationSubring.valuation_eq_one_iff A _).mp hNu
    push_cast at this; exact this

  have hsq : ((Real.sqrt N : ℝ) : ℂ) ^ 2 = (N : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  have h2 : A.valuation ((Real.sqrt N : ℝ) : ℂ) ^ 2 = 1 := by
    rw [← map_pow, hsq, hvN]
  rcases lt_trichotomy (A.valuation ((Real.sqrt N : ℝ) : ℂ)) 1 with h | h | h
  · exact absurd h2 (pow_lt_one₀ zero_le' h two_ne_zero).ne
  · exact h
  · exact absurd h2 (one_lt_pow₀ h two_ne_zero).ne'
end GlobalTheory
