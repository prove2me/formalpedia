-- Prove2me | solution 1 for LiouvilleDiffAlg.inv_X_sq_add_one_no_antideriv
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-01T13:15:38.228068+00:00
-- url     : https://prove2.me/submissions/76b3bcf2-1faa-42bd-8377-cc2db1e101fc

import Mathlib
import Definitions.Def_LiouvilleDiffAlg_RatFunc

open scoped Differential
open LiouvilleDiffAlg

attribute [local instance 2000] Ring.toIntAlgebra

theorem solution [Differential (RatFunc ℂ)] (hD : IsStandardDerivation) :
    ¬ ∃ g : RatFunc ℂ, g′ = 1 / (RatFunc.X ^ 2 + 1) := by
  rintro ⟨g, hg⟩
  set a := g.num with ha
  set b := g.denom with hb
  have hb0 : b ≠ 0 := g.denom_ne_zero
  have hden : algebraMap (Polynomial ℂ) (RatFunc ℂ) b ≠ 0 := by
    rw [map_ne_zero_iff _ (RatFunc.algebraMap_injective ℂ)]
    exact hb0
  set Q : Polynomial ℂ := Polynomial.X ^ 2 + 1 with hQdef
  have hιQ : algebraMap (Polynomial ℂ) (RatFunc ℂ) Q = RatFunc.X ^ 2 + 1 := by
    simp [hQdef, RatFunc.algebraMap_X]
  have hQ0 : (RatFunc.X ^ 2 + 1 : RatFunc ℂ) ≠ 0 := by
    rw [← hιQ, map_ne_zero_iff _ (RatFunc.algebraMap_injective ℂ)]
    intro h0
    have := congrArg (fun p => Polynomial.coeff p 0) h0
    simp [hQdef] at this
  have h0 : g * algebraMap _ (RatFunc ℂ) b = algebraMap _ (RatFunc ℂ) a := by
    have := RatFunc.num_div_denom g
    rw [div_eq_iff hden] at this
    exact this.symm
  have h1 := congrArg (fun y => y′) h0
  simp only [Derivation.leibniz, smul_eq_mul] at h1
  rw [hD b, hD a, hg] at h1
  have hX1 : (RatFunc.X ^ 2 + 1 : RatFunc ℂ) * (1 / (RatFunc.X ^ 2 + 1)) = 1 :=
    mul_one_div_cancel hQ0
  -- polynomial identity `b * b = Q * (a' * b - a * b')`
  set r : RatFunc ℂ := 1 / (RatFunc.X ^ 2 + 1) with hr
  have h2 : algebraMap _ (RatFunc ℂ) (b * b) =
      algebraMap _ (RatFunc ℂ) (Q * (Polynomial.derivative a * b - a * Polynomial.derivative b)) := by
    rw [map_mul, map_mul, map_sub, map_mul, map_mul, hιQ]
    linear_combination ((RatFunc.X ^ 2 + 1 : RatFunc ℂ) * algebraMap (Polynomial ℂ) (RatFunc ℂ) b) * h1 -
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) b) ^ 2 * hX1 -
      (RatFunc.X ^ 2 + 1 : RatFunc ℂ) * (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (Polynomial.derivative b) * h0
  have h3 : b * b = Q * (Polynomial.derivative a * b - a * Polynomial.derivative b) :=
    RatFunc.algebraMap_injective ℂ h2
  -- factor `Q = p * q`
  set p : Polynomial ℂ := Polynomial.X - Polynomial.C Complex.I with hp
  set q : Polynomial ℂ := Polynomial.X + Polynomial.C Complex.I with hq
  have hQpq : Q = p * q := by
    simp only [hQdef, hp, hq]
    have : (Polynomial.C Complex.I) * Polynomial.C Complex.I = -1 := by
      rw [← map_mul, Complex.I_mul_I, map_neg, map_one]
    linear_combination this
  have hpp : Prime p := Polynomial.prime_X_sub_C Complex.I
  have hpd : Polynomial.derivative p = 1 := by simp [hp]
  have hpdeg : p.natDegree = 1 := Polynomial.natDegree_X_sub_C Complex.I
  -- `p` does not divide `q` (nor any nonzero constant)
  have hnc : ∀ r : Polynomial ℂ, r ≠ 0 → r.natDegree = 0 → ¬ p ∣ r := by
    intro r hr0 hr hdvd
    have := Polynomial.natDegree_le_of_dvd hdvd hr0
    omega
  have hpq : ¬ p ∣ q := by
    intro hdvd
    have h2I : p ∣ Polynomial.C (2 * Complex.I) := by
      have : Polynomial.C (2 * Complex.I) = q - p := by
        rw [show (2 : ℂ) * Complex.I = Complex.I + Complex.I by ring, map_add]
        simp only [hp, hq]; ring
      rw [this]
      exact dvd_sub hdvd dvd_rfl
    exact hnc _ (by simp [Complex.I_ne_zero]) (Polynomial.natDegree_C _) h2I
  have hpb : p ∣ b := by
    have : p ∣ b * b := ⟨q * (Polynomial.derivative a * b - a * Polynomial.derivative b), by
      rw [h3, hQpq]; ring⟩
    rcases hpp.dvd_or_dvd this with h | h <;> exact h
  have hcop : IsCoprime a b := g.isCoprime_num_denom
  obtain ⟨m, c, hc, hbm⟩ := WfDvdMonoid.max_power_factor hb0 hpp.irreducible
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := by
    rcases m with _ | k
    · exfalso; apply hc; simpa [hbm] using hpb
    · exact ⟨k, rfl⟩
  have hb' : Polynomial.derivative b = ((k + 1 : ℕ) : Polynomial ℂ) * p ^ k * c +
      p ^ (k + 1) * Polynomial.derivative c := by
    rw [hbm, Polynomial.derivative_mul, Polynomial.derivative_pow, hpd]
    simp
  have h4 : p ^ (k + 1) * (p ^ (k + 1) * (c * c)) =
      p ^ (k + 1) * (q * (Polynomial.derivative a * p * c -
        a * (((k + 1 : ℕ) : Polynomial ℂ) * c) - a * p * Polynomial.derivative c)) := by
    have := h3
    rw [hb', hbm, hQpq] at this
    linear_combination this
  have h5 := mul_left_cancel₀ (pow_ne_zero (k + 1) hpp.ne_zero) h4
  have h6 : p ∣ q * (a * (((k + 1 : ℕ) : Polynomial ℂ) * c)) := by
    refine ⟨q * Polynomial.derivative a * c - q * a * Polynomial.derivative c -
      p ^ k * (c * c), ?_⟩
    linear_combination h5
  have hkne : ¬ p ∣ ((k + 1 : ℕ) : Polynomial ℂ) :=
    hnc _ (by exact_mod_cast Nat.succ_ne_zero k) (Polynomial.natDegree_natCast (k + 1))
  have hpa : p ∣ a := by
    rcases hpp.dvd_or_dvd h6 with h | h
    · exact absurd h hpq
    · rcases hpp.dvd_or_dvd h with h' | h'
      · exact h'
      · rcases hpp.dvd_or_dvd h' with h'' | h''
        · exact absurd h'' hkne
        · exact absurd h'' hc
  exact hpp.not_isUnit (hcop.isUnit_of_dvd' hpa hpb)
