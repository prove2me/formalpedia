-- Prove2me | solution 1 for LiouvilleDiffAlg.inv_X_no_antideriv
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-01T12:57:00.904754+00:00
-- url     : https://prove2.me/submissions/9bd70f39-d349-4d97-8dee-c09ef4f4bf50

import Mathlib
import Definitions.Def_LiouvilleDiffAlg_RatFunc

open scoped Differential
open LiouvilleDiffAlg

attribute [local instance 2000] Ring.toIntAlgebra

theorem solution [Differential (RatFunc ℂ)] (hD : IsStandardDerivation) :
    ¬ ∃ g : RatFunc ℂ, g′ = 1 / RatFunc.X := by
  rintro ⟨g, hg⟩
  set a := g.num with ha
  set b := g.denom with hb
  have hb0 : b ≠ 0 := g.denom_ne_zero
  have hden : algebraMap (Polynomial ℂ) (RatFunc ℂ) b ≠ 0 := by
    rw [map_ne_zero_iff _ (RatFunc.algebraMap_injective ℂ)]
    exact hb0
  have hX0 : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  have h0 : g * algebraMap _ (RatFunc ℂ) b = algebraMap _ (RatFunc ℂ) a := by
    have := RatFunc.num_div_denom g
    rw [div_eq_iff hden] at this
    exact this.symm
  -- differentiate `g * b = a`
  have h1 := congrArg (fun y => y′) h0
  simp only [Derivation.leibniz, smul_eq_mul] at h1
  rw [hD b, hD a, hg] at h1
  -- polynomial identity `b * b = X * (a' * b - a * b')`
  have hX1 : (RatFunc.X : RatFunc ℂ) * (1 / RatFunc.X) = 1 := mul_one_div_cancel hX0
  have h2 : algebraMap _ (RatFunc ℂ) (b * b) =
      algebraMap _ (RatFunc ℂ) (Polynomial.X * (Polynomial.derivative a * b - a * Polynomial.derivative b)) := by
    rw [map_mul, map_mul, map_sub, map_mul, map_mul, RatFunc.algebraMap_X]
    linear_combination (RatFunc.X * algebraMap (Polynomial ℂ) (RatFunc ℂ) b) * h1 -
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) b) ^ 2 * hX1 -
      RatFunc.X * (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (Polynomial.derivative b) * h0
  have h3 : b * b = Polynomial.X * (Polynomial.derivative a * b - a * Polynomial.derivative b) :=
    RatFunc.algebraMap_injective ℂ h2
  have hXp : Prime (Polynomial.X : Polynomial ℂ) := Polynomial.prime_X
  have hXb : Polynomial.X ∣ b := by
    have : (Polynomial.X : Polynomial ℂ) ∣ b * b := ⟨_, h3⟩
    rcases hXp.dvd_or_dvd this with h | h <;> exact h
  have hcop : IsCoprime a b := g.isCoprime_num_denom
  obtain ⟨m, c, hc, hbm⟩ := WfDvdMonoid.max_power_factor hb0 hXp.irreducible
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := by
    rcases m with _ | k
    · exfalso; apply hc; simpa [hbm] using hXb
    · exact ⟨k, rfl⟩
  -- cancel `X^(k+1)`
  have hb' : Polynomial.derivative b = ((k + 1 : ℕ) : Polynomial ℂ) * Polynomial.X ^ k * c +
      Polynomial.X ^ (k + 1) * Polynomial.derivative c := by
    rw [hbm, Polynomial.derivative_mul, Polynomial.derivative_X_pow]
    simp
  have h4 : Polynomial.X ^ (k + 1) * (Polynomial.X ^ (k + 1) * (c * c)) =
      Polynomial.X ^ (k + 1) * (Polynomial.derivative a * Polynomial.X * c -
        a * (((k + 1 : ℕ) : Polynomial ℂ) * c) - a * Polynomial.X * Polynomial.derivative c) := by
    have := h3
    rw [hb', hbm] at this
    linear_combination this
  have h5 := mul_left_cancel₀ (pow_ne_zero (k + 1) Polynomial.X_ne_zero) h4
  have h6 : (Polynomial.X : Polynomial ℂ) ∣ a * (((k + 1 : ℕ) : Polynomial ℂ) * c) := by
    have h7 : a * (((k + 1 : ℕ) : Polynomial ℂ) * c) = Polynomial.X * (Polynomial.derivative a * c -
        a * Polynomial.derivative c - Polynomial.X ^ k * (c * c)) := by
      linear_combination h5
    exact ⟨_, h7⟩
  have hkne : ¬ (Polynomial.X : Polynomial ℂ) ∣ ((k + 1 : ℕ) : Polynomial ℂ) := by
    rw [Polynomial.X_dvd_iff]
    simp [Polynomial.coeff_natCast_ite]
    exact_mod_cast Nat.succ_ne_zero k
  have hXa : Polynomial.X ∣ a := by
    rcases hXp.dvd_or_dvd h6 with h | h
    · exact h
    · rcases hXp.dvd_or_dvd h with h' | h'
      · exact absurd h' hkne
      · exact absurd h' hc
  exact hXp.not_isUnit (hcop.isUnit_of_dvd' hXa hXb)
