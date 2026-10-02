-- Prove2me | solution 1 for LiouvilleDiffAlg.constants_ratFunc
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-01T12:39:47.281687+00:00
-- url     : https://prove2.me/submissions/1769c837-a0c6-4763-84a0-4a3e5d9a439d

import Mathlib
import Definitions.Def_LiouvilleDiffAlg_Basic
import Definitions.Def_LiouvilleDiffAlg_RatFunc

open scoped Differential
open LiouvilleDiffAlg

attribute [local instance 2000] Ring.toIntAlgebra

theorem solution [Differential (RatFunc ℂ)] (hD : IsStandardDerivation) :
    constants (RatFunc ℂ) = Set.range (algebraMap ℂ (RatFunc ℂ)) := by
  ext x
  constructor
  · intro hx
    have hx0 : x′ = 0 := hx
    set a := x.num with ha
    set b := x.denom with hb
    have hb0 : b ≠ 0 := x.denom_ne_zero
    have hden : algebraMap (Polynomial ℂ) (RatFunc ℂ) b ≠ 0 := by
      rw [map_ne_zero_iff _ (RatFunc.algebraMap_injective ℂ)]
      exact hb0
    have h0 : x * algebraMap _ (RatFunc ℂ) b = algebraMap _ (RatFunc ℂ) a := by
      have := RatFunc.num_div_denom x
      rw [div_eq_iff hden] at this
      exact this.symm
    -- differentiate `x * b = a`
    have h1 := congrArg (fun y => y′) h0
    simp only [Derivation.leibniz, hx0, smul_eq_mul, zero_mul, add_zero] at h1
    rw [hD b, hD a] at h1
    -- `x * b' = a'` in `ℂ(x)`, hence `a' * b = a * b'` in `ℂ[x]`
    have h2 : algebraMap _ (RatFunc ℂ) (Polynomial.derivative a * b) =
        algebraMap _ (RatFunc ℂ) (a * Polynomial.derivative b) := by
      rw [map_mul, map_mul, ← h1, ← h0]
      ring
    have h3 : Polynomial.derivative a * b = a * Polynomial.derivative b :=
      RatFunc.algebraMap_injective ℂ h2
    -- coprimality gives `b ∣ b'`, hence `b' = 0`
    have hcop : IsCoprime a b := x.isCoprime_num_denom
    have hdvd : b ∣ Polynomial.derivative b := by
      have : b ∣ a * Polynomial.derivative b := ⟨Polynomial.derivative a, by rw [← h3]; ring⟩
      exact (hcop.symm).dvd_of_dvd_mul_left this
    have hb' : Polynomial.derivative b = 0 := by
      by_contra hne
      have hle := Polynomial.natDegree_le_of_dvd hdvd hne
      have hlt : (Polynomial.derivative b).natDegree < b.natDegree := by
        by_cases hb1 : b.natDegree = 0
        · rw [Polynomial.natDegree_eq_zero] at hb1
          obtain ⟨c, hc⟩ := hb1
          rw [← hc] at hne
          simp at hne
        · exact Polynomial.natDegree_derivative_lt hb1
      omega
    have ha' : Polynomial.derivative a = 0 := by
      rw [hb', mul_zero] at h3
      exact (mul_eq_zero.1 h3).resolve_right hb0
    -- both are constant polynomials
    obtain ⟨ca, hca⟩ := Polynomial.natDegree_eq_zero.1
      (Polynomial.natDegree_eq_zero_of_derivative_eq_zero ha')
    obtain ⟨cb, hcb⟩ := Polynomial.natDegree_eq_zero.1
      (Polynomial.natDegree_eq_zero_of_derivative_eq_zero hb')
    have hcb0 : cb ≠ 0 := by
      rintro rfl
      apply hb0
      rw [← hcb]; simp
    refine ⟨ca / cb, ?_⟩
    rw [map_div₀]
    have hxa : x = algebraMap _ (RatFunc ℂ) a / algebraMap _ (RatFunc ℂ) b :=
      (RatFunc.num_div_denom x).symm
    rw [hxa, ← hca, ← hcb]
    simp [RatFunc.algebraMap_C]
  · rintro ⟨c, rfl⟩
    show (algebraMap ℂ (RatFunc ℂ) c)′ = 0
    have h1 := hD (Polynomial.C c)
    rw [RatFunc.algebraMap_C, Polynomial.derivative_C, map_zero] at h1
    exact h1
