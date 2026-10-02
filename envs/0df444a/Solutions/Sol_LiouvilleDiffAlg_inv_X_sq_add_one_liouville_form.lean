-- Prove2me | solution 1 for LiouvilleDiffAlg.inv_X_sq_add_one_liouville_form
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-01T12:14:39.848087+00:00
-- url     : https://prove2.me/submissions/68262121-2d86-49a7-987a-f71595cebe82

import Mathlib
import Definitions.Def_LiouvilleDiffAlg_RatFunc

open scoped Differential
open LiouvilleDiffAlg

theorem solution [Differential (RatFunc ℂ)] (hD : IsStandardDerivation) :
    (1 + algebraMap ℂ (RatFunc ℂ) Complex.I * RatFunc.X) /
        (1 - algebraMap ℂ (RatFunc ℂ) Complex.I * RatFunc.X) ≠ 0 ∧
    1 / (RatFunc.X ^ 2 + 1) =
      algebraMap ℂ (RatFunc ℂ) (1 / (2 * Complex.I)) *
        (((1 + algebraMap ℂ (RatFunc ℂ) Complex.I * RatFunc.X) /
            (1 - algebraMap ℂ (RatFunc ℂ) Complex.I * RatFunc.X))′ /
          ((1 + algebraMap ℂ (RatFunc ℂ) Complex.I * RatFunc.X) /
            (1 - algebraMap ℂ (RatFunc ℂ) Complex.I * RatFunc.X))) := by
  -- notation
  set κ : ℂ →+* RatFunc ℂ := algebraMap ℂ (RatFunc ℂ) with hκ
  set X : RatFunc ℂ := RatFunc.X with hXdef
  have hI2 : κ Complex.I * κ Complex.I = -1 := by
    rw [← map_mul, Complex.I_mul_I, map_neg, map_one]
  -- derivative of constants and of `X`
  have hC : ∀ c : ℂ, (κ c)′ = 0 := by
    intro c
    have h1 := hD (Polynomial.C c)
    rw [RatFunc.algebraMap_C, Polynomial.derivative_C, map_zero] at h1
    exact h1
  have hX : X′ = 1 := by
    have h1 := hD Polynomial.X
    rw [RatFunc.algebraMap_X, Polynomial.derivative_X, map_one] at h1
    exact h1
  -- nonvanishing of `1 ± i X`
  have hpos : (1 + κ Complex.I * X) ≠ 0 := by
    have hp : (1 + Polynomial.C Complex.I * Polynomial.X : Polynomial ℂ) ≠ 0 := by
      intro h0
      have := congrArg (fun p => Polynomial.coeff p 0) h0
      simp at this
    intro h0
    apply hp
    apply RatFunc.algebraMap_injective ℂ
    simpa [hκ, hXdef] using h0
  have hneg : (1 - κ Complex.I * X) ≠ 0 := by
    have hp : (1 - Polynomial.C Complex.I * Polynomial.X : Polynomial ℂ) ≠ 0 := by
      intro h0
      have := congrArg (fun p => Polynomial.coeff p 0) h0
      simp at this
    intro h0
    apply hp
    apply RatFunc.algebraMap_injective ℂ
    simpa [hκ, hXdef] using h0
  refine ⟨div_ne_zero hpos hneg, ?_⟩
  have hd1 : (1 + κ Complex.I * X)′ = κ Complex.I := by
    simp [Derivation.leibniz, hC, hX]
  have hd2 : (1 - κ Complex.I * X)′ = -κ Complex.I := by
    simp [Derivation.leibniz, hC, hX]
  have hdu : ((1 + κ Complex.I * X) / (1 - κ Complex.I * X))′ =
      ((1 - κ Complex.I * X) ^ 2)⁻¹ *
        ((1 - κ Complex.I * X) * κ Complex.I + (1 + κ Complex.I * X) * κ Complex.I) := by
    simp only [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv, hd1, hd2, smul_eq_mul]
    field_simp
    ring
  have hJ : κ Complex.I ≠ 0 := by
    rw [map_ne_zero]; exact Complex.I_ne_zero
  have h2J : κ (2 * Complex.I) = 2 * κ Complex.I := by
    rw [map_mul, map_ofNat]
  have hkey : X ^ 2 + 1 = (1 + κ Complex.I * X) * (1 - κ Complex.I * X) := by
    linear_combination X ^ 2 * hI2
  rw [hdu, hkey, map_div₀, map_one, h2J]
  field_simp
  ring
