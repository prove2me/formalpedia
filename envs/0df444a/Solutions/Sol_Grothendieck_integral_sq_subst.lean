-- Prove2me | solution 1 for Grothendieck.integral_sq_subst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:54:20.390208+00:00
-- url     : https://prove2.me/submissions/0f3a4f95-10eb-4a3d-bb6d-bd0b01a4a6a7

import Mathlib

set_option autoImplicit false

open MeasureTheory intervalIntegral
open scoped BigOperators Real Topology

/-- Derivative of `q ↦ q²/(1+q²)`. -/
theorem hasDerivAt_sq_div_one_add_sq' (q : ℝ) :
    HasDerivAt (fun q : ℝ => q ^ 2 / (1 + q ^ 2)) (2 * q / (1 + q ^ 2) ^ 2) q := by
  have h1 : (1 + q ^ 2) ≠ 0 := by positivity
  have hnum : HasDerivAt (fun q : ℝ => q ^ 2) (2 * q) q := by
    simpa using hasDerivAt_pow 2 q
  have hden : HasDerivAt (fun q : ℝ => 1 + q ^ 2) (2 * q) q := by
    simpa using (hasDerivAt_pow 2 q).const_add 1
  refine HasDerivAt.congr_deriv (hnum.div hden h1) ?_
  field_simp
  ring

open MeasureTheory intervalIntegral
open scoped BigOperators Real Topology

namespace Grothendieck

/-- **The `q² = x/(1-x)` substitution.** For `M > 1/2` and `|τ| < 1`,
`∫₀^∞ (1+q²)^{1/2-M} (1+(1-τ²)q²)^{-1/2} dq = ½ ∫₀^1 x^{-1/2}(1-x)^{M-3/2}(1-τ²x)^{-1/2} dx`. -/
theorem integral_sq_subst_proof {M τ : ℝ} (hM : 1 / 2 < M) (hτ : |τ| < 1) :
    (∫ q in Set.Ioi (0:ℝ), (1 + q ^ 2) ^ (1 / 2 - M) *
        (1 + (1 - τ ^ 2) * q ^ 2) ^ (-(1 / 2) : ℝ))
      = 1 / 2 * ∫ x in Set.Ioo (0:ℝ) 1,
          x ^ (-(1 / 2) : ℝ) * (1 - x) ^ (M - 3 / 2) * (1 - τ ^ 2 * x) ^ (-(1 / 2) : ℝ) := by
  set f : ℝ → ℝ := fun q => q ^ 2 / (1 + q ^ 2) with hf
  set g : ℝ → ℝ := fun x => (1 / 2 : ℝ) * x ^ (-(1 / 2) : ℝ) * (1 - x) ^ (M - 3 / 2) *
    (1 - τ ^ 2 * x) ^ (-(1 / 2) : ℝ) with hg
  have hτ2 : τ ^ 2 < 1 := by
    have := abs_lt.mp hτ
    nlinarith
  -- range and injectivity of `f` on `(0,∞)`
  have himg : f '' Set.Ioi (0:ℝ) = Set.Ioo (0:ℝ) 1 := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      have hq0 : (0:ℝ) < q := hq
      have hpos : 0 < 1 + q ^ 2 := by positivity
      exact ⟨div_pos (by positivity) hpos, by rw [div_lt_one hpos]; linarith⟩
    · rintro ⟨hx0, hx1⟩
      refine ⟨Real.sqrt (x / (1 - x)), ?_, ?_⟩
      · exact Real.sqrt_pos.mpr (div_pos hx0 (by linarith))
      · have h1 : (0:ℝ) < 1 - x := by linarith
        have hs : Real.sqrt (x / (1 - x)) ^ 2 = x / (1 - x) :=
          Real.sq_sqrt (le_of_lt (div_pos hx0 h1))
        show (Real.sqrt (x / (1 - x))) ^ 2 / (1 + (Real.sqrt (x / (1 - x))) ^ 2) = x
        rw [hs]
        field_simp
        ring
  have hinj : Set.InjOn f (Set.Ioi (0:ℝ)) := by
    intro a ha b hb hab
    have ha0 : (0:ℝ) < a := ha
    have hb0 : (0:ℝ) < b := hb
    have hpa : (0:ℝ) < 1 + a ^ 2 := by positivity
    have hpb : (0:ℝ) < 1 + b ^ 2 := by positivity
    simp only [hf] at hab
    rw [div_eq_div_iff hpa.ne' hpb.ne'] at hab
    have hsq : a ^ 2 = b ^ 2 := by nlinarith
    nlinarith [ha0, hb0, hsq]
  -- move the constant `1/2` inside `g`
  have hR : 1 / 2 * ∫ x in Set.Ioo (0:ℝ) 1,
        x ^ (-(1 / 2) : ℝ) * (1 - x) ^ (M - 3 / 2) * (1 - τ ^ 2 * x) ^ (-(1 / 2) : ℝ)
      = ∫ x in Set.Ioo (0:ℝ) 1, g x := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo (fun x _ => ?_)
    simp only [hg]
    ring
  rw [hR, ← himg,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun q _ => (hasDerivAt_sq_div_one_add_sq' q).hasDerivWithinAt) hinj g]
  refine setIntegral_congr_fun measurableSet_Ioi (fun q hq => ?_)
  have hq0 : (0:ℝ) < q := hq
  have hpos : (0:ℝ) < 1 + q ^ 2 := by positivity
  have hB : (0:ℝ) < 1 + (1 - τ ^ 2) * q ^ 2 := by
    have h1 : 0 < 1 - τ ^ 2 := by linarith
    positivity
  have hcompl1 : (1:ℝ) - q ^ 2 / (1 + q ^ 2) = 1 / (1 + q ^ 2) := by
    field_simp
    ring
  have hcompl2 : (1:ℝ) - τ ^ 2 * (q ^ 2 / (1 + q ^ 2))
      = (1 + (1 - τ ^ 2) * q ^ 2) / (1 + q ^ 2) := by
    field_simp
    ring
  have hpow1 : (q ^ 2 / (1 + q ^ 2)) ^ (-(1/2) : ℝ) = q ^ (-1 : ℝ) * (1 + q ^ 2) ^ (1/2 : ℝ) := by
    rw [Real.div_rpow (le_of_lt (pow_pos hq0 2)) (le_of_lt hpos)]
    have hnum : (q ^ 2) ^ (-(1/2) : ℝ) = q ^ (-1 : ℝ) := by
      have h2 : q ^ 2 = q * q := by ring
      rw [h2, Real.mul_rpow (le_of_lt hq0) (le_of_lt hq0), ← Real.rpow_add hq0]
      norm_num
    rw [hnum, div_eq_mul_inv, Real.rpow_neg (le_of_lt hpos), inv_inv]
  have hpow2 : (1 / (1 + q ^ 2)) ^ (M - 3/2) = (1 + q ^ 2) ^ (3/2 - M) := by
    rw [one_div, Real.inv_rpow (le_of_lt hpos), ← Real.rpow_neg (le_of_lt hpos)]
    congr 1
    ring
  have hpow3 : ((1 + (1 - τ ^ 2) * q ^ 2) / (1 + q ^ 2)) ^ (-(1/2) : ℝ)
      = (1 + q ^ 2) ^ (1/2 : ℝ) * (1 + (1 - τ ^ 2) * q ^ 2) ^ (-(1/2) : ℝ) := by
    rw [Real.div_rpow (le_of_lt hB) (le_of_lt hpos), div_eq_mul_inv,
      Real.rpow_neg (le_of_lt hpos), inv_inv, mul_comm]
  have habs : |2 * q / (1 + q ^ 2) ^ 2| = 2 * q * (1 + q ^ 2) ^ (-(2) : ℝ) := by
    rw [abs_of_pos (by positivity : (0:ℝ) < 2 * q / (1 + q ^ 2) ^ 2), div_eq_mul_inv,
      Real.rpow_neg (le_of_lt hpos), Real.rpow_two]
  simp only [hg, smul_eq_mul, habs, hcompl1, hcompl2, hpow1, hpow2, hpow3]
  have hqq : q ^ (-1 : ℝ) * q = 1 := by
    rw [Real.rpow_neg_one]
    field_simp
  have hpow : (1 + q ^ 2) ^ (-(2) : ℝ) *
      ((1 + q ^ 2) ^ (1/2 : ℝ) * ((1 + q ^ 2) ^ (3/2 - M) * (1 + q ^ 2) ^ (1/2 : ℝ)))
      = (1 + q ^ 2) ^ (1/2 - M) := by
    rw [← Real.rpow_add hpos, ← Real.rpow_add hpos, ← Real.rpow_add hpos]
    congr 1
    ring
  have hmain : 2 * q * (1 + q ^ 2) ^ (-(2) : ℝ) *
        (1 / 2 * (q ^ (-1 : ℝ) * (1 + q ^ 2) ^ (1/2 : ℝ)) * (1 + q ^ 2) ^ (3/2 - M) *
          ((1 + q ^ 2) ^ (1/2 : ℝ) * (1 + (1 - τ ^ 2) * q ^ 2) ^ (-(1/2) : ℝ)))
      = (q ^ (-1 : ℝ) * q) * ((1 + q ^ 2) ^ (-(2) : ℝ) *
          ((1 + q ^ 2) ^ (1/2 : ℝ) * ((1 + q ^ 2) ^ (3/2 - M) * (1 + q ^ 2) ^ (1/2 : ℝ)))) *
          (1 + (1 - τ ^ 2) * q ^ 2) ^ (-(1/2) : ℝ) := by ring
  rw [hmain, hqq, hpow, one_mul]

end Grothendieck

open MeasureTheory in
open Grothendieck in
theorem solution {M τ : ℝ} (hM : 1 / 2 < M) (hτ : |τ| < 1) :
    (∫ q in Set.Ioi (0:ℝ), (1 + q ^ 2) ^ (1 / 2 - M) *
        (1 + (1 - τ ^ 2) * q ^ 2) ^ (-(1 / 2) : ℝ))
      = 1 / 2 * ∫ x in Set.Ioo (0:ℝ) 1,
          x ^ (-(1 / 2) : ℝ) * (1 - x) ^ (M - 3 / 2) * (1 - τ ^ 2 * x) ^ (-(1 / 2) : ℝ) :=
  integral_sq_subst_proof hM hτ
