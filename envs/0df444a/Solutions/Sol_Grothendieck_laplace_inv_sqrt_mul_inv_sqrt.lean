-- Prove2me | solution 1 for Grothendieck.laplace_inv_sqrt_mul_inv_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-02T22:18:12.972221+00:00
-- url     : https://prove2.me/submissions/7d46698f-35cf-41dd-beb6-676b2ea2468f

import Mathlib

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators Real Topology

namespace Grothendieck

/-- The one-dimensional Laplace identity `∫_0^∞ u^{-1/2} e^{-Cu} du = √π/√C`. -/
theorem integral_rpow_neg_half_exp_mul {C : ℝ} (hC : 0 < C) :
    (∫ u in Set.Ioi (0:ℝ), u ^ (-(1/2) : ℝ) * Real.exp (-(C * u)))
      = Real.sqrt Real.pi / Real.sqrt C := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (1/2:ℝ)) (r := C) (by norm_num) hC
  have h1 : ((1/2:ℝ) - 1) = -(1/2) := by norm_num
  rw [h1, Real.Gamma_one_half_eq] at h
  rw [h, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    Real.div_rpow zero_le_one (le_of_lt hC), Real.one_rpow, one_div, div_eq_mul_inv]
  ring_nf

/-- **The Laplace step.** For `A, B > 0`,
`1/(√A √B) = π⁻¹ ∫∫_{(0,∞)²} (st)^{-1/2} e^{-(sA+tB)} ds dt`. -/
theorem laplace_inv_sqrt_mul_inv_sqrt_proof {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (Real.sqrt A * Real.sqrt B)⁻¹
      = Real.pi⁻¹ * ∫ s in Set.Ioi (0:ℝ), ∫ t in Set.Ioi (0:ℝ),
          (s * t) ^ (-(1/2) : ℝ) * Real.exp (-(s * A + t * B)) := by
  have hI : ∀ C : ℝ, 0 < C →
      (∫ u in Set.Ioi (0:ℝ), u ^ (-(1/2) : ℝ) * Real.exp (-(C * u)))
        = Real.sqrt Real.pi / Real.sqrt C := fun C hC => integral_rpow_neg_half_exp_mul hC
  have hinner : ∀ s ∈ Set.Ioi (0:ℝ),
      (∫ t in Set.Ioi (0:ℝ), (s * t) ^ (-(1/2) : ℝ) * Real.exp (-(s * A + t * B)))
        = (s ^ (-(1/2) : ℝ) * Real.exp (-(A * s))) * (Real.sqrt Real.pi / Real.sqrt B) := by
    intro s hs
    have hs0 : (0:ℝ) < s := hs
    have hpt : ∀ t ∈ Set.Ioi (0:ℝ),
        (s * t) ^ (-(1/2) : ℝ) * Real.exp (-(s * A + t * B))
          = (s ^ (-(1/2) : ℝ) * Real.exp (-(A * s))) * (t ^ (-(1/2) : ℝ) * Real.exp (-(B * t))) := by
      intro t ht
      have ht0 : (0:ℝ) < t := ht
      have e1 : -(s * A + t * B) = -(A * s) + -(B * t) := by ring
      rw [Real.mul_rpow (le_of_lt hs0) (le_of_lt ht0), e1, Real.exp_add]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, hI B hB]
  rw [setIntegral_congr_fun measurableSet_Ioi hinner, integral_mul_const, hI A hA]
  have hsq : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := by
    rw [← sq, Real.sq_sqrt (le_of_lt Real.pi_pos)]
  have hp : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  have hA0 : Real.sqrt A ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hA)
  have hB0 : Real.sqrt B ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hB)
  field_simp
  rw [Real.sq_sqrt (le_of_lt Real.pi_pos)]

end Grothendieck

open MeasureTheory in
open Grothendieck in
theorem solution {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (Real.sqrt A * Real.sqrt B)⁻¹
      = Real.pi⁻¹ * ∫ s in Set.Ioi (0:ℝ), ∫ t in Set.Ioi (0:ℝ),
          (s * t) ^ (-(1/2) : ℝ) * Real.exp (-(s * A + t * B)) :=
  laplace_inv_sqrt_mul_inv_sqrt_proof hA hB
