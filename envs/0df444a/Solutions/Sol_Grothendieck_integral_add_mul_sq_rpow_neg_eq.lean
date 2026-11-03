-- Prove2me | solution 1 for Grothendieck.integral_add_mul_sq_rpow_neg_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T03:26:41.03485+00:00
-- url     : https://prove2.me/submissions/841bef55-3f39-4b2c-b56a-0ced18789633

import Mathlib

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators Real Topology

namespace Grothendieck

/-- **Scaling step of the `p`-integral.** For `A, B > 0`,
`∫₀^∞ (A + B p²)^{-M} dp = √(A/B) · A^{-M} · ∫₀^∞ (1 + t²)^{-M} dt`. -/
theorem integral_add_mul_sq_rpow_neg_eq_proof {A B M : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (∫ p in Set.Ioi (0:ℝ), (A + B * p ^ 2) ^ (-M))
      = Real.sqrt (A / B) * A ^ (-M) *
          ∫ t in Set.Ioi (0:ℝ), (1 + t ^ 2) ^ (-M) := by
  have hb : (0:ℝ) < Real.sqrt (A / B) := Real.sqrt_pos.mpr (div_pos hA hB)
  have hb2 : Real.sqrt (A / B) ^ 2 = A / B := Real.sq_sqrt (le_of_lt (div_pos hA hB))
  have hkey := integral_comp_mul_left_Ioi (fun p : ℝ => (A + B * p ^ 2) ^ (-M)) (0:ℝ) hb
  -- `hkey : ∫ x in Ioi 0, (A + B*(√(A/B)*x)^2)^(-M) = (√(A/B))⁻¹ • ∫ x in Ioi (√(A/B)*0), ...`
  rw [mul_zero, smul_eq_mul] at hkey
  have hpt : ∀ x : ℝ, (A + B * (Real.sqrt (A / B) * x) ^ 2) ^ (-M)
      = A ^ (-M) * (1 + x ^ 2) ^ (-M) := by
    intro x
    have hBsq : B * (Real.sqrt (A / B) * x) ^ 2 = A * x ^ 2 := by
      rw [mul_pow, hb2]; field_simp
    rw [hBsq]
    have hfac : A + A * x ^ 2 = A * (1 + x ^ 2) := by ring
    rw [hfac, Real.mul_rpow (le_of_lt hA) (by positivity)]
  simp only [hpt] at hkey
  rw [integral_const_mul] at hkey
  -- `hkey : A^(-M) * ∫ x in Ioi 0, (1+x^2)^(-M) = (√(A/B))⁻¹ * ∫ x in Ioi 0, (A + B*x^2)^(-M)`
  have hfac : Real.sqrt (A / B) * (Real.sqrt (A / B))⁻¹ = 1 := mul_inv_cancel₀ hb.ne'
  calc (∫ p in Set.Ioi (0:ℝ), (A + B * p ^ 2) ^ (-M))
      = Real.sqrt (A / B) * ((Real.sqrt (A / B))⁻¹ *
          ∫ p in Set.Ioi (0:ℝ), (A + B * p ^ 2) ^ (-M)) := by
        rw [← mul_assoc, hfac, one_mul]
    _ = Real.sqrt (A / B) * (A ^ (-M) * ∫ t in Set.Ioi (0:ℝ), (1 + t ^ 2) ^ (-M)) := by
        rw [hkey]
    _ = Real.sqrt (A / B) * A ^ (-M) * ∫ t in Set.Ioi (0:ℝ), (1 + t ^ 2) ^ (-M) := by ring

end Grothendieck

open MeasureTheory in
open Grothendieck in
theorem solution {A B M : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (∫ p in Set.Ioi (0:ℝ), (A + B * p ^ 2) ^ (-M))
      = Real.sqrt (A / B) * A ^ (-M) *
          ∫ t in Set.Ioi (0:ℝ), (1 + t ^ 2) ^ (-M) :=
  integral_add_mul_sq_rpow_neg_eq_proof hA hB
