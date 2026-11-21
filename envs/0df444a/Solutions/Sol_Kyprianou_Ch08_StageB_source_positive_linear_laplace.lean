-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_positive_linear_laplace
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T01:33:42.705555+00:00
-- url     : https://prove2.me/submissions/12b0db72-db0d-458e-8724-1534cc1a2564

import Mathlib
set_option autoImplicit false
open MeasureTheory

theorem solution (θ : ℝ) (hθ : 0 < θ) :
    IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * (2 * x))
      (Set.Ioi (0 : ℝ)) volume ∧
    (∫ x in Set.Ioi (0 : ℝ),
      Real.exp (-(θ * x)) * (2 * x) ∂volume) = 2 / θ ^ 2 := by
  have hθne : θ ≠ 0 := hθ.ne'
  -- Base integrability of `exp (-t) * t` on `Ioi 0`, from the Gamma integral.
  have hbase : IntegrableOn (fun t : ℝ => Real.exp (-t) * t) (Set.Ioi (0 : ℝ)) := by
    have h := Real.GammaIntegral_convergent (s := 2) (by norm_num : (0 : ℝ) < 2)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    norm_num
  -- Scale by θ.
  have hscaled : IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * (θ * x))
      (Set.Ioi (0 : ℝ)) := by
    have h := (integrableOn_Ioi_comp_mul_left_iff (fun t : ℝ => Real.exp (-t) * t) 0 hθ).mpr
      (by simpa using hbase)
    simpa using h
  have hxmul : IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * x) (Set.Ioi (0 : ℝ)) := by
    have h' : IntegrableOn (fun x : ℝ => (1 / θ) * (Real.exp (-(θ * x)) * (θ * x)))
        (Set.Ioi (0 : ℝ)) := hscaled.const_mul (1 / θ)
    refine h'.congr (Filter.Eventually.of_forall fun x => ?_)
    field_simp
  have hInt : IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * (2 * x))
      (Set.Ioi (0 : ℝ)) := by
    have h' : IntegrableOn (fun x : ℝ => (2 : ℝ) * (Real.exp (-(θ * x)) * x))
        (Set.Ioi (0 : ℝ)) := hxmul.const_mul 2
    refine h'.congr (Filter.Eventually.of_forall fun x => ?_)
    ring
  constructor
  · exact hInt
  -- Value of the integral.
  have hval : (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(θ * x)) * x) = (1 / θ) ^ 2 := by
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := θ) (by norm_num) hθ
    have hG : Real.Gamma 2 = 1 := by
      simpa using Real.Gamma_nat_eq_factorial 1
    rw [hG, mul_one] at h
    rw [Real.rpow_two] at h
    rw [← h]
    apply integral_congr_ae
    filter_upwards with x
    have hx : x ^ ((2 : ℝ) - 1) = x := by
      rw [show (2 : ℝ) - 1 = 1 by norm_num]
      rw [Real.rpow_one]
    rw [hx]
    ring
  calc (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(θ * x)) * (2 * x))
      = ∫ x in Set.Ioi (0 : ℝ), (2 : ℝ) * (Real.exp (-(θ * x)) * x) := by
        apply integral_congr_ae
        filter_upwards with x
        ring
    _ = (2 : ℝ) * ∫ x in Set.Ioi (0 : ℝ), Real.exp (-(θ * x)) * x :=
        integral_const_mul 2 _
    _ = (2 : ℝ) * (1 / θ) ^ 2 := by rw [hval]
    _ = 2 / θ ^ 2 := by ring
