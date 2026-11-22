-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m81_tail_kernel_inner_exp_lintegral_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T06:32:43.64981+00:00
-- url     : https://prove2.me/submissions/5ae1281a-1ce8-4c43-ba10-4b1cf5bb7c9d

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (s : ℝ) (hs : 0 < s) (z : ℝ) :
    (∫⁻ y in Ico (0 : ℝ) z, ENNReal.ofReal (Real.exp (-s * y)) ∂volume) =
      (1 - ENNReal.ofReal (Real.exp (-s * z))) / ENNReal.ofReal s := by
  have hs_ne : s ≠ 0 := ne_of_gt hs
  by_cases hz : 0 ≤ z
  · have hCont : Continuous (fun y : ℝ => Real.exp (-s * y)) := by continuity
    have hIntble : IntervalIntegrable (fun y : ℝ => Real.exp (-s * y)) volume 0 z :=
      hCont.intervalIntegrable 0 z
    have hIntegOn := (intervalIntegrable_iff_integrableOn_Ico_of_le hz).mp hIntble
    have hOfReal := ofReal_integral_eq_lintegral_ofReal hIntegOn
      (Filter.Eventually.of_forall (fun y : ℝ => (Real.exp_pos (-s * y)).le))
    have hIIoc : (∫ y in (0 : ℝ)..z, Real.exp (-s * y) ∂volume) =
        ∫ y in Ioc 0 z, Real.exp (-s * y) ∂volume :=
      intervalIntegral.integral_of_le (μ := volume) hz
    have hIocIco : (∫ y in Ioc (0 : ℝ) z, Real.exp (-s * y) ∂volume) =
        ∫ y in Ico 0 z, Real.exp (-s * y) ∂volume :=
      (integral_Ico_eq_integral_Ioc).symm
    have hComp := intervalIntegral.integral_comp_mul_left (a := 0) (b := z)
      Real.exp (neg_ne_zero.mpr hs_ne)
    have hExpInt := integral_exp (a := (-s) * 0) (b := (-s) * z)
    have hVal : (∫ y in Ico 0 z, Real.exp (-s * y) ∂volume) =
        (1 - Real.exp (-s * z)) / s := by
      rw [← hIocIco, ← hIIoc, hComp, hExpInt]
      simp [smul_eq_mul]
      field_simp
      ring
    rw [← hOfReal, hVal]
    have hexpNN : 0 ≤ Real.exp (-s * z) := (Real.exp_pos _).le
    rw [ENNReal.ofReal_div_of_pos hs, ENNReal.ofReal_sub 1 hexpNN, ENNReal.ofReal_one]
  · have hz_le : z ≤ 0 := le_of_not_ge hz
    have hEmpty : Ico (0 : ℝ) z = ∅ := Ico_eq_empty_iff.mpr (not_lt.mpr hz_le)
    rw [hEmpty, setLIntegral_empty]
    have hargNN : 0 ≤ -s * z := by have := mul_nonpos_of_nonneg_of_nonpos hs.le hz_le; linarith
    have h1le : (1 : ℝ) ≤ Real.exp (-s * z) := by have h := Real.add_one_le_exp (-s * z); linarith
    have hENN : (1 : ENNReal) ≤ ENNReal.ofReal (Real.exp (-s * z)) := by
      have h' : ENNReal.ofReal 1 ≤ ENNReal.ofReal (Real.exp (-s * z)) :=
        ENNReal.ofReal_le_ofReal h1le
      rwa [ENNReal.ofReal_one] at h'
    rw [tsub_eq_zero_of_le hENN, div_eq_mul_inv, zero_mul]
