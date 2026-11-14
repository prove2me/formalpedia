-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_field_tilt_identities
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:51:28.465837+00:00
-- url     : https://prove2.me/submissions/4467de26-4872-4e8f-9091-d814f172f3fa

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
set_option autoImplicit false
open KSATSingleFlip.Connect

theorem solution (z : ℝ) :
    wInt z * Real.exp (aShift z) = 2*Real.cosh z ∧
    wInt z * Real.exp (-aShift z) = Real.exp z := by
  let e := Real.exp z
  let w := wInt z
  let A := Real.exp (aShift z)
  have he : 0 < e := Real.exp_pos _
  have he0 : e ≠ 0 := ne_of_gt he
  have hw : 0 < w := by dsimp [w,wInt]; positivity
  have hw0 : w ≠ 0 := ne_of_gt hw
  have hA : 0 < A := Real.exp_pos _
  have hA0 : A ≠ 0 := ne_of_gt hA
  have he2 : Real.exp (2*z) = e^2 := by dsimp [e]; rw [show 2*z = z+z by ring, Real.exp_add]; ring
  have hneg2 : Real.exp (-2*z) = (e^2)⁻¹ := by
    rw [show -2*z = -(2*z) by ring, Real.exp_neg, he2]
  have hw2 : w^2 = 1+e^2 := by dsimp [w,wInt]; rw [Real.sq_sqrt (by positivity), he2]
  have hA2 : A^2 = 1+(e^2)⁻¹ := by
    dsimp [A,aShift]
    rw [show (1/2:ℝ)*Real.log (1+Real.exp (-2*z)) = Real.log (1+Real.exp (-2*z))/2 by ring, Real.exp_half, Real.sq_sqrt (by positivity), Real.exp_log (by positivity), hneg2]
  have hprod2 : (w*A)^2 = (e+e⁻¹)^2 := by
    rw [mul_pow, hw2, hA2]
    field_simp
    ring
  have hprod : w*A = e+e⁻¹ := by
    have hi : 0 < e⁻¹ := inv_pos.mpr he
    nlinarith [hprod2, mul_pos hw hA]
  have heAw : e*A = w := by
    have hh := congrArg (fun x : ℝ => e*x) hprod
    field_simp at hh
    nlinarith [hw2]
  constructor
  · change w*A = 2*Real.cosh z
    rw [Real.cosh_eq, Real.exp_neg]
    change w*A = 2*((e+e⁻¹)/2)
    linarith
  · change w*Real.exp (-aShift z) = e
    rw [Real.exp_neg]
    change w*A⁻¹ = e
    rw [← heAw]
    field_simp
