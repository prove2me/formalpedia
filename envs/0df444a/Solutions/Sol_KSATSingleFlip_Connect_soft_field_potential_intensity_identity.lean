-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_field_potential_intensity_identity
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:51:28.638402+00:00
-- url     : https://prove2.me/submissions/352f02d3-f051-4e62-b442-433c27fbcc68

import Theorems.Thm_KSATSingleFlip_Connect_soft_field_mass_identity
import Mathlib
set_option autoImplicit false
open KSATSingleFlip.Connect

private theorem q_reflect (z : ℝ) : qOf (-z) = 1-qOf z := by
  have hp : 0 < Real.exp (2*z) := Real.exp_pos _
  have hp0 : Real.exp (2*z) ≠ 0 := ne_of_gt hp
  have hden : 1+Real.exp (2*z) ≠ 0 := by positivity
  unfold qOf
  rw [show 2*(-z) = -(2*z) by ring, Real.exp_neg]
  field_simp
  ring

private theorem intensity_q (z : ℝ) : 2*Real.cosh z*Real.sqrt (qOf z) = wInt z := by
  let e := Real.exp z
  let w := wInt z
  have he : 0 < e := Real.exp_pos _
  have he0 : e ≠ 0 := ne_of_gt he
  have hw : 0 < w := by dsimp [w,wInt]; positivity
  have hw0 : w ≠ 0 := ne_of_gt hw
  have he2 : Real.exp (2*z) = e^2 := by dsimp [e]; rw [show 2*z = z+z by ring, Real.exp_add]; ring
  have hw2 : w^2=1+e^2 := by dsimp [w,wInt]; rw [Real.sq_sqrt (by positivity), he2]
  have hq : qOf z=e^2/(1+e^2) := by simp [qOf,he2]
  have hqpos : 0 < qOf z := (soft_field_mass_identity z).1
  have hsq : (Real.sqrt (qOf z))^2 = qOf z := Real.sq_sqrt (le_of_lt hqpos)
  have hroot : Real.sqrt (qOf z) = e/w := by
    have hroot2 : (e/w)^2 = qOf z := by rw [hq,←hw2]; field_simp
    have hh : 0 ≤ e/w := by positivity
    nlinarith [Real.sqrt_nonneg (qOf z)]
  rw [hroot, Real.cosh_eq, Real.exp_neg]
  change 2*((e+e⁻¹)/2)*(e/w) = w
  field_simp
  nlinarith [hw2]

theorem solution (z : ℝ) :
    Real.cosh z * gW (qOf z) = wInt z+wInt (-z)-2*Real.cosh z := by
  have h1 := intensity_q z
  have h2 := intensity_q (-z)
  rw [q_reflect, Real.cosh_neg] at h2
  unfold gW
  nlinarith [h1,h2]
