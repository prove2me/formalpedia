-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_field_mass_identity
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:14:21.986587+00:00
-- url     : https://prove2.me/submissions/199d934c-3119-496f-80ec-266c9614a933

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
set_option autoImplicit false
open KSATSingleFlip.Connect

theorem solution (z : ℝ) :
    0 < qOf z ∧ qOf z < 1 ∧ Real.cosh z * fW (qOf z) = 1 := by
  have he : 0 < Real.exp z := Real.exp_pos _
  have he0 : Real.exp z ≠ 0 := ne_of_gt he
  have he2 : Real.exp (2*z) = (Real.exp z)^2 := by
    rw [show 2*z = z+z by ring, Real.exp_add]
    ring
  have hden : 0 < 1+(Real.exp z)^2 := by positivity
  have hden0 : 1+(Real.exp z)^2 ≠ 0 := ne_of_gt hden
  have hq : qOf z = (Real.exp z)^2/(1+(Real.exp z)^2) := by simp [qOf,he2]
  have hqpos : 0 < qOf z := by rw [hq]; positivity
  have hqone : qOf z < 1 := by
    rw [hq]
    apply (div_lt_one₀ hden).2
    linarith
  have hqq : 0 ≤ qOf z * (1-qOf z) := mul_nonneg (le_of_lt hqpos) (by linarith)
  have hs : (Real.sqrt (qOf z*(1-qOf z)))^2 = qOf z*(1-qOf z) := Real.sq_sqrt hqq
  have hroot : Real.sqrt (qOf z*(1-qOf z)) = Real.exp z/(1+(Real.exp z)^2) := by
    have hsq : (Real.exp z/(1+(Real.exp z)^2))^2 = qOf z*(1-qOf z) := by
      rw [hq]
      field_simp
      ring
    have hleft : 0 ≤ Real.sqrt (qOf z*(1-qOf z)) := Real.sqrt_nonneg _
    have hright : 0 ≤ Real.exp z/(1+(Real.exp z)^2) := by positivity
    nlinarith
  refine ⟨hqpos,hqone,?_⟩
  rw [fW, hroot, Real.cosh_eq, Real.exp_neg]
  field_simp
  ring
