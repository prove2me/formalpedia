-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_field_nonpositive_gamma_step
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:01:14.916293+00:00
-- url     : https://prove2.me/submissions/24af619b-5cc0-4b18-aa54-870ed83c2d0a

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
set_option autoImplicit false
open KSATSingleFlip.Connect

theorem solution (m h γ : ℝ) (hm : 0 ≤ m) (hh : c0*m ≤ h) (hγ : γ ≤ 0) :
    m + 1/2 ≤ Real.exp (-γ)*Real.exp h := by
  have hr : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hr2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hc : (4/5:ℝ) ≤ c0 := by unfold c0; nlinarith
  have hh' : (4/5:ℝ)*m ≤ h := by nlinarith [mul_nonneg (sub_nonneg.mpr hc) hm]
  have hp : 0 ≤ h := by nlinarith
  have he := Real.add_one_le_exp (h/2)
  have he0 : 0 ≤ Real.exp (h/2) := le_of_lt (Real.exp_pos _)
  have heq : Real.exp h = (Real.exp (h/2))^2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hs : (1+h/2)^2 ≤ Real.exp h := by rw [heq]; nlinarith
  have hsq : ((4/5:ℝ)*m)^2 ≤ h^2 := by nlinarith [sq_nonneg (h-(4/5:ℝ)*m)]
  have hscalar : m+1/2 ≤ Real.exp h := by
    nlinarith [sq_nonneg (m-1)]
  have hb : 1 ≤ Real.exp (-γ) := Real.one_le_exp_iff.mpr (by linarith)
  have hepos : 0 ≤ Real.exp h := le_of_lt (Real.exp_pos _)
  have hp' : Real.exp h ≤ Real.exp (-γ)*Real.exp h := by nlinarith [mul_nonneg (show 0 ≤ Real.exp (-γ)-1 by linarith) hepos]
  exact hscalar.trans hp'
