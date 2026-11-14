-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_field_large_mass_growth
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:17:48.144935+00:00
-- url     : https://prove2.me/submissions/f2a807b9-3a91-4505-9666-2c37a7ba962a

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
set_option autoImplicit false
open KSATSingleFlip.Connect

theorem solution (m h γ : ℝ) (hm : 8 ≤ m) (hh : c0*m ≤ h) (hγ : γ ≤ 1) :
    m + 1 ≤ Real.exp (-γ)*Real.exp h := by
  have hr : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hr2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hc : (4/5:ℝ) ≤ c0 := by unfold c0; nlinarith
  have hh' : (4/5:ℝ)*m ≤ h := by nlinarith [mul_nonneg (sub_nonneg.mpr hc) (show 0 ≤ m by linarith)]
  have hx : 0 ≤ -γ+h := by linarith
  have he := Real.add_one_le_exp ((-γ+h)/2)
  have he0 : 0 ≤ Real.exp ((-γ+h)/2) := le_of_lt (Real.exp_pos _)
  have heq : Real.exp (-γ+h) = (Real.exp ((-γ+h)/2))^2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hs : (1+(-γ+h)/2)^2 ≤ Real.exp (-γ+h) := by rw [heq]; nlinarith
  have ht : (1/2+(2/5:ℝ)*m)^2 ≤ (1+(-γ+h)/2)^2 := by
    have ha : 0 ≤ (1/2+(2/5:ℝ)*m) := by linarith
    have hb : (1/2+(2/5:ℝ)*m) ≤ 1+(-γ+h)/2 := by linarith
    nlinarith
  have hscalar : m+1 ≤ (1/2+(2/5:ℝ)*m)^2 := by nlinarith [sq_nonneg (m-8)]
  rw [← Real.exp_add]
  exact hscalar.trans (ht.trans hs)
