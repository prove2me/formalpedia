-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_field_weight_bounds
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:14:21.866712+00:00
-- url     : https://prove2.me/submissions/bb3ad530-4143-424e-b94b-d6cb55e2fc75

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
set_option autoImplicit false
open KSATSingleFlip.Connect

theorem solution (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ gW q ∧ gW q ≤ fW q ∧ fW q ≤ 1 := by
  have h1q : 0 ≤ 1-q := by linarith
  have hs : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
  have ht : 0 ≤ Real.sqrt (1-q) := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt q)^2 = q := Real.sq_sqrt hq
  have ht2 : (Real.sqrt (1-q))^2 = 1-q := Real.sq_sqrt h1q
  have hs1 : Real.sqrt q ≤ 1 := Real.sqrt_le_one.mpr hq1
  have ht1 : Real.sqrt (1-q) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hsge : q ≤ Real.sqrt q := by nlinarith [mul_nonneg hs (show 0 ≤ 1-Real.sqrt q by linarith)]
  have htge : 1-q ≤ Real.sqrt (1-q) := by nlinarith [mul_nonneg ht (show 0 ≤ 1-Real.sqrt (1-q) by linarith)]
  have hroot : Real.sqrt (q*(1-q)) = Real.sqrt q * Real.sqrt (1-q) := Real.sqrt_mul hq _
  constructor
  · unfold gW; linarith
  constructor
  · unfold gW fW
    rw [hroot]
    nlinarith [mul_nonneg (show 0 ≤ 1-Real.sqrt q by linarith) (show 0 ≤ 1-Real.sqrt (1-q) by linarith)]
  · unfold fW
    rw [hroot]
    nlinarith [sq_nonneg (Real.sqrt q-Real.sqrt (1-q))]
