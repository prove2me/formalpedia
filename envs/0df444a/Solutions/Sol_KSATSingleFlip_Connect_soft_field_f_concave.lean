-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_field_f_concave
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:14:21.893973+00:00
-- url     : https://prove2.me/submissions/fc0e976e-01a9-4b57-ae2a-0a0f0ccdd670

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
set_option autoImplicit false
open KSATSingleFlip.Connect Set

theorem solution : ConcaveOn ℝ (Icc 0 1) fW ∧ fW 0 = 0 ∧ fW 1 = 0 := by
  refine ⟨⟨convex_Icc 0 1, ?_⟩, ?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    have hx' : 0 ≤ x*(1-x) := mul_nonneg hx.1 (by linarith [hx.2])
    have hy' : 0 ≤ y*(1-y) := mul_nonneg hy.1 (by linarith [hy.2])
    have hs := Real.strictConcaveOn_sqrt.concaveOn.2 hx' hy' ha hb hab
    simp only [smul_eq_mul] at hs ⊢
    have hquad : a*(x*(1-x))+b*(y*(1-y)) ≤ (a*x+b*y)*(1-(a*x+b*y)) := by
      have h := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x-y))
      have hb' : b = 1-a := by linarith
      subst b
      nlinarith [h]
    have hroot := Real.sqrt_le_sqrt hquad
    unfold fW
    linarith
  · simp [fW]
  · simp [fW]
