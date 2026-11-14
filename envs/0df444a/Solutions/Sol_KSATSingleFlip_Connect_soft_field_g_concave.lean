-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_field_g_concave
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:14:21.863882+00:00
-- url     : https://prove2.me/submissions/b4d5a22b-b39f-497a-88bb-cdb2782e8cc4

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
set_option autoImplicit false
open KSATSingleFlip.Connect Set

theorem solution : ConcaveOn ℝ (Icc 0 1) gW ∧ gW 0 = 0 ∧ gW 1 = 0 := by
  refine ⟨⟨convex_Icc 0 1, ?_⟩, ?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    have hS := Real.strictConcaveOn_sqrt.concaveOn.2 hx.1 hy.1 ha hb hab
    have hx' : 0 ≤ 1-x := by linarith [hx.2]
    have hy' : 0 ≤ 1-y := by linarith [hy.2]
    have hT := Real.strictConcaveOn_sqrt.concaveOn.2 hx' hy' ha hb hab
    have heq : a*(1-x)+b*(1-y) = 1-(a*x+b*y) := by nlinarith
    simp only [smul_eq_mul] at hS hT ⊢
    rw [heq] at hT
    unfold gW
    nlinarith
  · simp [gW]
  · simp [gW]
