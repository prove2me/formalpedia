-- Prove2me | solution 1 for Kyprianou.Ch04.zeroSlopeOfPositiveRoot
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:45:31.208942+00:00
-- url     : https://prove2.me/submissions/7b76f485-92b0-47cb-a43e-b056befe3acd

import Mathlib.Algebra.Order.Archimedean.Real.Basic
open Set
set_option autoImplicit false

/-- A positive zero of an exponent forces its nonnegative secant infimum to vanish. -/
theorem solution (f : ℝ → ℝ) (b : ℝ) (hb : 0 < b) (hz : f b = 0) :
    max 0 (sInf ((fun x : ℝ => f x / x) '' Ioi 0)) = 0 := by
  let S := (fun x : ℝ => f x / x) '' Ioi 0
  change max 0 (sInf S) = 0
  apply max_eq_left
  by_cases h : BddBelow S
  · have hm : (0 : ℝ) ∈ S := ⟨b,hb,by change f b / b = 0; rw [hz,zero_div]⟩
    exact csInf_le h hm
  · rw [Real.sInf_of_not_bddBelow h]
