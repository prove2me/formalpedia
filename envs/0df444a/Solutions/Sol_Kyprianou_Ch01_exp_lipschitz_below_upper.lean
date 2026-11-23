-- Prove2me | solution 1 for Kyprianou.Ch01.exp_lipschitz_below_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T09:15:16.389728+00:00
-- url     : https://prove2.me/submissions/3af6effb-3c33-454f-b364-61748c647a38

import Mathlib
open Real Set
open scoped Topology
set_option autoImplicit false

theorem solution
    (b x y : ℝ) (hx : x ≤ b) (hy : y ≤ b) :
    |Real.exp y - Real.exp x| ≤ Real.exp b * |y - x| := by
  have hder (z : ℝ) :
      HasDerivAt Real.exp (Real.exp z) z := Real.hasDerivAt_exp z
  have hbound (z : ℝ) (hz : z ∈ Iic b) :
      ‖deriv Real.exp z‖ ≤ Real.exp b := by
    rw [(hder z).deriv, Real.norm_eq_abs, abs_of_pos (Real.exp_pos z)]
    exact (Real.exp_le_exp).mpr hz
  have h := (convex_Iic b).norm_image_sub_le_of_norm_deriv_le
    (fun z (_ : z ∈ Iic b) => (hder z).differentiableAt)
    hbound hx hy
  simpa only [Real.norm_eq_abs] using h
