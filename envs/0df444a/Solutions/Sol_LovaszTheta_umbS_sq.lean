-- Prove2me | solution 1 for LovaszTheta.umbS_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T14:47:18.7238+00:00
-- url     : https://prove2.me/submissions/1fc8265a-cce3-4a22-a6c2-cf591b1cf6ab

module
public import Mathlib
public import Definitions.Def_ThetaLib_Theta

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open LovaszTheta
variable {V : Type*}
namespace LovaszTheta
theorem _root_.solution : umbS ^ 2 = 1 - 1 / Real.sqrt 5 := by
  have h5 : (1 : ℝ) ≤ Real.sqrt 5 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  unfold umbS
  rw [Real.sq_sqrt]
  rw [sub_nonneg, div_le_one (by linarith)]; exact h5
end LovaszTheta
