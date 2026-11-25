-- Prove2me | solution 1 for LovaszTheta.cos_pentAngle_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T14:57:11.432339+00:00
-- url     : https://prove2.me/submissions/404b3793-ce0d-47ea-ac8f-ed7fe3e33f57

module
public import Mathlib
public import Definitions.Def_ThetaLib_Theta
public import Theorems.Thm_LovaszTheta_pentAngle_sub

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open LovaszTheta
variable {V : Type*}
namespace LovaszTheta
theorem _root_.solution (i j : Fin 5) (hij : i ≠ j) (hadj : ¬ (cycleGraph 5).Adj i j) :
    Real.cos (pentAngle i - pentAngle j) = -(1 + √5) / 4 := by
  have h4 : Real.cos (4 * Real.pi / 5) = -(1 + √5) / 4 := by
    rw [show 4 * Real.pi / 5 = Real.pi - Real.pi / 5 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_five]; ring
  have h6 : Real.cos (6 * Real.pi / 5) = -(1 + √5) / 4 := by
    rw [show 6 * Real.pi / 5 = Real.pi / 5 + Real.pi by ring, Real.cos_add_pi,
      Real.cos_pi_div_five]; ring
  rcases pentAngle_sub i j hij hadj with h | h | h | h <;> rw [h] <;> simp [h4, h6]
end LovaszTheta
