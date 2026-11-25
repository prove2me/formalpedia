-- Prove2me | solution 1 for LovaszTheta.umbrella_dot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T14:47:12.462253+00:00
-- url     : https://prove2.me/submissions/1a0c7b1d-87c6-46b4-b951-2ea3df7902b0

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
theorem _root_.solution (i j : Fin 5) :
    dotProduct (umbrella i) (umbrella j) =
      umbS ^ 2 * Real.cos (pentAngle i - pentAngle j) + umbH ^ 2 := by
  simp only [umbrella, dotProduct, Fin.sum_univ_three, Real.cos_sub]
  simp
  ring
end LovaszTheta
