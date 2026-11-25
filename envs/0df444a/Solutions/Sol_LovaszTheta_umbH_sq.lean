-- Prove2me | solution 1 for LovaszTheta.umbH_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T14:37:26.443579+00:00
-- url     : https://prove2.me/submissions/f6605b66-77f5-4c3d-b61e-226c492f8493

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
theorem _root_.solution : umbH ^ 2 = 1 / Real.sqrt 5 := by
  unfold umbH
  rw [Real.sq_sqrt (by positivity)]
end LovaszTheta
