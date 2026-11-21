-- Prove2me | solution 1 for NewtonianLipschitz.euclideanRadius_eq_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:20:27.111179+00:00
-- url     : https://prove2.me/submissions/03436169-6dab-4d7b-9e89-056102aedd9b

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_Basic

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution (x : Vec3) :
    euclideanRadius x = Real.sqrt (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) := by
  rfl
end NewtonianLipschitz
