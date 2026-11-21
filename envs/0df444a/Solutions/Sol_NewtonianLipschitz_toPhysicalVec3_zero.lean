-- Prove2me | solution 1 for NewtonianLipschitz.toPhysicalVec3_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:20:16.614924+00:00
-- url     : https://prove2.me/submissions/8b4dcd05-4a3b-4c98-8a74-b67ab27d254c

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_Basic

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution : toPhysicalVec3 (0 : Vec3) = 0 := by
  rfl
end NewtonianLipschitz
