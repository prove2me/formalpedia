-- Prove2me | solution 1 for NewtonianLipschitz.toPhysicalVec3_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:20:26.201156+00:00
-- url     : https://prove2.me/submissions/f8abc774-d4ac-4025-9727-f237029f2fa3

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_Basic

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution (q : Vec3) (i : Fin 3) :
    toPhysicalVec3 q i = q i := by
  rfl
end NewtonianLipschitz
