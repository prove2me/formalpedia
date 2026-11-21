-- Prove2me | solution 1 for NewtonianLipschitz.ofLp_toPhysicalVec3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:20:16.054074+00:00
-- url     : https://prove2.me/submissions/e51e6d90-dd93-4f24-b951-e888407dde90

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_Basic

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution (q : Vec3) :
    WithLp.ofLp (toPhysicalVec3 q) = q := by
  rfl
end NewtonianLipschitz
