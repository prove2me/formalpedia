-- Prove2me | solution 1 for NewtonianLipschitz.cycleVec_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:26:50.857751+00:00
-- url     : https://prove2.me/submissions/8b0d92cf-2aa4-4054-92fb-a85f91c2148e

module
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
public import Definitions.Def_NewtonianLipschitz_JacobianPermutations

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution (x : Vec3) : cycleVec x 0 = x 1 := by rfl
end NewtonianLipschitz
