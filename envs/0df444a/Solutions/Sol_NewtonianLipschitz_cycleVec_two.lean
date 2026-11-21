-- Prove2me | solution 1 for NewtonianLipschitz.cycleVec_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:27:11.916644+00:00
-- url     : https://prove2.me/submissions/938208da-329a-4839-ad0b-721c736a9b6b

module
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
public import Definitions.Def_NewtonianLipschitz_JacobianPermutations

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution (x : Vec3) : cycleVec x 2 = x 0 := by rfl
end NewtonianLipschitz
