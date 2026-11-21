-- Prove2me | solution 1 for NewtonianLipschitz.cycleVec_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:27:17.165174+00:00
-- url     : https://prove2.me/submissions/ed499612-8ae9-4a29-8fe9-4c9ed5f75af2

module
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
public import Definitions.Def_NewtonianLipschitz_JacobianPermutations

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution (x : Vec3) : cycleVec x 1 = x 2 := by rfl
end NewtonianLipschitz
