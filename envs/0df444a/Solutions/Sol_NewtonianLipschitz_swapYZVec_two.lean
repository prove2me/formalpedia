-- Prove2me | solution 1 for NewtonianLipschitz.swapYZVec_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:28:21.155559+00:00
-- url     : https://prove2.me/submissions/fc4c0e47-c2f2-45db-b6ec-2217d04eba55

module
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
public import Definitions.Def_NewtonianLipschitz_JacobianPermutations

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution (x : Vec3) : swapYZVec x 2 = x 1 := by rfl
end NewtonianLipschitz
