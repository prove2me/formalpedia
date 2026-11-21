-- Prove2me | solution 1 for NewtonianLipschitz.swapYZVec_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:28:04.077193+00:00
-- url     : https://prove2.me/submissions/8c6db53d-9102-4542-96b0-c87f2c70f4e7

module
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
public import Definitions.Def_NewtonianLipschitz_JacobianPermutations

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution (x : Vec3) : swapYZVec x 0 = x 0 := by rfl
end NewtonianLipschitz
