-- Prove2me | solution 1 for NewtonianLipschitz.swapYZVec_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:28:10.832307+00:00
-- url     : https://prove2.me/submissions/32b85fa9-a944-48a6-9bc4-b49335022735

module
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
public import Definitions.Def_NewtonianLipschitz_JacobianPermutations

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution (x : Vec3) : swapYZVec x 1 = x 2 := by rfl
end NewtonianLipschitz
