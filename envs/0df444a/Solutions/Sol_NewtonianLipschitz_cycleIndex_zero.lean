-- Prove2me | solution 1 for NewtonianLipschitz.cycleIndex_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:26:50.436893+00:00
-- url     : https://prove2.me/submissions/af4f602b-d36b-4694-a5b8-b1687c8654c0

module
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
public import Definitions.Def_NewtonianLipschitz_JacobianPermutations

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution : cycleIndex 0 = 1 := by decide
end NewtonianLipschitz
