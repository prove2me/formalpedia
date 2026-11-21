-- Prove2me | solution 1 for NewtonianLipschitz.cycleIndex_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:26:45.585055+00:00
-- url     : https://prove2.me/submissions/964b03f7-bc39-48af-b00b-9f2604fa4c32

module
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
public import Definitions.Def_NewtonianLipschitz_JacobianPermutations

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution : cycleIndex 1 = 2 := by decide
end NewtonianLipschitz
