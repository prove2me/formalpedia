-- Prove2me | solution 1 for NewtonianLipschitz.cycleIndex_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:27:07.536179+00:00
-- url     : https://prove2.me/submissions/86de079a-c34c-41c4-abd2-79db1754d9c9

module
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
public import Definitions.Def_NewtonianLipschitz_JacobianPermutations

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution : cycleIndex 2 = 0 := by decide
end NewtonianLipschitz
