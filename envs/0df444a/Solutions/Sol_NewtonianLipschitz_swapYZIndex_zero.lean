-- Prove2me | solution 1 for NewtonianLipschitz.swapYZIndex_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:27:53.457603+00:00
-- url     : https://prove2.me/submissions/f18757f3-5c12-4ef0-9333-4b4a5bc78de6

module
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
public import Definitions.Def_NewtonianLipschitz_JacobianPermutations

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution : swapYZIndex 0 = 0 := by decide
end NewtonianLipschitz
