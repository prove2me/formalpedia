-- Prove2me | solution 1 for NewtonianLipschitz.swapYZIndex_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:28:08.016003+00:00
-- url     : https://prove2.me/submissions/f4643545-2dc3-4788-98e6-cf565e8f23e0

module
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
public import Definitions.Def_NewtonianLipschitz_JacobianPermutations

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution : swapYZIndex 2 = 1 := by decide
end NewtonianLipschitz
