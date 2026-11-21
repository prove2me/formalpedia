-- Prove2me | solution 1 for NewtonianLipschitz.swapYZIndex_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:27:56.306769+00:00
-- url     : https://prove2.me/submissions/53a04998-a9d4-49ee-8020-b7118ad08423

module
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
public import Definitions.Def_NewtonianLipschitz_JacobianPermutations

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution : swapYZIndex 1 = 2 := by decide
end NewtonianLipschitz
