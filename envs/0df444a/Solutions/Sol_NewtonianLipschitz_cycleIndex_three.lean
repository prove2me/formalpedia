-- Prove2me | solution 1 for NewtonianLipschitz.cycleIndex_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:29:33.409553+00:00
-- url     : https://prove2.me/submissions/ad3bd2f6-7ae8-462b-ba7c-156317e99465

module
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
public import Definitions.Def_NewtonianLipschitz_JacobianPermutations

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution (i : Fin 3) :
    cycleIndex (cycleIndex (cycleIndex i)) = i := by
  fin_cases i <;> decide
end NewtonianLipschitz
