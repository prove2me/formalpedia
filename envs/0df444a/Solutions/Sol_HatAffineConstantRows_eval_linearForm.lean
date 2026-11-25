-- Prove2me | solution 1 for HatAffineConstantRows.eval_linearForm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:10:56.729886+00:00
-- url     : https://prove2.me/submissions/c91de75b-933a-499a-bf8e-2b1a1b316e5c

import Definitions.Def_HatAffineGeneral_Discovery
import Definitions.Def_HatAffineConstantRows_LowDegreeBox
import Definitions.Def_HatAffineConstantRows_ConstantRows
import Theorems.Thm_HatAffineGenericCore_mem_puncturedValues
import Theorems.Thm_HatAffineGenericCore_puncturedValues_card
attribute [local simp] HatAffineGenericCore.mem_puncturedValues
attribute [local simp] HatAffineGenericCore.puncturedValues_card



set_option autoImplicit true
open scoped BigOperators
open HatAffineConstantRows
universe u v
open Finset
open MvPolynomial
namespace HatAffineConstantRows
theorem _root_.solution
    {K : Type u} [CommRing K] {m : Nat}
    (a y : Fin m → K) :
    MvPolynomial.eval y (linearForm a) = ∑ j, a j * y j := by
  simp [linearForm]
end HatAffineConstantRows
