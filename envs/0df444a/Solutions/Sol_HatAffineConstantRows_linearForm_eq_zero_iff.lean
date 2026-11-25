-- Prove2me | solution 1 for HatAffineConstantRows.linearForm_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:14:13.013936+00:00
-- url     : https://prove2.me/submissions/a72ebed8-3fd6-454d-9c40-5cc8ca981829

import Definitions.Def_HatAffineGeneral_Discovery
import Definitions.Def_HatAffineConstantRows_LowDegreeBox
import Definitions.Def_HatAffineConstantRows_ConstantRows
import Theorems.Thm_HatAffineConstantRows_eval_linearForm
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
    {K : Type u} [Field K] {m : Nat} (a : Fin m → K) :
    linearForm a = 0 ↔ a = 0 := by
  classical
  constructor
  · intro h
    funext j
    let y : Fin m → K := fun k => if k = j then 1 else 0
    have heval := congrArg (MvPolynomial.eval y) h
    simpa [eval_linearForm, y] using heval
  · rintro rfl
    simp [linearForm]
end HatAffineConstantRows
