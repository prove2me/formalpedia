-- Prove2me | solution 1 for HatAffineConstantRows.affineObstructionFactor_rowSeparating_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:11:08.881905+00:00
-- url     : https://prove2.me/submissions/5a06dbe7-efc5-4b3f-aad0-3ec3a4e4161f

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
    {K : Type u} [Field K] {m : Nat} {I : Type v}
    (A : I → Fin m → K) (b : I → K) (i : I) (hi : A i ≠ 0) :
    affineObstructionFactor A b (rowSeparatingOffset A b) i = linearForm (A i) := by
  classical
  simp [affineObstructionFactor, rowSeparatingOffset, hi]
end HatAffineConstantRows
