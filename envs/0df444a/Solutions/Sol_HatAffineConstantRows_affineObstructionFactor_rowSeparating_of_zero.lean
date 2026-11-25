-- Prove2me | solution 1 for HatAffineConstantRows.affineObstructionFactor_rowSeparating_of_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:11:04.547293+00:00
-- url     : https://prove2.me/submissions/4e4512b0-84be-4b8c-aeae-325e178b5826

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
    (A : I → Fin m → K) (b : I → K) (i : I) (hi : A i = 0) :
    affineObstructionFactor A b (rowSeparatingOffset A b) i = C (-1) := by
  classical
  simp [affineObstructionFactor, rowSeparatingOffset, hi, linearForm]
end HatAffineConstantRows
