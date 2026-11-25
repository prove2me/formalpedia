-- Prove2me | solution 1 for HatAffineConstantRows.affineObstructionFactor_rowSeparating_totalDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:18:19.399946+00:00
-- url     : https://prove2.me/submissions/32657986-e1f5-4676-a9f0-ad5027ca0765

import Definitions.Def_HatAffineGeneral_Discovery
import Definitions.Def_HatAffineConstantRows_LowDegreeBox
import Definitions.Def_HatAffineConstantRows_ConstantRows
import Theorems.Thm_HatAffineConstantRows_linearForm_totalDegree_eq_one
import Theorems.Thm_HatAffineConstantRows_affineObstructionFactor_rowSeparating_of_zero
import Theorems.Thm_HatAffineConstantRows_affineObstructionFactor_rowSeparating_of_ne_zero
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
    (A : I → Fin m → K) (b : I → K) (i : I) :
    (affineObstructionFactor A b (rowSeparatingOffset A b) i).totalDegree =
      rowDegree (A i) := by
  classical
  by_cases hi : A i = 0
  · rw [affineObstructionFactor_rowSeparating_of_zero A b i hi]
    simp [rowDegree, hi]
  · rw [affineObstructionFactor_rowSeparating_of_ne_zero A b i hi,
      linearForm_totalDegree_eq_one (A i) hi]
    simp [rowDegree, hi]
end HatAffineConstantRows
