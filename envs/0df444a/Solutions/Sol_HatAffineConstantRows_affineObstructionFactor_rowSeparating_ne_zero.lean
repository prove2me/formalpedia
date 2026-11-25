-- Prove2me | solution 1 for HatAffineConstantRows.affineObstructionFactor_rowSeparating_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:17:00.826962+00:00
-- url     : https://prove2.me/submissions/901a9e6a-b7c2-448f-9017-ea262502dc72

import Definitions.Def_HatAffineGeneral_Discovery
import Definitions.Def_HatAffineConstantRows_LowDegreeBox
import Definitions.Def_HatAffineConstantRows_ConstantRows
import Theorems.Thm_HatAffineConstantRows_linearForm_ne_zero_iff
import Theorems.Thm_HatAffineConstantRows_affineObstructionFactor_rowSeparating_of_zero
import Theorems.Thm_HatAffineConstantRows_affineObstructionFactor_rowSeparating_of_ne_zero

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
    affineObstructionFactor A b (rowSeparatingOffset A b) i ≠ 0 := by
  by_cases hi : A i = 0
  · rw [affineObstructionFactor_rowSeparating_of_zero A b i hi]
    exact MvPolynomial.C_ne_zero.mpr (neg_ne_zero.mpr one_ne_zero)
  · rw [affineObstructionFactor_rowSeparating_of_ne_zero A b i hi]
    exact (linearForm_ne_zero_iff (A i)).mpr hi
end HatAffineConstantRows
