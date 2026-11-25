-- Prove2me | solution 1 for HatAffineConstantRows.linearForm_totalDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:14:20.010217+00:00
-- url     : https://prove2.me/submissions/01738c65-de8b-46b6-ad6f-d6965d3c1114

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
    {K : Type u} [Field K] {m : Nat} (a : Fin m → K) :
    (linearForm a).totalDegree ≤ 1 := by
  classical
  unfold linearForm
  refine (MvPolynomial.totalDegree_finsetSum Finset.univ
    (fun j => C (a j) * X j)).trans ?_
  apply Finset.sup_le
  intro j hj
  exact (MvPolynomial.totalDegree_mul (C (a j)) (X j)).trans (by simp)
end HatAffineConstantRows
