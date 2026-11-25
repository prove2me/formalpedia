-- Prove2me | solution 1 for HatAffineConstantRows.linearForm_totalDegree_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:16:51.949294+00:00
-- url     : https://prove2.me/submissions/e9b78674-a2fe-4897-a5fd-baf8d7996105

import Definitions.Def_HatAffineGeneral_Discovery
import Definitions.Def_HatAffineConstantRows_LowDegreeBox
import Definitions.Def_HatAffineConstantRows_ConstantRows
import Theorems.Thm_HatAffineConstantRows_linearForm_ne_zero_iff
import Theorems.Thm_HatAffineConstantRows_linearForm_totalDegree_le
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
    {K : Type u} [Field K] {m : Nat} (a : Fin m → K) (ha : a ≠ 0) :
    (linearForm a).totalDegree = 1 := by
  have hle := linearForm_totalDegree_le a
  have hne : (linearForm a).totalDegree ≠ 0 := by
    intro hzero
    have hC := (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp hzero
    have hconst : MvPolynomial.coeff 0 (linearForm a) = 0 := by
      classical
      simp [linearForm, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
    have hlinear : linearForm a = 0 := by
      simpa [hconst] using hC
    exact (linearForm_ne_zero_iff a).mpr ha hlinear
  omega
end HatAffineConstantRows
