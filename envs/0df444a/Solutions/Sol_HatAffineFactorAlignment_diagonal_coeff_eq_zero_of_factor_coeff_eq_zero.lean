-- Prove2me | solution 1 for HatAffineFactorAlignment.diagonal_coeff_eq_zero_of_factor_coeff_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:15:04.265817+00:00
-- url     : https://prove2.me/submissions/cb456fd4-5c52-49f4-a353-52ca95a846f8

import Definitions.Def_HatAffineGenericCore_G3A
import Definitions.Def_HatAffineFactorAlignment_FactorShape
import Theorems.Thm_HatAffineFactorAlignment_eval_diagonal_eq_zero_of_dvd
import Theorems.Thm_HatAffineGenericCore_eval_diagonalForm
import Theorems.Thm_HatAffineGenericCore_eval_linearForm
import Theorems.Thm_HatAffineGenericCore_mem_coeffSupport
attribute [local simp] HatAffineGenericCore.mem_coeffSupport



set_option autoImplicit true
open scoped BigOperators
open HatAffineFactorAlignment
universe u
open Finset
open MvPolynomial
open HatAffineGenericCore
namespace HatAffineFactorAlignment
theorem _root_.solution
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (hq : 3 ≤ Fintype.card K)
    (a lambda : Fin m → K)
    (hdiv : linearForm a ∣ diagonalForm lambda)
    (r : Fin m) (har : a r = 0) :
    lambda r = 0 := by
  classical
  let y : Fin m → K := fun j => if j = r then 1 else 0
  have hLy : MvPolynomial.eval y (linearForm a) = 0 := by
    rw [eval_linearForm]
    simp [y, har]
  have hDy := eval_diagonal_eq_zero_of_dvd hdiv hLy
  rw [eval_diagonalForm] at hDy
  have hn : Fintype.card K - 1 ≠ 0 := by omega
  simpa [y, hn] using hDy
end HatAffineFactorAlignment
