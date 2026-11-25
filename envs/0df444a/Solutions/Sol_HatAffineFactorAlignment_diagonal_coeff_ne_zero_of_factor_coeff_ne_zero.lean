-- Prove2me | solution 1 for HatAffineFactorAlignment.diagonal_coeff_ne_zero_of_factor_coeff_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:15:16.69173+00:00
-- url     : https://prove2.me/submissions/0a7133c9-1b1e-442d-8d40-b779c126d314

import Definitions.Def_HatAffineGenericCore_G3A
import Definitions.Def_HatAffineFactorAlignment_FactorShape
import Theorems.Thm_HatAffineFactorAlignment_eval_diagonal_eq_zero_of_dvd
import Theorems.Thm_HatAffineGenericCore_eval_diagonalForm
import Theorems.Thm_HatAffineGenericCore_eval_linearForm
import Theorems.Thm_HatAffineGenericCore_mem_coeffSupport
attribute [local simp] HatAffineGenericCore.mem_coeffSupport


section
open scoped BigOperators
namespace HatAffineFactorAlignment
universe u
open Finset
open MvPolynomial
open HatAffineGenericCore
private lemma sum_ite_two
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid R]
    (r s : ι) (hrs : r ≠ s) (fr fs : ι → R) :
    (∑ x, if x = r then fr x else if x = s then fs x else 0) =
      fr r + fs s := by
  calc
    (∑ x, if x = r then fr x else if x = s then fs x else 0) =
        ∑ x, ((if x = r then fr x else 0) +
          (if x = s then fs x else 0)) := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hxr : x = r <;> by_cases hxs : x = s <;> simp_all
    _ = fr r + fs s := by
      rw [Finset.sum_add_distrib]
      simp
end HatAffineFactorAlignment
end

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
    (hlambda : lambda ≠ 0)
    (hdiv : linearForm a ∣ diagonalForm lambda)
    (r : Fin m) (har : a r ≠ 0) :
    lambda r ≠ 0 := by
  classical
  intro hlr0
  apply hlambda
  funext v
  by_cases hvr : v = r
  · simpa [hvr] using hlr0
  · let y : Fin m → K := fun j =>
      if j = r then -(a v / a r) else if j = v then 1 else 0
    have hLy : MvPolynomial.eval y (linearForm a) = 0 := by
      rw [eval_linearForm]
      simp only [y, mul_ite, mul_neg, mul_one, mul_zero]
      rw [sum_ite_two r v (Ne.symm hvr)]
      field_simp [har] <;> ring
    have hDy := eval_diagonal_eq_zero_of_dvd hdiv hLy
    rw [eval_diagonalForm] at hDy
    have hn : Fintype.card K - 1 ≠ 0 := by omega
    simp only [y, ite_pow, mul_ite, one_pow, zero_pow hn, mul_zero] at hDy
    rw [sum_ite_two r v (Ne.symm hvr)] at hDy
    simpa [hlr0] using hDy
end HatAffineFactorAlignment
