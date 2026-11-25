-- Prove2me | solution 1 for HatAffineGenericCore.puncturedGrid_totalDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:14:02.946264+00:00
-- url     : https://prove2.me/submissions/bce9e7dc-939a-4460-8faa-96c6a5637d26

import Mathlib
import Definitions.Def_HatAffineGenericCore_G2
import Theorems.Thm_HatAffineGenericCore_mem_puncturedValues
import Theorems.Thm_HatAffineGenericCore_puncturedValues_card
import Theorems.Thm_HatAffineGenericCore_puncturedSet_card
attribute [local simp] HatAffineGenericCore.mem_puncturedValues
attribute [local simp] HatAffineGenericCore.puncturedValues_card
section
open scoped BigOperators MonomialOrder
namespace HatAffineGenericCore
universe u
open Finset
open MvPolynomial
private lemma X_sub_C_ne_zero_mv {K : Type u} [Field K] {m : Nat}
    (j : Fin m) (x : K) : (X j - C x : MvPolynomial (Fin m) K) ≠ 0 := by
  exact (MonomialOrder.degLex.monic_X_sub_C j x).ne_zero
private lemma totalDegree_X_sub_C {K : Type u} [Field K] {m : Nat}
    (j : Fin m) (x : K) :
    (X j - C x : MvPolynomial (Fin m) K).totalDegree = 1 := by
  rw [← MvPolynomial.degree_degLexDegree]
  rw [MonomialOrder.degree_X_sub_C]
  simp
private lemma totalDegree_prod_X_sub_C {K : Type u} [Field K] {m : Nat}
    (j : Fin m) (s : Finset K) :
    (∏ x ∈ s, (X j - C x : MvPolynomial (Fin m) K)).totalDegree = s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      rw [Finset.prod_insert hx]
      rw [MvPolynomial.totalDegree_mul_of_isDomain
        (X_sub_C_ne_zero_mv j x)
        (Finset.prod_ne_zero_iff.mpr fun y hy => X_sub_C_ne_zero_mv j y)]
      rw [totalDegree_X_sub_C, ih]
      simp [hx]
      omega
end HatAffineGenericCore
end

set_option autoImplicit true
open scoped BigOperators MonomialOrder
open HatAffineGenericCore
universe u
open Finset
open MvPolynomial
namespace HatAffineGenericCore
theorem _root_.solution {K : Type u} [Field K] [Fintype K] {m : Nat}
    (g : Fin m → K) (j : Fin m) :
    (puncturedGrid g j).totalDegree = Fintype.card K - 1 := by
  rw [puncturedGrid, totalDegree_prod_X_sub_C, puncturedSet_card]
end HatAffineGenericCore
