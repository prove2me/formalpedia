-- Prove2me | solution 1 for HatAffineGenericCore.puncturedGrid_eq_puncturedPower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:14:07.426877+00:00
-- url     : https://prove2.me/submissions/533d9df0-c9b5-4bae-905c-b83b8b9df9b3

import Mathlib
import Definitions.Def_HatAffineGenericCore_G2
import Theorems.Thm_HatAffineGenericCore_mem_puncturedValues
import Theorems.Thm_HatAffineGenericCore_puncturedValues_card
attribute [local simp] HatAffineGenericCore.mem_puncturedValues
attribute [local simp] HatAffineGenericCore.puncturedValues_card
section
open scoped BigOperators MonomialOrder
namespace HatAffineGenericCore
universe u
open Finset
open MvPolynomial
private lemma prod_punctured_sub_self {K : Type u} [Field K] [Fintype K]
    (g : K) :
    ∏ x ∈ puncturedValues g, (g - x) = (-1 : K) := by
  classical
  calc
    ∏ x ∈ puncturedValues g, (g - x) = ∏ z : Kˣ, (z : K) := by
      refine Finset.prod_bij
        (fun x hx => Units.mk0 (g - x) (sub_ne_zero.mpr ?_))
        (fun _ _ => Finset.mem_univ _)
        ?_ ?_ (fun _ _ => rfl)
      · exact (mem_puncturedValues g x).mp hx |>.symm
      · intro x₁ hx₁ x₂ hx₂ heq
        exact sub_right_injective (congrArg Units.val heq)
      · intro z hz
        refine ⟨g - (z : K), ?_, ?_⟩
        · rw [mem_puncturedValues]
          intro hz
          exact Units.ne_zero z (sub_eq_self.mp hz)
        · apply Units.ext
          simp
    _ = (-1 : K) := by
      have h := congrArg Units.val (FiniteField.prod_univ_units_id_eq_neg_one (K := K))
      simpa using h
private lemma polynomial_punctured_product_eq_power
    {K : Type u} [Field K] [Fintype K] (g : K) :
    (∏ x ∈ puncturedValues g,
      (Polynomial.X - Polynomial.C x)) =
      (Polynomial.X - Polynomial.C g) ^ (Fintype.card K - 1) - 1 := by
  classical
  let n := Fintype.card K - 1
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq
    _ _ Function.injective_id
  · intro y
    simp only [id_eq, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_one]
    change (∏ x ∈ puncturedValues g, (y - x)) =
      (y - g) ^ (Fintype.card K - 1) - 1
    by_cases hyg : y = g
    · subst y
      rw [prod_punctured_sub_self]
      have hn : 0 < Fintype.card K - 1 := by
        have hcard : 1 < Fintype.card K := Fintype.one_lt_card
        omega
      simp [zero_pow hn.ne']
    · have hy_mem : y ∈ puncturedValues g := (mem_puncturedValues g y).mpr hyg
      rw [Finset.prod_eq_zero hy_mem]
      · rw [FiniteField.pow_card_sub_one_eq_one (y - g) (sub_ne_zero.mpr hyg), sub_self]
      · simp
  · have hleft :
        (∏ x ∈ puncturedValues g,
          (Polynomial.X - Polynomial.C x)).natDegree = n := by
      simp [n]
    have hbase :
        (Polynomial.X - Polynomial.C g : Polynomial K).natDegree = 1 :=
      Polynomial.natDegree_X_sub_C g
    have hpow :
        ((Polynomial.X - Polynomial.C g) ^ n : Polynomial K).natDegree = n := by
      simpa [hbase] using (Polynomial.monic_X_sub_C g).natDegree_pow n
    have hright :
        ((Polynomial.X - Polynomial.C g) ^ n - 1 : Polynomial K).natDegree ≤ n := by
      exact (Polynomial.natDegree_sub_le _ _).trans (by simp [hpow])
    dsimp only [n] at hleft hpow hright ⊢
    rw [hleft]
    apply lt_of_le_of_lt (max_le le_rfl hright)
    have hcard : 1 < Fintype.card K := Fintype.one_lt_card
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
theorem _root_.solution
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (g : Fin m → K) (j : Fin m) :
    puncturedGrid g j = puncturedPower g j := by
  have h := congrArg (Polynomial.toMvPolynomial (R := K) j)
    (polynomial_punctured_product_eq_power (g j))
  simpa [puncturedGrid, puncturedPower, puncturedSet, puncturedValues] using h
end HatAffineGenericCore
