-- Prove2me | solution 1 for HatAffineFactorAlignment.genericTypeII_of_shape
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:15:39.954135+00:00
-- url     : https://prove2.me/submissions/135424f0-87de-4b92-b075-a709d7781c24

import Definitions.Def_HatAffineFactorAlignment_FactorShape
import Definitions.Def_HatAffineFactorAlignment_FactorAlignment
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
private lemma sum_eq_two_of_zero_off
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid R]
    (f : ι → R) (u v : ι) (huv : u ≠ v)
    (hzero : ∀ j, j ≠ u → j ≠ v → f j = 0) :
    (∑ j, f j) = f u + f v := by
  calc
    (∑ j, f j) =
        ∑ j, ((if j = u then f j else 0) +
          (if j = v then f j else 0)) := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hju : j = u
      · subst j
        simp [huv]
      · by_cases hjv : j = v
        · subst j
          simp [hju]
        · simp [hju, hjv, hzero j hju hjv]
    _ = f u + f v := by
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
    (A : Fin (Fintype.card K - 1) → Fin m → K)
    (lambda : Fin m → K)
    (hidentity : (∏ i, linearForm (A i)) = diagonalForm lambda)
    (hshape : GenericTypeIIShape A lambda) :
    GenericTypeII A lambda := by
  classical
  obtain ⟨u, v, alpha, c, mu, huv, hmu, halpha, hc, hAshape,
    hlambdaShape⟩ := hshape
  have hsurj : ∀ z : K, z ≠ 0 → ∃ i, c i = z := by
    intro z hz
    let y : Fin m → K := fun j =>
      if j = u then z else if j = v then 1 else 0
    have hfactorEval : ∀ i,
        (∑ j, A i j * y j) = alpha i * (z - c i) := by
      intro i
      rw [sum_eq_two_of_zero_off (fun j => A i j * y j) u v huv]
      · rw [hAshape i]
        simp [y, huv, Ne.symm huv]
        ring
      · intro j hju hjv
        rw [hAshape i]
        simp [hju, hjv]
    have hrhs : (∑ j, lambda j * y j ^ (Fintype.card K - 1)) = 0 := by
      rw [sum_eq_two_of_zero_off
        (fun j => lambda j * y j ^ (Fintype.card K - 1)) u v huv]
      · rw [hlambdaShape]
        have hzpow : z ^ (Fintype.card K - 1) = 1 :=
          FiniteField.pow_card_sub_one_eq_one z hz
        simp [y, huv, Ne.symm huv, hzpow]
      · intro j hju hjv
        rw [hlambdaShape]
        simp [hju, hjv]
    have heval :
        (∏ i, ∑ j, A i j * y j) =
          ∑ j, lambda j * y j ^ (Fintype.card K - 1) := by
      simpa only [map_prod, eval_linearForm, eval_diagonalForm] using
        congrArg (MvPolynomial.eval y) hidentity
    have hlhs :
        (∏ i, ∑ j, A i j * y j) =
          ∏ i, alpha i * (z - c i) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact hfactorEval i
    have hprodzero : (∏ i, alpha i * (z - c i)) = 0 := by
      calc
        (∏ i, alpha i * (z - c i)) =
            ∏ i, ∑ j, A i j * y j := hlhs.symm
        _ = ∑ j, lambda j * y j ^ (Fintype.card K - 1) := heval
        _ = 0 := hrhs
    obtain ⟨i, hi, hizero⟩ := Finset.prod_eq_zero_iff.mp hprodzero
    have hzci : z - c i = 0 :=
      (mul_eq_zero.mp hizero).resolve_left (halpha i)
    exact ⟨i, (sub_eq_zero.mp hzci).symm⟩
  exact ⟨u, v, alpha, c, mu, huv, hmu, halpha, hc, hsurj,
    hAshape, hlambdaShape⟩
end HatAffineFactorAlignment
