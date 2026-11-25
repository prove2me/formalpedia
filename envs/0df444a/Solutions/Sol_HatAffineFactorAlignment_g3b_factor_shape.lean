-- Prove2me | solution 1 for HatAffineFactorAlignment.g3b_factor_shape
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:17:04.671806+00:00
-- url     : https://prove2.me/submissions/90eea8c1-f242-4ce0-88fc-32e896cf5621

import Definitions.Def_HatAffineGenericCore_G3A
import Definitions.Def_HatAffineFactorAlignment_FactorShape
import Theorems.Thm_HatAffineFactorAlignment_exists_nonzero_coord
import Theorems.Thm_HatAffineFactorAlignment_eval_diagonal_eq_zero_of_dvd
import Theorems.Thm_HatAffineFactorAlignment_diagonal_coeff_eq_zero_of_factor_coeff_eq_zero
import Theorems.Thm_HatAffineFactorAlignment_diagonal_coeff_ne_zero_of_factor_coeff_ne_zero
import Theorems.Thm_HatAffineFactorAlignment_factor_dvd_diagonal
import Theorems.Thm_HatAffineFactorAlignment_coeff_eq_zero_outside_two_of_card_le
import Theorems.Thm_HatAffineGenericCore_eval_diagonalForm
import Theorems.Thm_HatAffineGenericCore_eval_linearForm
import Theorems.Thm_HatAffineGenericCore_g3a_support_le_two
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
    (hm : 1 ≤ m) (hq : 3 ≤ Fintype.card K)
    (A : Fin (Fintype.card K - 1) → Fin m → K)
    (lambda : Fin m → K)
    (hrows : ∀ i, A i ≠ 0)
    (hlambda : lambda ≠ 0)
    (hidentity : (∏ i, linearForm (A i)) = diagonalForm lambda) :
    GenericTypeI A lambda ∨ GenericTypeIIShape A lambda := by
  classical
  have hnpos : 0 < Fintype.card K - 1 := by omega
  let i0 : Fin (Fintype.card K - 1) := ⟨0, hnpos⟩
  have hdiv : ∀ i, linearForm (A i) ∣ diagonalForm lambda := by
    intro i
    exact factor_dvd_diagonal A lambda hidentity i
  have hsupport : ∀ i, (coeffSupport (A i)).card ≤ 2 := by
    intro i
    exact g3a_support_le_two hm hq (A i) lambda (hrows i) hlambda (hdiv i)
  obtain ⟨u, hu⟩ := exists_nonzero_coord (A i0) (hrows i0)
  by_cases hsecond : ∃ v, v ≠ u ∧ A i0 v ≠ 0
  · obtain ⟨v, hvu, hv⟩ := hsecond
    have huv : u ≠ v := Ne.symm hvu
    have hseedOutside : ∀ j, j ≠ u → j ≠ v → A i0 j = 0 := by
      intro j hju hjv
      exact coeff_eq_zero_outside_two_of_card_le
        (A i0) u v j (hsupport i0) hu hv huv hju hjv
    have hlambdaOutside : ∀ j, j ≠ u → j ≠ v → lambda j = 0 := by
      intro j hju hjv
      exact diagonal_coeff_eq_zero_of_factor_coeff_eq_zero
        hq (A i0) lambda (hdiv i0) j (hseedOutside j hju hjv)
    have hlu : lambda u ≠ 0 :=
      diagonal_coeff_ne_zero_of_factor_coeff_ne_zero
        hq (A i0) lambda hlambda (hdiv i0) u hu
    have hlv : lambda v ≠ 0 :=
      diagonal_coeff_ne_zero_of_factor_coeff_ne_zero
        hq (A i0) lambda hlambda (hdiv i0) v hv
    let c0 : K := -(A i0 v / A i0 u)
    have hc0 : c0 ≠ 0 := by
      dsimp [c0]
      exact neg_ne_zero.mpr (div_ne_zero hv hu)
    have hlambdaPre : lambda = fun j =>
        if j = u then lambda u else if j = v then lambda v else 0 := by
      funext j
      by_cases hju : j = u
      · subst j
        simp
      · by_cases hjv : j = v
        · subst j
          simp [huv, Ne.symm huv]
        · simp [hju, hjv, hlambdaOutside j hju hjv]
    let y : Fin m → K := fun j =>
      if j = u then c0 else if j = v then 1 else 0
    have hLy : MvPolynomial.eval y (linearForm (A i0)) = 0 := by
      rw [eval_linearForm]
      simp only [y, mul_ite, mul_one, mul_zero]
      rw [sum_ite_two u v huv]
      dsimp [c0]
      field_simp [hu] <;> ring
    have hDy := eval_diagonal_eq_zero_of_dvd (hdiv i0) hLy
    rw [eval_diagonalForm] at hDy
    have hc0pow : c0 ^ (Fintype.card K - 1) = 1 :=
      FiniteField.pow_card_sub_one_eq_one c0 hc0
    have hsum :
        (∑ j, lambda j * y j ^ (Fintype.card K - 1)) =
          lambda u * y u ^ (Fintype.card K - 1) +
            lambda v * y v ^ (Fintype.card K - 1) := by
      calc
        (∑ j, lambda j * y j ^ (Fintype.card K - 1)) =
            ∑ j, if j = u then lambda j * y j ^ (Fintype.card K - 1)
              else if j = v then lambda j * y j ^ (Fintype.card K - 1)
              else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          by_cases hju : j = u
          · simp [hju]
          · by_cases hjv : j = v
            · simp [hju, hjv]
            · rw [hlambdaOutside j hju hjv]
              simp [hju, hjv]
        _ = lambda u * y u ^ (Fintype.card K - 1) +
              lambda v * y v ^ (Fintype.card K - 1) := by
          rw [sum_ite_two u v huv]
    have hadd : lambda u + lambda v = 0 := by
      rw [hsum] at hDy
      simpa [y, huv, Ne.symm huv, hc0pow] using hDy
    have hlvEq : lambda v = -lambda u :=
      eq_neg_of_add_eq_zero_right hadd
    have hrowOutside : ∀ i j, j ≠ u → j ≠ v → A i j = 0 := by
      intro i j hju hjv
      by_contra haj
      have hlj : lambda j ≠ 0 :=
        diagonal_coeff_ne_zero_of_factor_coeff_ne_zero
          hq (A i) lambda hlambda (hdiv i) j haj
      exact hlj (hlambdaOutside j hju hjv)
    have hAu : ∀ i, A i u ≠ 0 := by
      intro i hzero
      have : lambda u = 0 :=
        diagonal_coeff_eq_zero_of_factor_coeff_eq_zero
          hq (A i) lambda (hdiv i) u hzero
      exact hlu this
    have hAv : ∀ i, A i v ≠ 0 := by
      intro i hzero
      have : lambda v = 0 :=
        diagonal_coeff_eq_zero_of_factor_coeff_eq_zero
          hq (A i) lambda (hdiv i) v hzero
      exact hlv this
    let alpha : Fin (Fintype.card K - 1) → K := fun i => A i u
    let c : Fin (Fintype.card K - 1) → K := fun i => -(A i v / A i u)
    have halpha : ∀ i, alpha i ≠ 0 := by
      intro i
      exact hAu i
    have hc : ∀ i, c i ≠ 0 := by
      intro i
      dsimp [c]
      exact neg_ne_zero.mpr (div_ne_zero (hAv i) (hAu i))
    have hAshape : ∀ i, A i = fun j =>
        if j = u then alpha i
        else if j = v then -alpha i * c i
        else 0 := by
      intro i
      funext j
      by_cases hju : j = u
      · subst j
        simp [alpha]
      · by_cases hjv : j = v
        · subst j
          simp only [hvu, if_false, if_pos]
          dsimp [alpha, c]
          field_simp [hAu i] <;> ring
        · simp [hju, hjv, hrowOutside i j hju hjv]
    have hlambdaShape : lambda = fun j =>
        if j = u then lambda u
        else if j = v then -lambda u
        else 0 := by
      funext j
      by_cases hju : j = u
      · subst j
        simp
      · by_cases hjv : j = v
        · subst j
          simp [huv, Ne.symm huv, hlvEq]
        · simp [hju, hjv, hlambdaOutside j hju hjv]
    right
    exact ⟨u, v, alpha, c, lambda u, huv, hlu, halpha, hc,
      hAshape, hlambdaShape⟩
  · have hseedOutside : ∀ j, j ≠ u → A i0 j = 0 := by
      intro j hju
      by_contra haj
      exact hsecond ⟨j, hju, haj⟩
    have hlambdaOutside : ∀ j, j ≠ u → lambda j = 0 := by
      intro j hju
      exact diagonal_coeff_eq_zero_of_factor_coeff_eq_zero
        hq (A i0) lambda (hdiv i0) j (hseedOutside j hju)
    have hlu : lambda u ≠ 0 :=
      diagonal_coeff_ne_zero_of_factor_coeff_ne_zero
        hq (A i0) lambda hlambda (hdiv i0) u hu
    have hrowOutside : ∀ i j, j ≠ u → A i j = 0 := by
      intro i j hju
      by_contra haj
      have hlj : lambda j ≠ 0 :=
        diagonal_coeff_ne_zero_of_factor_coeff_ne_zero
          hq (A i) lambda hlambda (hdiv i) j haj
      exact hlj (hlambdaOutside j hju)
    let alpha : Fin (Fintype.card K - 1) → K := fun i => A i u
    have halpha : ∀ i, alpha i ≠ 0 := by
      intro i hzero
      apply hrows i
      funext j
      by_cases hju : j = u
      · subst j
        exact hzero
      · exact hrowOutside i j hju
    have hAshape : ∀ i, A i = fun j =>
        if j = u then alpha i else 0 := by
      intro i
      funext j
      by_cases hju : j = u
      · subst j
        simp [alpha]
      · simp [hju, hrowOutside i j hju]
    have hlambdaShape : lambda = fun j =>
        if j = u then lambda u else 0 := by
      funext j
      by_cases hju : j = u
      · subst j
        simp
      · simp [hju, hlambdaOutside j hju]
    left
    exact ⟨u, alpha, lambda u, hlu, halpha, hAshape, hlambdaShape⟩
end HatAffineFactorAlignment
