-- Prove2me | solution 1 for HatAffineGenericCore.g3a_support_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:14:23.543693+00:00
-- url     : https://prove2.me/submissions/1741ce96-a60c-47a3-95cb-661a28663944

import Mathlib
import Definitions.Def_HatAffineGenericCore_G3A
import Theorems.Thm_HatAffineGenericCore_mem_coeffSupport
import Theorems.Thm_HatAffineGenericCore_eval_linearForm
import Theorems.Thm_HatAffineGenericCore_eval_diagonalForm
attribute [local simp] HatAffineGenericCore.mem_coeffSupport
section
open scoped BigOperators
namespace HatAffineGenericCore
universe u
open Finset
open MvPolynomial
private lemma sum_ite_two
    {ι A : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid A]
    (r s : ι) (hrs : r ≠ s) (fr fs : ι → A) :
    (∑ x, if x = r then fr x else if x = s then fs x else 0) =
      fr r + fs s := by
  calc
    (∑ x, if x = r then fr x else if x = s then fs x else 0) =
        ∑ x, ((if x = r then fr x else 0) + (if x = s then fs x else 0)) := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hxr : x = r <;> by_cases hxs : x = s <;> simp_all
    _ = fr r + fs s := by
      rw [Finset.sum_add_distrib]
      simp
private lemma sum_ite_three
    {ι A : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid A]
    (r s t : ι) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (fr fs ft : ι → A) :
    (∑ x, if x = r then fr x else if x = s then fs x else if x = t then ft x else 0) =
      fr r + fs s + ft t := by
  calc
    (∑ x, if x = r then fr x else if x = s then fs x else if x = t then ft x else 0) =
        ∑ x, ((if x = r then fr x else 0) +
          (if x = s then fs x else 0) + (if x = t then ft x else 0)) := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hxr : x = r <;> by_cases hxs : x = s <;> by_cases hxt : x = t <;>
        simp_all
    _ = fr r + fs s + ft t := by
      simp_rw [Finset.sum_add_distrib]
      simp
private lemma coeff_scaled_X_add_C_pow_pred
    {K : Type u} [Field K] (n : Nat) (hn : 1 ≤ n) (alpha c : K) :
    (((Polynomial.C alpha) * (Polynomial.X + Polynomial.C c)) ^ n).coeff (n - 1) =
      alpha ^ n * c * (n : K) := by
  have hsub : n - (n - 1) = 1 := by omega
  have hchoose : n.choose (n - 1) = n := by
    rw [Nat.choose_symm hn, Nat.choose_one_right]
  rw [mul_pow]
  simp only [← Polynomial.C_pow, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_add_C_pow]
  rw [hsub, pow_one, hchoose]
  ring
end HatAffineGenericCore
end

set_option autoImplicit true
open scoped BigOperators
open HatAffineGenericCore
universe u
open Finset
open MvPolynomial
namespace HatAffineGenericCore
theorem _root_.solution
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (hm : 1 ≤ m) (hq : 3 ≤ Fintype.card K)
    (a lambda : Fin m → K)
    (ha : a ≠ 0) (hlambda : lambda ≠ 0)
    (hdiv : linearForm a ∣ diagonalForm lambda) :
    (coeffSupport a).card ≤ 2 := by
  classical
  by_contra hsupport
  have hthree : 2 < (coeffSupport a).card := Nat.lt_of_not_ge hsupport
  obtain ⟨r, s, t, hr, hs, ht, hrs, hrt, hst⟩ :=
    Finset.two_lt_card_iff.mp hthree
  have har : a r ≠ 0 := (mem_coeffSupport a r).mp hr
  have has : a s ≠ 0 := (mem_coeffSupport a s).mp hs
  have hat : a t ≠ 0 := (mem_coeffSupport a t).mp ht
  let n := Fintype.card K - 1
  have hn : 2 ≤ n := by
    dsimp [n]
    omega
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_two hn
  obtain ⟨Q, hQ⟩ := hdiv
  have eval_diagonal_eq_zero (y : Fin m → K)
      (hy : MvPolynomial.eval y (linearForm a) = 0) :
      MvPolynomial.eval y (diagonalForm lambda) = 0 := by
    rw [hQ, map_mul, hy, zero_mul]
  have hlr : lambda r ≠ 0 := by
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
      have hDy := eval_diagonal_eq_zero y hLy
      rw [eval_diagonalForm] at hDy
      have hexp : Fintype.card K - 1 ≠ 0 := by simpa [n] using hnpos.ne'
      simp only [y, ite_pow, mul_ite, one_pow, zero_pow hexp, mul_zero] at hDy
      rw [sum_ite_two r v (Ne.symm hvr)] at hDy
      simpa [hlr0] using hDy
  let alpha : K := -a s / a r
  let c : K := a t / a s
  let phi : Fin m → Polynomial K := fun j =>
    if j = r then Polynomial.C alpha * (Polynomial.X + Polynomial.C c)
    else if j = s then Polynomial.X
    else if j = t then 1
    else 0
  let Phi : MvPolynomial (Fin m) K →+* Polynomial K :=
    MvPolynomial.eval₂Hom Polynomial.C phi
  have hPhiL : Phi (linearForm a) = 0 := by
    simp only [Phi, linearForm, map_sum, map_mul, MvPolynomial.eval₂Hom_C,
      MvPolynomial.eval₂Hom_X', phi, mul_ite, mul_zero]
    rw [sum_ite_three r s t hrs hrt hst]
    simp only [if_pos, if_neg, hrs.symm, hrt.symm, hst.symm, mul_one]
    have h1 : Polynomial.C (a r) * Polynomial.C alpha = -Polynomial.C (a s) := by
      rw [← map_mul, ← map_neg]
      congr 1
      dsimp [alpha]
      field_simp
    have h2 : Polynomial.C (a s) * Polynomial.C c = Polynomial.C (a t) := by
      rw [← map_mul]
      congr 1
      dsimp [c]
      field_simp
    rw [← mul_assoc, h1]
    calc
      -Polynomial.C (a s) * (Polynomial.X + Polynomial.C c) +
          Polynomial.C (a s) * Polynomial.X + Polynomial.C (a t) =
          -(Polynomial.C (a s) * Polynomial.C c) + Polynomial.C (a t) := by ring
      _ = 0 := by rw [h2]; ring
  have hPhiD : Phi (diagonalForm lambda) = 0 := by
    rw [hQ, map_mul, hPhiL, zero_mul]
  have hPhiD_formula :
      Phi (diagonalForm lambda) =
        Polynomial.C (lambda r) *
            (Polynomial.C alpha * (Polynomial.X + Polynomial.C c)) ^ n +
          Polynomial.C (lambda s) * Polynomial.X ^ n +
          Polynomial.C (lambda t) := by
    simp only [Phi, diagonalForm, map_sum, map_mul, map_pow,
      MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', phi]
    have hexp : Fintype.card K - 1 ≠ 0 := by simpa [n] using hnpos.ne'
    simp only [ite_pow, zero_pow hexp, mul_ite, mul_zero]
    rw [sum_ite_three r s t hrs hrt hst]
    simp only [if_pos, if_neg, hrs.symm, hrt.symm, hst.symm, one_pow, mul_one]
    rfl
  have hcoeffzero := congrArg
    (fun p : Polynomial K => p.coeff (n - 1)) hPhiD
  simp only [Polynomial.coeff_zero] at hcoeffzero
  have hcoeff :
      (Phi (diagonalForm lambda)).coeff (n - 1) =
        lambda r * alpha ^ n * c * (n : K) := by
    rw [hPhiD_formula]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul]
    rw [coeff_scaled_X_add_C_pow_pred n (by omega)]
    have hpred_ne_n : n - 1 ≠ n := by omega
    have hpred_ne_zero : n - 1 ≠ 0 := by omega
    simp [Polynomial.coeff_X_pow, hpred_ne_n, hpred_ne_zero]
    rw [Polynomial.coeff_C_of_ne_zero hpred_ne_zero]
    ring
  have halpha : alpha ≠ 0 := by
    dsimp [alpha]
    exact div_ne_zero (neg_ne_zero.mpr has) har
  have hc : c ≠ 0 := by
    dsimp [c]
    exact div_ne_zero hat has
  have hncast : (n : K) ≠ 0 := by
    have hone : 1 ≤ Fintype.card K := Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero
    have hn_eq : (n : K) = -1 := by
      dsimp [n]
      rw [Nat.cast_sub hone, Nat.cast_card_eq_zero K, Nat.cast_one, zero_sub]
    rw [hn_eq]
    exact neg_ne_zero.mpr one_ne_zero
  rw [hcoeff] at hcoeffzero
  exact (mul_ne_zero
    (mul_ne_zero (mul_ne_zero hlr (pow_ne_zero n halpha)) hc) hncast) hcoeffzero
end HatAffineGenericCore
