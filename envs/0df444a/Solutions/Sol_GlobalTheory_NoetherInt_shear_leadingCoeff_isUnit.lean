-- Prove2me | solution 1 for GlobalTheory.NoetherInt.shear_leadingCoeff_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:13:28.890132+00:00
-- url     : https://prove2.me/submissions/52897be8-70a0-4ae9-b7e9-e2695d7b54dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsQuasiFinitePolynomialMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory.NoetherInt
open Polynomial
end GlobalTheory.NoetherInt
namespace GlobalTheory.NoetherInt
open MvPolynomial
section shear
variable {A : Type*} [CommRing A] {n : ℕ}
end shear
section lead
variable {k : Type*} [Field k] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) k)
variable (v w : Fin (n + 1) →₀ ℕ)
local notation3 "up" => 2 + f.totalDegree
local notation3 "r" => fun (i : Fin (n + 1)) ↦ up ^ i.1
local notation3 "T" => shear k n (2 + f.totalDegree)
variable {f v} in
private lemma lt_up (vlt : ∀ i, v i < up) : ∀ l ∈ List.ofFn v, l < up := by
  grind
private lemma sum_r_mul_ne (vlt : ∀ i, v i < up) (wlt : ∀ i, w i < up) (ne : v ≠ w) :
    ∑ x : Fin (n + 1), r x * v x ≠ ∑ x : Fin (n + 1), r x * w x := by
  intro h
  refine ne <| Finsupp.ext <| congrFun <| List.ofFn_inj.mp ?_
  apply Nat.ofDigits_inj_of_len_eq (Nat.lt_add_right f.totalDegree one_lt_two)
    (by simp) (lt_up vlt) (lt_up wlt)
  simpa only [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn, List.get_ofFn, List.length_ofFn,
    Fin.val_cast, mul_comm, List.sum_ofFn] using! h
private lemma shear_X_zero (u : ℕ) : shear k n u (X 0) = X 0 := by simp [shear, shearHom]
private lemma shear_X_succ (u : ℕ) (i : Fin n) :
    shear k n u (X i.succ) = X i.succ + X 0 ^ (u ^ i.succ.1) := by simp [shear, shearHom]
private lemma degreeOf_zero_t {a : k} (ha : a ≠ 0) : (T (monomial v a)).degreeOf 0 =
    ∑ i : Fin (n + 1), (r i) * v i := by
  have hT : T (MvPolynomial.C a) = MvPolynomial.C a := (shear k n _).commutes a
  rw [← natDegree_finSuccEquiv, monomial_eq, Finsupp.prod_pow v fun a ↦ X a]
  simp only [hT, Fin.prod_univ_succ, Fin.sum_univ_succ, map_mul, map_prod, map_pow,
    shear_X_zero, shear_X_succ, AlgEquiv.commutes, algebraMap_eq,
    map_add, finSuccEquiv_X_zero, finSuccEquiv_X_succ]
  have h (i : Fin n) :
      (Polynomial.C (X (R := k) i) + Polynomial.X ^ r i.succ) ^ v i.succ ≠ 0 :=
    pow_ne_zero (v i.succ) (Polynomial.leadingCoeff_ne_zero.mp <| by
      simp [add_comm, Polynomial.leadingCoeff_X_pow_add_C])
  rw [Polynomial.natDegree_mul (by simp [ha]) (mul_ne_zero (by simp) (Finset.prod_ne_zero_iff.mpr
    (fun i _ ↦ h i))), Polynomial.natDegree_mul (by simp) (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ h i)),
    Polynomial.natDegree_prod _ _ (fun i _ ↦ h i), natDegree_finSuccEquiv, degreeOf_C]
  simpa only [Polynomial.natDegree_pow, zero_add, Polynomial.natDegree_X, mul_one, Fin.val_zero,
    pow_zero, one_mul, add_right_inj] using Finset.sum_congr rfl (fun i _ ↦ by
    rw [add_comm (Polynomial.C _), Polynomial.natDegree_X_pow_add_C, mul_comm])
private lemma degreeOf_t_ne_of_ne (hv : v ∈ f.support) (hw : w ∈ f.support) (ne : v ≠ w) :
    (T <| monomial v <| coeff v f).degreeOf 0 ≠
    (T <| monomial w <| coeff w f).degreeOf 0 := by
  rw [degreeOf_zero_t _ _ <| mem_support_iff.mp hv, degreeOf_zero_t _ _ <| mem_support_iff.mp hw]
  refine sum_r_mul_ne f v w (fun i ↦ ?_) (fun i ↦ ?_) ne <;>
  exact lt_of_le_of_lt ((monomial_le_degreeOf i ‹_›).trans (degreeOf_le_totalDegree f i))
    (by lia)
private lemma leadingCoeff_finSuccEquiv_t :
    (finSuccEquiv k n (T ((monomial v) (coeff v f)))).leadingCoeff =
    algebraMap k _ (coeff v f) := by
  rw [monomial_eq, Finsupp.prod_fintype]
  · simp only [map_mul, map_prod, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_prod]
    have h0 : (finSuccEquiv k n (T (MvPolynomial.C (coeff v f)))).leadingCoeff = algebraMap k _ (coeff v f) := by
      have : T (MvPolynomial.C (coeff v f)) = MvPolynomial.C (coeff v f) := (shear k n _).commutes (coeff v f)
      rw [this]; simp [finSuccEquiv_apply]
    have : ∀ j, ((finSuccEquiv k n) (T (X j))).leadingCoeff = 1 := fun j ↦ by
      cases j using Fin.cases with
      | zero => simp [shear_X_zero, finSuccEquiv_X_zero]
      | succ i =>
        simp only [shear_X_succ, map_add, map_pow, finSuccEquiv_X_succ, finSuccEquiv_X_zero]
        simp [add_comm, Polynomial.leadingCoeff_X_pow_add_C]
    simp only [h0, map_pow, Polynomial.leadingCoeff_pow, this, one_pow, Finset.prod_const_one, mul_one]
  exact fun i ↦ pow_zero _
end lead
end GlobalTheory.NoetherInt
namespace GlobalTheory.NoetherInt
open MvPolynomial
end GlobalTheory.NoetherInt
namespace GlobalTheory.NoetherInt
open MvPolynomial
end GlobalTheory.NoetherInt
namespace GlobalTheory
open IsLocalRing
end GlobalTheory
end

set_option autoImplicit false
open GlobalTheory GlobalTheory.NoetherInt
open MvPolynomial
variable {k : Type*} [Field k] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) k)
variable (v w : Fin (n + 1) →₀ ℕ)
local notation3 "up" => 2 + f.totalDegree
local notation3 "r" => fun (i : Fin (n + 1)) ↦ up ^ i.1
local notation3 "T" => shear k n (2 + f.totalDegree)
namespace GlobalTheory.NoetherInt
theorem _root_.solution (fne : f ≠ 0) :
    IsUnit (finSuccEquiv k n (T f)).leadingCoeff := by
  obtain ⟨v, vin, vs⟩ := Finset.exists_max_image f.support
    (fun v ↦ (T ((monomial v) (coeff v f))).degreeOf 0) (support_nonempty.mpr fne)
  set h := fun w ↦ (MvPolynomial.monomial w) (coeff w f)
  simp only [← natDegree_finSuccEquiv] at vs
  replace vs : ∀ x ∈ f.support \ {v}, (finSuccEquiv k n (T (h x))).degree <
      (finSuccEquiv k n (T (h v))).degree := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hx
    apply Polynomial.degree_lt_degree <| lt_of_le_of_ne (vs x h1) ?_
    simpa only [natDegree_finSuccEquiv]
      using degreeOf_t_ne_of_ne f _ _ h1 vin <| List.ne_of_not_mem_cons h2
  have coeff : (finSuccEquiv k n (T (h v + ∑ x ∈ f.support \ {v}, h x))).leadingCoeff =
      (finSuccEquiv k n (T (h v))).leadingCoeff := by
    simp only [map_add, map_sum]
    rw [add_comm]
    apply Polynomial.leadingCoeff_add_of_degree_lt <| (lt_of_le_of_lt <| Polynomial.degree_sum_le _ _) ?_
    have h2 : h v ≠ 0 := by simpa [h] using mem_support_iff.mp vin
    replace h2 : (finSuccEquiv k n (T (h v))) ≠ 0 := fun eq ↦ h2 <|
      by simpa only [map_eq_zero_iff _ (AlgEquiv.injective _)] using eq
    exact (Finset.sup_lt_iff <| Ne.bot_lt (fun x ↦ h2 <| Polynomial.degree_eq_bot.mp x)).mpr vs
  nth_rw 2 [← f.support_sum_monomial_coeff]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem vin h]
  rw [leadingCoeff_finSuccEquiv_t] at coeff
  simpa only [coeff, algebraMap_eq] using (mem_support_iff.mp vin).isUnit.map MvPolynomial.C
end GlobalTheory.NoetherInt
