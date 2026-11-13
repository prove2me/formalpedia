-- Prove2me | solution 1 for HararySachs.Hyper.newtonTr_prod_one_sub_mul
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-13T03:36:23.367652+00:00
-- url     : https://prove2.me/submissions/45621f39-e730-4f7a-9ffc-327b0c24f2b1

import Mathlib
import Definitions.Def_HararySachs_Hyper_TensorPhi

open HararySachs.Hyper Polynomial Finset

namespace NewtonProdAux

variable {R : Type*} [CommRing R] {ι : Type*}

lemma geom_aux (y : R[X]) (M : ℕ) : (∑ j ∈ Icc 1 M, y ^ j) * (1 - y) = y - y ^ (M + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_Icc_succ_top (by omega), add_mul, ih]
    ring

/-- `X Φ' + (Σ_j p_j X^j) Φ` is divisible by `X^{M+1}` -/
lemma key [DecidableEq ι] (s : Finset ι) (b : ι → R) (M : ℕ) :
    X * derivative (∏ l ∈ s, (1 - C (b l) * X)) +
        (∑ j ∈ Icc 1 M, C (∑ l ∈ s, b l ^ j) * X ^ j) * ∏ l ∈ s, (1 - C (b l) * X) =
      -∑ l ∈ s, C (b l ^ (M + 1)) * (X ^ (M + 1) * ∏ a ∈ s.erase l, (1 - C (b a) * X)) := by
  rw [derivative_prod_finset]
  have hsum : (∑ j ∈ Icc 1 M, C (∑ l ∈ s, b l ^ j) * X ^ j : R[X]) =
      ∑ l ∈ s, ∑ j ∈ Icc 1 M, (C (b l) * X) ^ j := by
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [map_sum, sum_mul]
    exact sum_congr rfl fun l _ => by rw [map_pow, mul_pow]
  rw [hsum, sum_mul, mul_sum, ← sum_add_distrib, ← sum_neg_distrib]
  refine sum_congr rfl fun l hl => ?_
  rw [← mul_prod_erase s (fun a => 1 - C (b a) * X) hl]
  simp only [derivative_sub, derivative_one, derivative_C_mul_X, zero_sub, map_pow]
  linear_combination (∏ a ∈ s.erase l, (1 - C (b a) * X)) * geom_aux (C (b l) * X) M

/-- the coefficientwise Newton identity -/
lemma newton_coeff [DecidableEq ι] (s : Finset ι) (b : ι → R) (d M : ℕ) (hd : 1 ≤ d)
    (hdM : d ≤ M) :
    (d : R) * (∏ l ∈ s, (1 - C (b l) * X)).coeff d +
        ∑ j ∈ Icc 1 d, (∑ l ∈ s, b l ^ j) * (∏ l ∈ s, (1 - C (b l) * X)).coeff (d - j) = 0 := by
  set Φ := ∏ l ∈ s, (1 - C (b l) * X) with hΦ
  have h := congrArg (fun p : R[X] => p.coeff d) (key s b M)
  simp only at h
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [coeff_add, coeff_X_mul, coeff_derivative, sum_mul, finsetSum_coeff, coeff_neg,
    finsetSum_coeff] at h
  simp only [mul_assoc, coeff_C_mul, coeff_X_pow_mul'] at h
  have h0 : ∀ l ∈ s, b l ^ (M + 1) * (if M + 1 ≤ e + 1 then
      (∏ a ∈ s.erase l, (1 - C (b a) * X)).coeff (e + 1 - (M + 1)) else 0) = 0 := by
    intro l _
    rw [if_neg (by omega), mul_zero]
  rw [sum_eq_zero h0, neg_zero] at h
  have hfilter : ∑ j ∈ Icc 1 M, (∑ l ∈ s, b l ^ j) *
      (if j ≤ e + 1 then Φ.coeff (e + 1 - j) else 0) =
      ∑ j ∈ Icc 1 (e + 1), (∑ l ∈ s, b l ^ j) * Φ.coeff (e + 1 - j) := by
    simp only [mul_ite, mul_zero]
    rw [← sum_filter]
    congr 1
    ext j; simp only [mem_filter, mem_Icc]; omega
  rw [hfilter] at h
  rw [← h]
  push_cast
  ring

end NewtonProdAux

open NewtonProdAux in
theorem solution {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι)
    (b : ι → R) (m : ℕ) (hm : 1 ≤ m) :
    newtonTr (∏ l ∈ s, (1 - Polynomial.C (b l) * Polynomial.X)) m = ∑ l ∈ s, b l ^ m := by
  classical
  set Φ := ∏ l ∈ s, (1 - C (b l) * X) with hΦ
  have hΦ0 : Φ.coeff 0 = 1 := by
    rw [hΦ, coeff_zero_prod]
    exact prod_eq_one fun l _ => by simp
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    obtain ⟨e, rfl⟩ : ∃ e, m = e + 1 := ⟨m - 1, by omega⟩
    have hN := newton_coeff s b (e + 1) (e + 1) (by omega) le_rfl
    rw [sum_Icc_succ_top (by omega), Nat.sub_self, hΦ0, mul_one] at hN
    rw [newtonTr, Fin.sum_univ_eq_sum_range (fun j => newtonTr Φ j * Φ.coeff (e + 1 - j)),
      sum_range_succ' (fun j => newtonTr Φ j * Φ.coeff (e + 1 - j))]
    have hz : newtonTr Φ 0 * Φ.coeff (e + 1 - 0) = 0 := by rw [newtonTr, zero_mul]
    rw [hz, add_zero]
    have hsum : ∑ j ∈ range e, newtonTr Φ (j + 1) * Φ.coeff (e + 1 - (j + 1)) =
        ∑ j ∈ Icc 1 e, (∑ l ∈ s, b l ^ j) * Φ.coeff (e + 1 - j) := by
      have hI : Icc 1 e = Ico 1 (e + 1) := by ext j; simp only [mem_Icc, mem_Ico]; omega
      rw [hI, sum_Ico_eq_sum_range, Nat.add_sub_cancel]
      refine sum_congr rfl fun j hj => ?_
      rw [mem_range] at hj
      rw [show 1 + j = j + 1 by omega, ih (j + 1) (by omega) (by omega)]
    rw [hsum]
    linear_combination -hN
