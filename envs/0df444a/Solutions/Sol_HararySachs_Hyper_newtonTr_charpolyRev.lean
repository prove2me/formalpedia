-- Prove2me | solution 1 for HararySachs.Hyper.newtonTr_charpolyRev
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-13T04:51:21.306831+00:00
-- url     : https://prove2.me/submissions/f7708a8a-eb11-48e7-bbc5-ac77c40fe9b9

import Mathlib
import Definitions.Def_HararySachs_Hyper_TensorPhi

open HararySachs.Hyper Finset Polynomial

namespace CharRevAux

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Newton's recursion determines the traces uniquely. -/
lemma newtonTr_unique (Φ : Polynomial R) (h0 : Φ.coeff 0 = 1) (t : ℕ → R) (ht0 : t 0 = 0)
    (ht : ∀ n : ℕ, (n : R) * Φ.coeff n = -∑ p ∈ antidiagonal n, t p.1 * Φ.coeff p.2)
    (m : ℕ) : newtonTr Φ m = t m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    cases m with
    | zero => rw [newtonTr, ht0]
    | succ e =>
      have h := ht (e + 1)
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => t a * Φ.coeff b),
        sum_range_succ, Nat.sub_self, h0, mul_one] at h
      rw [newtonTr.eq_2,
        Fin.sum_univ_eq_sum_range (fun j => newtonTr Φ j * Φ.coeff (e + 1 - j))]
      have hs : ∑ j ∈ range (e + 1), newtonTr Φ j * Φ.coeff (e + 1 - j) =
          ∑ j ∈ range (e + 1), t j * Φ.coeff (e + 1 - j) :=
        sum_congr rfl fun j hj => by rw [ih j (mem_range.mp hj)]
      rw [hs]
      linear_combination -h

/-- Leibniz expansion of a determinant with one column replaced. -/
lemma det_updateCol_eq (A : Matrix (Fin n) (Fin n) R[X]) (j : Fin n) (v : Fin n → R[X]) :
    (A.updateCol j v).det =
      ∑ σ : Equiv.Perm (Fin n),
        Equiv.Perm.sign σ • ((∏ i ∈ univ.erase j, A (σ i) i) * v (σ j)) := by
  rw [Matrix.det_apply]
  refine sum_congr rfl fun σ _ => ?_
  congr 1
  rw [← mul_prod_erase univ _ (mem_univ j), Matrix.updateCol_self, mul_comm]
  congr 1
  refine prod_congr rfl fun i hi => ?_
  rw [Matrix.updateCol_ne (ne_of_mem_erase hi)]

/-- Jacobi's formula: `(det A)' = tr(adj A · A')`. -/
lemma derivative_det (A : Matrix (Fin n) (Fin n) R[X]) :
    derivative A.det = (A.adjugate * A.map derivative).trace := by
  classical
  have h2 : (A.adjugate * A.map derivative).trace =
      ∑ j, (A.updateCol j (fun k => derivative (A k j))).det := by
    unfold Matrix.trace
    refine sum_congr rfl fun j _ => ?_
    rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
    simp [Matrix.diag, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [h2, Matrix.det_apply, map_sum]
  simp_rw [det_updateCol_eq]
  rw [sum_comm]
  refine sum_congr rfl fun σ _ => ?_
  rw [← smul_sum, Units.smul_def, Units.smul_def, map_zsmul, derivative_prod_finset]

/-- Newton's identities for `det(1 - X M)` with the traces `tr(M^a)`. -/
lemma newton_charpolyRev (M : Matrix (Fin n) (Fin n) R) (m : ℕ) :
    (m : R) * M.charpolyRev.coeff m =
      -∑ p ∈ antidiagonal m,
        (if p.1 = 0 then 0 else (M ^ p.1).trace) * M.charpolyRev.coeff p.2 := by
  classical
  set A : Matrix (Fin n) (Fin n) R[X] := 1 - (X : R[X]) • M.map C with hA
  have hp : M.charpolyRev = A.det := rfl
  set B := A.adjugate with hB
  set Bk : ℕ → Matrix (Fin n) (Fin n) R := fun k => Matrix.of fun i j => (B i j).coeff k
    with hBk
  have hBA : B - (X : R[X]) • (B * M.map C) = A.det • (1 : Matrix (Fin n) (Fin n) R[X]) := by
    rw [hB, ← Matrix.adjugate_mul A, hA, mul_sub, mul_one, Matrix.mul_smul]
  have hc0 : M.charpolyRev.coeff 0 = 1 := by
    rw [coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
  -- the coefficients of the adjugate
  have hrec0 : Bk 0 = 1 := by
    ext i j
    have h := congrArg (fun N : Matrix (Fin n) (Fin n) R[X] => (N i j).coeff 0) hBA
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, coeff_sub, coeff_X_mul_zero,
      sub_zero, Matrix.one_apply, mul_ite, mul_one, mul_zero] at h
    simp only [hBk, Matrix.of_apply, h, Matrix.one_apply]
    split_ifs
    · rw [← hp, hc0]
    · rw [coeff_zero]
  have hrec : ∀ k, Bk (k + 1) = Bk k * M + M.charpolyRev.coeff (k + 1) • 1 := by
    intro k
    ext i j
    have h := congrArg (fun N : Matrix (Fin n) (Fin n) R[X] => (N i j).coeff (k + 1)) hBA
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, coeff_sub, coeff_X_mul,
      Matrix.mul_apply, Matrix.map_apply, finsetSum_coeff, coeff_mul_C, Matrix.one_apply,
      mul_ite, mul_one, mul_zero] at h
    simp only [hBk, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [← hp] at h
    split_ifs with hij
    · subst hij; simp only [if_true] at h; linear_combination h
    · simp only [hij, if_false, coeff_zero] at h; linear_combination h
  have hclosed : ∀ k, Bk k = ∑ q ∈ antidiagonal k, M.charpolyRev.coeff q.2 • M ^ q.1 := by
    intro k
    induction k with
    | zero => simp [hrec0, hc0]
    | succ k ih =>
      rw [hrec, ih, Finset.Nat.sum_antidiagonal_succ, sum_mul, add_comm]
      simp only [pow_zero, smul_mul_assoc, ← pow_succ]
  -- Jacobi for `A = 1 - X M`
  have hder : derivative A.det = -(B * M.map C).trace := by
    rw [derivative_det]
    have hAd : A.map derivative = -M.map C := by
      ext i j
      simp only [hA, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.one_apply, Matrix.neg_apply]
      split_ifs <;> simp [derivative_mul]
    rw [hAd, Matrix.mul_neg, Matrix.trace_neg]
  have htr : ∀ k, ((B * M.map C).trace).coeff k = (Bk k * M).trace := by
    intro k
    simp only [Matrix.trace, Matrix.diag, finsetSum_coeff, Matrix.mul_apply, Matrix.map_apply,
      coeff_mul_C, hBk, Matrix.of_apply]
  cases m with
  | zero => simp
  | succ k =>
    have h1 : ((k + 1 : ℕ) : R) * M.charpolyRev.coeff (k + 1) =
        (derivative M.charpolyRev).coeff k := by
      rw [coeff_derivative]; push_cast; ring
    rw [h1, hp, hder, coeff_neg, htr, hclosed k, sum_mul, Matrix.trace_sum,
      Finset.Nat.sum_antidiagonal_succ]
    simp only [if_true, zero_mul, zero_add, Nat.add_one_ne_zero, if_false]
    congr 1
    refine sum_congr rfl fun q _ => ?_
    rw [smul_mul_assoc, Matrix.trace_smul, ← pow_succ, smul_eq_mul, mul_comm, ← hp]

end CharRevAux

open CharRevAux in
theorem solution {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (e : ℕ) (he : 1 ≤ e) :
    newtonTr M.charpolyRev e = (M ^ e).trace := by
  have hc0 : M.charpolyRev.coeff 0 = 1 := by
    rw [coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
  rw [newtonTr_unique M.charpolyRev hc0 (fun a => if a = 0 then 0 else (M ^ a).trace)
    (by simp) (newton_charpolyRev M) e, if_neg (by omega)]
