-- Prove2me | solution 1 for NaculichRegge.regge_color_signature
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T21:52:35.539813+00:00
-- url     : https://prove2.me/submissions/2805b7e9-2b45-4d26-bee2-d3b1282274af

import Definitions.Def_NaculichRegge_TraceBasis

open Polynomial
open NaculichRegge

lemma P_sq : crossing * crossing = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [crossing, Matrix.mul_apply, Fin.sum_univ_succ]

lemma P_Tt2 : crossing * Tt2 * crossing = Tt2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [crossing, Tt2, Matrix.mul_apply, Fin.sum_univ_succ]

lemma P_Tsu2 : crossing * Tsu2 * crossing = -Tsu2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [crossing, Tsu2, Matrix.mul_apply, Fin.sum_univ_succ]

lemma P_C00 : crossing.mulVec C00 = -C00 := by
  ext i
  fin_cases i <;> simp [crossing, C00, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Conjugation by the crossing matrix. -/
noncomputable def cj (A : ColorOp) : ColorOp := crossing * A * crossing

lemma cj_mul (A B : ColorOp) : cj (A * B) = cj A * cj B := by
  unfold cj
  calc crossing * (A * B) * crossing = crossing * A * 1 * B * crossing := by
        simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = crossing * A * (crossing * crossing) * B * crossing := by rw [P_sq]
    _ = crossing * A * crossing * (crossing * B * crossing) := by
        simp only [Matrix.mul_assoc]

lemma cj_sub (A B : ColorOp) : cj (A - B) = cj A - cj B := by
  unfold cj; rw [Matrix.mul_sub, Matrix.sub_mul]

lemma cj_comm (A B : ColorOp) : cj (NaculichRegge.comm A B) = NaculichRegge.comm (cj A) (cj B) := by
  unfold NaculichRegge.comm; rw [cj_sub, cj_mul, cj_mul]

lemma cj_one : cj 1 = 1 := by unfold cj; rw [Matrix.mul_one, P_sq]

lemma cj_pow (A : ColorOp) (n : ℕ) : cj (A ^ n) = cj A ^ n := by
  induction n with
  | zero => simp [cj_one]
  | succ n ih => rw [pow_succ, pow_succ, cj_mul, ih]

lemma neg_pow_smul (A : ColorOp) (n : ℕ) : (-A) ^ n = ((-1 : ℂ[X]) ^ n) • A ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, smul_mul_assoc, mul_neg, ← pow_succ, pow_succ (-1 : ℂ[X]), mul_neg_one,
      neg_smul, smul_neg]

lemma comm_neg_right (A B : ColorOp) : NaculichRegge.comm A (-B) = -NaculichRegge.comm A B := by
  unfold NaculichRegge.comm; noncomm_ring

lemma comm_neg_smul (c : ℂ[X]) (A B : ColorOp) :
    NaculichRegge.comm (-A) (c • B) = (-c) • NaculichRegge.comm A B := by
  unfold NaculichRegge.comm
  rw [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_smul, Matrix.smul_mul, smul_sub, neg_smul,
    neg_smul]

/-- Moving the crossing matrix through `O C₀₀`. -/
lemma key (O : ColorOp) (v : ColorVec) :
    crossing.mulVec (O.mulVec v) = (cj O).mulVec (crossing.mulVec v) := by
  unfold cj
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc (crossing * O), P_sq,
    Matrix.mul_one]

lemma L_pow (n : ℕ) :
    crossing.mulVec ((Tsu2 ^ n).mulVec C00) = ((-1 : ℂ[X]) ^ (n + 1)) • (Tsu2 ^ n).mulVec C00 := by
  have hc : cj Tsu2 = -Tsu2 := P_Tsu2
  rw [key, cj_pow, hc, P_C00, neg_pow_smul, Matrix.mulVec_neg, Matrix.smul_mulVec,
    pow_succ, mul_neg_one, neg_smul]

lemma cj_tt (m : ℕ) : cj ((NaculichRegge.comm Tt2)^[m] Tsu2) = -((NaculichRegge.comm Tt2)^[m] Tsu2) := by
  induction m with
  | zero => exact P_Tsu2
  | succ m ih =>
    rw [Function.iterate_succ_apply', cj_comm, ih, show cj Tt2 = Tt2 from P_Tt2, comm_neg_right]

lemma L_tt (m : ℕ) :
    crossing.mulVec (((NaculichRegge.comm Tt2)^[m] Tsu2).mulVec C00) = ((NaculichRegge.comm Tt2)^[m] Tsu2).mulVec C00 := by
  rw [key, cj_tt, P_C00, Matrix.neg_mulVec, Matrix.mulVec_neg, neg_neg]

lemma cj_su (m : ℕ) :
    cj ((NaculichRegge.comm Tsu2)^[m] (NaculichRegge.comm Tt2 Tsu2)) =
      ((-1 : ℂ[X]) ^ (m + 1)) • ((NaculichRegge.comm Tsu2)^[m] (NaculichRegge.comm Tt2 Tsu2)) := by
  induction m with
  | zero =>
    rw [Function.iterate_zero_apply, cj_comm, show cj Tt2 = Tt2 from P_Tt2,
      show cj Tsu2 = -Tsu2 from P_Tsu2, comm_neg_right]
    simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', cj_comm, ih, show cj Tsu2 = -Tsu2 from P_Tsu2,
      comm_neg_smul, pow_succ (-1 : ℂ[X]) (m + 1), mul_neg_one]

lemma L_su (m : ℕ) :
    crossing.mulVec (((NaculichRegge.comm Tsu2)^[m] (NaculichRegge.comm Tt2 Tsu2)).mulVec C00) =
      ((-1 : ℂ[X]) ^ m) • ((NaculichRegge.comm Tsu2)^[m] (NaculichRegge.comm Tt2 Tsu2)).mulVec C00 := by
  rw [key, cj_su, P_C00, Matrix.mulVec_neg, Matrix.smul_mulVec, ← neg_smul, pow_succ,
    mul_neg_one, neg_neg]

theorem solution (i k : ℕ) (h : IsReggeIndex i k) :
    crossing.mulVec (reggeColor i k) = ((-1 : ℂ[X]) ^ (k + 1)) • reggeColor i k := by
  unfold reggeColor
  unfold IsReggeIndex at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, (rfl | rfl)⟩ | ⟨hi, (rfl | rfl | h3)⟩
  · have e : reggeOp 0 0 = 1 := by unfold reggeOp; rw [if_pos rfl]
    rw [e, Matrix.one_mulVec, P_C00]; simp
  · have e : reggeOp 1 1 = Tsu2 ^ 1 := by
      unfold reggeOp; rw [if_neg (by norm_num), if_pos rfl]
    rw [e, L_pow]
  · have e : reggeOp 2 1 = (NaculichRegge.comm Tt2)^[2 - 1] Tsu2 := by
      unfold reggeOp; rw [if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
    rw [e, L_tt]; simp
  · have e : reggeOp 2 2 = Tsu2 ^ 2 := by
      unfold reggeOp; rw [if_neg (by norm_num), if_pos rfl]
    rw [e, L_pow]
  · have e : reggeOp i 1 = (NaculichRegge.comm Tt2)^[i - 1] Tsu2 := by
      unfold reggeOp; rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
    rw [e, L_tt]; simp
  · have e : reggeOp i (i - 1) = (NaculichRegge.comm Tsu2)^[i - 2] (NaculichRegge.comm Tt2 Tsu2) := by
      unfold reggeOp
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
    rw [e, L_su]
    have e2 : i - 1 + 1 = (i - 2) + 2 := by omega
    rw [e2, pow_add]
    norm_num
  · subst h3
    have e : reggeOp k k = Tsu2 ^ k := by
      unfold reggeOp; rw [if_neg (by omega), if_pos rfl]
    rw [e, L_pow]
