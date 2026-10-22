-- Prove2me | solution 1 for MatrixAnalytic.PH.finite_support_is_discrete_PH
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:45:14.898498+00:00
-- url     : https://prove2.me/submissions/83cc0ed3-e235-49f4-92c0-6ff906a91f4e

import Mathlib
import Definitions.Def_MatrixAnalytic_PH_Discrete

open Matrix
open MatrixAnalytic.PH
@[simp] theorem g69d1_T_nn {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℝ) :
    dTransMat T none none = 1 := rfl
@[simp] theorem g69d1_T_ns {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℝ) (j : ι) :
    dTransMat T none (some j) = 0 := rfl
@[simp] theorem g69d1_T_sn {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℝ) (j : ι) :
    dTransMat T (some j) none = dExitProbs T j := rfl
@[simp] theorem g69d1_T_ss {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℝ) (i j : ι) :
    dTransMat T (some i) (some j) = T i j := rfl

theorem g69d1_P_none {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℝ) (k : ℕ) :
    (dTransMat T ^ k) none none = 1 ∧ ∀ j, (dTransMat T ^ k) none (some j) = 0 := by
  induction k with
  | zero => simp [Matrix.one_apply]
  | succ k ih =>
    refine ⟨?_, fun j => ?_⟩
    · rw [pow_succ, Matrix.mul_apply, Fintype.sum_option]
      simp [ih.1, ih.2]
    · rw [pow_succ, Matrix.mul_apply, Fintype.sum_option]
      simp [ih.1, ih.2]

theorem g69d1_P_some {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℝ) (k : ℕ) :
    ∀ i j, (dTransMat T ^ k) (some i) (some j) = (T ^ k) i j := by
  induction k with
  | zero => intro i j; simp [Matrix.one_apply]
  | succ k ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply, Fintype.sum_option, pow_succ, Matrix.mul_apply]
    simp [ih]

theorem g69d1_P_rowsum {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℝ) (k : ℕ) :
    (dTransMat T ^ k) *ᵥ (fun _ => (1:ℝ)) = fun _ => 1 := by
  have h1 : dTransMat T *ᵥ (fun _ => (1:ℝ)) = fun _ => 1 := by
    funext a
    cases a with
    | none => simp [mulVec, dotProduct, Fintype.sum_option]
    | some i =>
      simp [mulVec, dotProduct, Fintype.sum_option, dExitProbs]
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← mulVec_mulVec, h1, ih]

theorem g69d1_P_some_none {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℝ) (k : ℕ)
    (i : ι) : (dTransMat T ^ k) (some i) none = 1 - ((T ^ k) *ᵥ fun _ => (1:ℝ)) i := by
  have := congrFun (g69d1_P_rowsum T k) (some i)
  simp only [mulVec, dotProduct, Fintype.sum_option, mul_one] at this ⊢
  simp only [g69d1_P_some] at this
  linarith

theorem g69d1_dcdf {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : ι → ℝ) (T : Matrix ι ι ℝ)
    (k : ℕ) : dcdf τ T k = 1 - τ ⬝ᵥ ((T ^ k) *ᵥ fun _ => (1 : ℝ)) := by
  unfold dcdf
  rw [Fintype.sum_option]
  simp only [dInitDist, (g69d1_P_none T k).1, g69d1_P_some_none, mul_sub, mul_one,
    Finset.sum_sub_distrib, dInitAtom, dotProduct]
  ring

theorem g69d1_dpmf_succ {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : ι → ℝ) (T : Matrix ι ι ℝ)
    (k : ℕ) : dpmf τ T (k + 1) = τ ⬝ᵥ ((T ^ k) *ᵥ dExitProbs T) := by
  show dcdf τ T (k + 1) - dcdf τ T k = _
  rw [g69d1_dcdf, g69d1_dcdf]
  have : dExitProbs T = (fun _ => (1:ℝ)) - T *ᵥ (fun _ => (1:ℝ)) := by
    funext i; simp [dExitProbs]
  rw [this, mulVec_sub, mulVec_mulVec, ← pow_succ, dotProduct_sub]
  ring

theorem g69d1_dpmf_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : ι → ℝ) (T : Matrix ι ι ℝ) :
    dpmf τ T 0 = dInitAtom τ := by
  show dcdf τ T 0 = _
  rw [g69d1_dcdf]; simp [dInitAtom, dotProduct]

theorem g69d1_shift_mulVec (N : ℕ) (v : Fin N → ℝ) (i : Fin N) :
    ((Matrix.of fun (a b : Fin N) => if (a : ℕ) = (b : ℕ) + 1 then (1:ℝ) else 0) *ᵥ v) i =
      ∑ j : Fin N, if (i : ℕ) = (j : ℕ) + 1 then v j else 0 := by
  simp [mulVec, dotProduct]

theorem g69d1_shift_pow (N : ℕ) (k : ℕ) (i : Fin N) :
    (((Matrix.of fun (a b : Fin N) => if (a : ℕ) = (b : ℕ) + 1 then (1:ℝ) else 0) ^ k) *ᵥ
      dExitProbs (Matrix.of fun (a b : Fin N) => if (a : ℕ) = (b : ℕ) + 1 then (1:ℝ) else 0)) i =
      if (i : ℕ) = k then 1 else 0 := by
  set T : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun a b => if (a : ℕ) = (b : ℕ) + 1 then 1 else 0
  induction k generalizing i with
  | zero =>
    simp only [pow_zero, one_mulVec, dExitProbs]
    have := g69d1_shift_mulVec N (fun _ => 1) i
    rw [this]
    rcases Nat.eq_zero_or_eq_succ_pred (i : ℕ) with h | h
    · simp [h]
    · have hm : (i : ℕ) - 1 < N := by omega
      rw [Finset.sum_eq_single ⟨(i:ℕ) - 1, hm⟩]
      · have h1 : (i:ℕ) = (i:ℕ) - 1 + 1 := by omega
        simp only [Fin.val_mk]; rw [if_pos h1, if_neg (by omega)]; norm_num
      · intro b _ hb; simp only [ite_eq_right_iff, one_ne_zero, imp_false]
        intro h'; apply hb; ext; simp; omega
      · simp
  | succ k ih =>
    rw [pow_succ', ← mulVec_mulVec, g69d1_shift_mulVec]
    simp only [ih]
    by_cases hi : (i : ℕ) = k + 1
    · have hm : k < N := by omega
      rw [Finset.sum_eq_single ⟨k, hm⟩]
      · simp [hi]
      · intro b _ hb; simp only [ite_eq_right_iff]
        intro h1 h2; exact absurd (Fin.ext h2) hb
      · simp
    · rw [if_neg hi]
      refine Finset.sum_eq_zero fun j _ => ?_
      split_ifs <;> first | rfl | (exfalso; omega)

theorem g69d1_finsupp (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (N : ℕ) (hsupp : ∀ k, N < k → p k = 0) (hsum : ∑ k ∈ Finset.range (N + 1), p k = 1) :
    ∃ (n : ℕ) (τ : Fin n → ℝ) (T : Matrix (Fin n) (Fin n) ℝ),
      IsPHdRep τ T ∧ ∀ k : ℕ, dpmf τ T k = p k := by
  set T : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun a b => if (a : ℕ) = (b : ℕ) + 1 then 1 else 0
    with hT
  have hsum' : p 0 + ∑ i : Fin N, p ((i : ℕ) + 1) = 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => p (i + 1)), add_comm, ← Finset.sum_range_succ']
    exact hsum
  have hex : ∀ i, dExitProbs T i = if (i : ℕ) = 0 then 1 else 0 := by
    intro i; simpa using g69d1_shift_pow N 0 i
  refine ⟨N, fun i => p ((i : ℕ) + 1), T, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i j; simp only [hT, Matrix.of_apply]; split_ifs <;> norm_num
  · intro i; rw [hex]; split_ifs <;> norm_num
  · intro i; exact hp _
  · simp only [dInitAtom]; linarith [hp 0]
  · intro k
    cases k with
    | zero => rw [g69d1_dpmf_zero]; simp only [dInitAtom]; linarith
    | succ k =>
      rw [g69d1_dpmf_succ]
      have hpow : ∀ i, (T ^ k *ᵥ dExitProbs T) i = if (i:ℕ) = k then 1 else 0 :=
        g69d1_shift_pow N k
      simp only [dotProduct, hpow, mul_ite, mul_one, mul_zero]
      by_cases hk : k < N
      · rw [Finset.sum_eq_single ⟨k, hk⟩]
        · simp
        · intro b _ hb; rw [if_neg]; intro h; exact hb (Fin.ext h)
        · simp
      · rw [hsupp (k + 1) (by omega)]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [if_neg]; omega

/-- Theorem 2.6.5 (Latouche–Ramaswami, p. 54): every probability distribution on `ℕ` with finite
support is a discrete PH distribution. -/
theorem solution (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (N : ℕ) (hsupp : ∀ k, N < k → p k = 0) (hsum : ∑ k ∈ Finset.range (N + 1), p k = 1) :
    ∃ (n : ℕ) (τ : Fin n → ℝ) (T : Matrix (Fin n) (Fin n) ℝ),
      IsPHdRep τ T ∧ ∀ k : ℕ, dpmf τ T k = p k := by
  exact g69d1_finsupp p hp N hsupp hsum

