-- Prove2me | solution 1 for MatrixAnalytic.PH.discrete_pmf_cdf_formula
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:32:59.312981+00:00
-- url     : https://prove2.me/submissions/2683574e-f566-438c-80d2-874c9ee1f973

import Mathlib
import Definitions.Def_MatrixAnalytic_PH_Discrete

open Matrix
open MatrixAnalytic.PH
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

/-- Theorem 2.5.3 (Latouche–Ramaswami, p. 49): if `X` is `PH_d(τ, T)` then `P[X = 0] = τ₀`,
`P[X = k] = τ T^{k−1} t` for `k ≥ 1`, and `P[X ≤ k] = 1 − τ T^k 𝟙` for `k ≥ 0`, where
`τ₀ = 1 − τ𝟙` and `t = 𝟙 − T𝟙`. -/
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ) (hrep : IsPHdRep τ T) :
    dpmf τ T 0 = dInitAtom τ ∧
    (∀ k : ℕ, 1 ≤ k → dpmf τ T k = τ ⬝ᵥ ((T ^ (k - 1)) *ᵥ dExitProbs T)) ∧
    (∀ k : ℕ, dcdf τ T k = 1 - τ ⬝ᵥ ((T ^ k) *ᵥ fun _ => (1 : ℝ))) := by
  refine ⟨g69d1_dpmf_zero τ T, fun k hk => ?_, fun k => g69d1_dcdf τ T k⟩
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simpa using g69d1_dpmf_succ τ T m

