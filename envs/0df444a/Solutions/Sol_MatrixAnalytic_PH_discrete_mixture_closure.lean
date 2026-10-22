-- Prove2me | solution 1 for MatrixAnalytic.PH.discrete_mixture_closure
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:40:23.36371+00:00
-- url     : https://prove2.me/submissions/7ecc7b84-6645-4800-b603-b720c7ba2685

import Mathlib
import Definitions.Def_MatrixAnalytic_PH_Discrete

open Matrix
open MatrixAnalytic.PH
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

theorem g69d1_fromBlocks_diag_pow {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (T : Matrix ι ι ℝ) (S : Matrix κ κ ℝ) (k : ℕ) :
    (fromBlocks T 0 0 S) ^ k = fromBlocks (T ^ k) 0 0 (S ^ k) := by
  induction k with
  | zero => simp [fromBlocks_one]
  | succ k ih => rw [pow_succ, ih, fromBlocks_multiply]; simp [pow_succ]

theorem g69d1_kron_pow {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (T : Matrix ι ι ℝ) (S : Matrix κ κ ℝ) (k : ℕ) :
    (kronecker T S) ^ k = kronecker (T ^ k) (S ^ k) := by
  induction k with
  | zero => simp [one_kronecker_one]
  | succ k ih => rw [pow_succ, ih, pow_succ, pow_succ]; exact (mul_kronecker_mul _ _ _ _).symm

theorem g69d1_kron_mulVec_one {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) (p : ι × κ) :
    (kronecker A B *ᵥ fun _ => (1:ℝ)) p = (A *ᵥ fun _ => (1:ℝ)) p.1 * (B *ᵥ fun _ => (1:ℝ)) p.2 := by
  obtain ⟨a, b⟩ := p
  simp only [mulVec, dotProduct, mul_one, Fintype.sum_prod_type, Finset.sum_mul_sum]
  rfl

theorem g69d1_rowsum_nonneg {ι : Type*} [Fintype ι] (T : Matrix ι ι ℝ)
    (h : ∀ i j, 0 ≤ T i j) (i : ι) : 0 ≤ (T *ᵥ fun _ => (1:ℝ)) i := by
  simp only [mulVec, dotProduct, mul_one]
  exact Finset.sum_nonneg fun j _ => h i j

theorem g69d1_mix {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ) (β : κ → ℝ) (S : Matrix κ κ ℝ)
    (hX : IsPHdRep τ T) (hY : IsPHdRep β S) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    IsPHdRep (Sum.elim (θ • τ) ((1 - θ) • β)) (Matrix.fromBlocks T 0 0 S) ∧
    ∀ k : ℕ,
      dcdf (Sum.elim (θ • τ) ((1 - θ) • β)) (Matrix.fromBlocks T 0 0 S) k =
        θ * dcdf τ T k + (1 - θ) * dcdf β S k := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, fun k => ?_⟩
  · rintro (i|i) (j|j) <;> simp [hX.entry_nonneg, hY.entry_nonneg]
  · rintro (i|i)
    · have := hX.exitProbs_nonneg i
      simpa [dExitProbs, mulVec, dotProduct, Fintype.sum_sum_type] using this
    · have := hY.exitProbs_nonneg i
      simpa [dExitProbs, mulVec, dotProduct, Fintype.sum_sum_type] using this
  · rintro (i|i)
    · simpa using mul_nonneg hθ0 (hX.init_nonneg i)
    · simpa using mul_nonneg (by linarith) (hY.init_nonneg i)
  · have h1 := hX.initAtom_nonneg
    have h2 := hY.initAtom_nonneg
    simp only [dInitAtom, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.smul_apply,
      smul_eq_mul, ← Finset.mul_sum] at h1 h2 ⊢
    nlinarith [mul_nonneg hθ0 h1, mul_nonneg (sub_nonneg.2 hθ1) h2]
  · rw [g69d1_dcdf, g69d1_dcdf, g69d1_dcdf, g69d1_fromBlocks_diag_pow]
    simp only [dotProduct, mulVec, Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero,
      add_zero, zero_add, Sum.elim_inl, Sum.elim_inr, Pi.smul_apply, smul_eq_mul, mul_one,
      mul_assoc, ← Finset.mul_sum]
    ring

theorem g69d1_min {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ) (β : κ → ℝ) (S : Matrix κ κ ℝ)
    (hX : IsPHdRep τ T) (hY : IsPHdRep β S) :
    IsPHdRep (fun p : ι × κ => τ p.1 * β p.2) (Matrix.kronecker T S) ∧
    ∀ k : ℕ,
      1 - dcdf (fun p : ι × κ => τ p.1 * β p.2) (Matrix.kronecker T S) k =
        (1 - dcdf τ T k) * (1 - dcdf β S k) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, fun k => ?_⟩
  · rintro ⟨i, j⟩ ⟨a, b⟩
    show 0 ≤ T i a * S j b
    exact mul_nonneg (hX.entry_nonneg _ _) (hY.entry_nonneg _ _)
  · rintro ⟨i, j⟩
    have h1 := hX.exitProbs_nonneg i
    have h2 := hY.exitProbs_nonneg j
    have h3 := g69d1_rowsum_nonneg T hX.entry_nonneg i
    have h4 := g69d1_rowsum_nonneg S hY.entry_nonneg j
    simp only [dExitProbs] at h1 h2 ⊢
    rw [g69d1_kron_mulVec_one]
    simp only
    nlinarith [mul_le_one₀ (show (T *ᵥ fun _ => (1:ℝ)) i ≤ 1 by linarith) h4 (show (S *ᵥ fun _ => (1:ℝ)) j ≤ 1 by linarith)]
  · rintro ⟨i, j⟩; exact mul_nonneg (hX.init_nonneg i) (hY.init_nonneg j)
  · have h1 := hX.initAtom_nonneg
    have h2 := hY.initAtom_nonneg
    have h3 : 0 ≤ ∑ i, τ i := Finset.sum_nonneg fun i _ => hX.init_nonneg i
    have h4 : 0 ≤ ∑ i, β i := Finset.sum_nonneg fun i _ => hY.init_nonneg i
    simp only [dInitAtom, Fintype.sum_prod_type, ← Finset.sum_mul_sum] at h1 h2 ⊢
    nlinarith [mul_le_mul_of_nonneg_left (show ∑ i, β i ≤ 1 by linarith) h3]
  · rw [g69d1_dcdf, g69d1_dcdf, g69d1_dcdf, g69d1_kron_pow]
    simp only [sub_sub_cancel]
    simp only [dotProduct, g69d1_kron_mulVec_one, Fintype.sum_prod_type, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

/-- Theorem 2.6.2 (Latouche–Ramaswami, p. 52): if `X` is `PH_d(τ, T)` with `n` phases and `Y` is
`PH_d(β, S)` with `m` phases, with distribution functions `F` and `G`, then for `0 ≤ θ ≤ 1` the
convex mixture `θF + (1 − θ)G` is the distribution function of `PH_d(γ, C)` with `n + m` phases,
`γ = [θτ, (1 − θ)β]`, `C = [[T, 0], [0, S]]`. -/
theorem solution {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ) (β : κ → ℝ) (S : Matrix κ κ ℝ)
    (hX : IsPHdRep τ T) (hY : IsPHdRep β S) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    IsPHdRep (Sum.elim (θ • τ) ((1 - θ) • β)) (Matrix.fromBlocks T 0 0 S) ∧
    ∀ k : ℕ,
      dcdf (Sum.elim (θ • τ) ((1 - θ) • β)) (Matrix.fromBlocks T 0 0 S) k =
        θ * dcdf τ T k + (1 - θ) * dcdf β S k := by
  exact g69d1_mix τ T β S hX hY θ hθ0 hθ1

