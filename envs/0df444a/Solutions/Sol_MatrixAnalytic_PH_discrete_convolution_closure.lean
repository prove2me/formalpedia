-- Prove2me | solution 1 for MatrixAnalytic.PH.discrete_convolution_closure
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:58:45.741828+00:00
-- url     : https://prove2.me/submissions/16aab457-ad6a-4623-825a-bb29b7696f93

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

theorem g69d1_conv_abstract (pX pY pZ A B U : ℕ → ℝ) (hX0 : pX 0 = 1 - A 0)
    (hXs : ∀ a, pX (a + 1) = A a - A (a + 1)) (hY0 : pY 0 = 1 - B 0)
    (hYs : ∀ a, pY (a + 1) = B a - B (a + 1)) (hZ0 : pZ 0 = 1 - U 0)
    (hZs : ∀ a, pZ (a + 1) = U a - U (a + 1))
    (hU : ∀ k, U k = A k + ∑ a ∈ Finset.range (k + 1), pX a * B (k - a)) :
    ∀ k, pZ k = ∑ a ∈ Finset.range (k + 1), pX a * pY (k - a) := by
  intro k
  cases k with
  | zero => simp [hZ0, hU, hX0, hY0]; ring
  | succ k =>
    rw [hZs, hU, hU, Finset.sum_range_succ (fun a => pX a * pY (k + 1 - a)),
      Finset.sum_range_succ (fun a => pX a * B (k + 1 - a))]
    have h1 : ∑ a ∈ Finset.range (k + 1), pX a * pY (k + 1 - a) =
        ∑ a ∈ Finset.range (k + 1), (pX a * B (k - a) - pX a * B (k + 1 - a)) := by
      refine Finset.sum_congr rfl fun a ha => ?_
      have : k + 1 - a = (k - a) + 1 := by have := Finset.mem_range.1 ha; omega
      rw [this, hYs]; ring
    rw [h1, Finset.sum_sub_distrib, Nat.sub_self, hXs, hY0]
    ring

theorem g69d1_conv_vec {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (T : Matrix ι ι ℝ) (β : κ → ℝ) (S : Matrix κ κ ℝ) (k : ℕ) :
    ((fromBlocks T (vecMulVec (dExitProbs T) β) 0 S) ^ k *ᵥ fun _ => (1:ℝ)) =
      Sum.elim ((T ^ k *ᵥ fun _ => (1:ℝ)) + ∑ a ∈ Finset.range k,
          (β ⬝ᵥ (S ^ (k - 1 - a) *ᵥ fun _ => (1:ℝ))) • (T ^ a *ᵥ dExitProbs T))
        (S ^ k *ᵥ fun _ => (1:ℝ)) := by
  induction k with
  | zero => funext x; cases x <;> simp
  | succ k ih =>
    rw [pow_succ', ← mulVec_mulVec, ih]
    funext x
    cases x with
    | inr j =>
      simp only [Sum.elim_inr]
      rw [pow_succ', ← mulVec_mulVec]
      simp only [mulVec, dotProduct, Fintype.sum_sum_type, fromBlocks_apply₂₁,
        fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add,
        Sum.elim_inr]
    | inl i =>
      have e1 : (fromBlocks T (vecMulVec (dExitProbs T) β) 0 S *ᵥ
          Sum.elim ((T ^ k *ᵥ fun _ => (1:ℝ)) + ∑ a ∈ Finset.range k,
            (β ⬝ᵥ (S ^ (k - 1 - a) *ᵥ fun _ => (1:ℝ))) • (T ^ a *ᵥ dExitProbs T))
          (S ^ k *ᵥ fun _ => (1:ℝ))) (Sum.inl i) =
          (T *ᵥ ((T ^ k *ᵥ fun _ => (1:ℝ)) + ∑ a ∈ Finset.range k,
            (β ⬝ᵥ (S ^ (k - 1 - a) *ᵥ fun _ => (1:ℝ))) • (T ^ a *ᵥ dExitProbs T))) i +
          dExitProbs T i * (β ⬝ᵥ (S ^ k *ᵥ fun _ => (1:ℝ))) := by
        simp only [mulVec, dotProduct, Fintype.sum_sum_type, fromBlocks_apply₁₁,
          fromBlocks_apply₁₂, Sum.elim_inl, Sum.elim_inr, vecMulVec_apply, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [e1]
      simp only [Sum.elim_inl]
      have hR : ∑ a ∈ Finset.range (k + 1),
          (β ⬝ᵥ (S ^ (k + 1 - 1 - a) *ᵥ fun _ => (1:ℝ))) • (T ^ a *ᵥ dExitProbs T) =
          ∑ a ∈ Finset.range k,
            (β ⬝ᵥ (S ^ (k - 1 - a) *ᵥ fun _ => (1:ℝ))) • (T ^ (a + 1) *ᵥ dExitProbs T) +
          (β ⬝ᵥ (S ^ k *ᵥ fun _ => (1:ℝ))) • dExitProbs T := by
        rw [Finset.sum_range_succ']
        congr 1
        · refine Finset.sum_congr rfl fun a ha => ?_
          have : k + 1 - 1 - (a + 1) = k - 1 - a := by omega
          rw [this]
        · simp
      have hL : T *ᵥ (∑ a ∈ Finset.range k,
            (β ⬝ᵥ (S ^ (k - 1 - a) *ᵥ fun _ => (1:ℝ))) • (T ^ a *ᵥ dExitProbs T)) =
          ∑ a ∈ Finset.range k,
            (β ⬝ᵥ (S ^ (k - 1 - a) *ᵥ fun _ => (1:ℝ))) • (T ^ (a + 1) *ᵥ dExitProbs T) := by
        rw [mulVec_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [mulVec_smul, mulVec_mulVec, ← pow_succ']
      rw [mulVec_add, hL, hR, mulVec_mulVec, ← pow_succ']
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring

theorem g69d1_hgen {σ : Type*} [Fintype σ] [DecidableEq σ] (v : σ → ℝ) (M : Matrix σ σ ℝ) :
    (dpmf v M 0 = 1 - v ⬝ᵥ (M ^ 0 *ᵥ fun _ => (1:ℝ))) ∧
    ∀ a, dpmf v M (a + 1) = v ⬝ᵥ (M ^ a *ᵥ fun _ => (1:ℝ)) -
      v ⬝ᵥ (M ^ (a + 1) *ᵥ fun _ => (1:ℝ)) := by
  refine ⟨by rw [← g69d1_dcdf]; rfl, fun a => ?_⟩
  show dcdf v M (a + 1) - dcdf v M a = _
  rw [g69d1_dcdf, g69d1_dcdf]; ring

theorem g69d1_conv_U {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ) (β : κ → ℝ) (S : Matrix κ κ ℝ) (k : ℕ) :
    Sum.elim τ (dInitAtom τ • β) ⬝ᵥ
      ((Matrix.fromBlocks T (vecMulVec (dExitProbs T) β) 0 S) ^ k *ᵥ fun _ => (1:ℝ)) =
    τ ⬝ᵥ (T ^ k *ᵥ fun _ => (1:ℝ)) + ∑ a ∈ Finset.range (k + 1),
      dpmf τ T a * (β ⬝ᵥ (S ^ (k - a) *ᵥ fun _ => (1:ℝ))) := by
  rw [g69d1_conv_vec, Finset.sum_range_succ', g69d1_dpmf_zero]
  simp only [g69d1_dpmf_succ]
  have hsplit : ∀ (f : ι → ℝ) (g : κ → ℝ), Sum.elim τ (dInitAtom τ • β) ⬝ᵥ Sum.elim f g =
      τ ⬝ᵥ f + dInitAtom τ * (β ⬝ᵥ g) := by
    intro f g
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum, mul_assoc]
  rw [hsplit, dotProduct_add, dotProduct_sum]
  simp only [dotProduct_smul, smul_eq_mul, Nat.sub_zero]
  have : ∀ a ∈ Finset.range k, (β ⬝ᵥ (S ^ (k - 1 - a) *ᵥ fun _ => (1:ℝ))) *
      (τ ⬝ᵥ (T ^ a *ᵥ dExitProbs T)) =
      (τ ⬝ᵥ (T ^ a *ᵥ dExitProbs T)) * (β ⬝ᵥ (S ^ (k - (a + 1)) *ᵥ fun _ => (1:ℝ))) := by
    intro a ha
    have : k - 1 - a = k - (a + 1) := by omega
    rw [this, mul_comm]
  rw [Finset.sum_congr rfl this]
  ring

theorem g69d1_conv {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ) (β : κ → ℝ) (S : Matrix κ κ ℝ)
    (hX : IsPHdRep τ T) (hY : IsPHdRep β S) :
    IsPHdRep (Sum.elim τ (dInitAtom τ • β)) (Matrix.fromBlocks T (vecMulVec (dExitProbs T) β) 0 S) ∧
    ∀ k : ℕ,
      dpmf (Sum.elim τ (dInitAtom τ • β)) (Matrix.fromBlocks T (vecMulVec (dExitProbs T) β) 0 S) k =
        ∑ a ∈ Finset.range (k + 1), dpmf τ T a * dpmf β S (k - a) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rintro (i|i) (j|j)
    · simpa using hX.entry_nonneg i j
    · simpa [vecMulVec_apply] using mul_nonneg (hX.exitProbs_nonneg i) (hY.init_nonneg j)
    · simp
    · simpa using hY.entry_nonneg i j
  · rintro (i|i)
    · have h1 := hX.exitProbs_nonneg i
      have h2 := hY.initAtom_nonneg
      have h3 : dExitProbs (fromBlocks T (vecMulVec (dExitProbs T) β) 0 S) (Sum.inl i) =
          dExitProbs T i * dInitAtom β := by
        simp only [dExitProbs, dInitAtom, mulVec, dotProduct, Fintype.sum_sum_type,
          fromBlocks_apply₁₁, fromBlocks_apply₁₂, vecMulVec_apply, mul_one, ← Finset.mul_sum]
        ring
      rw [h3]; exact mul_nonneg h1 h2
    · have := hY.exitProbs_nonneg i
      simpa [dExitProbs, mulVec, dotProduct, Fintype.sum_sum_type] using this
  · rintro (i|i)
    · simpa using hX.init_nonneg i
    · simpa using mul_nonneg hX.initAtom_nonneg (hY.init_nonneg i)
  · have h1 := hX.initAtom_nonneg
    have h2 := hY.initAtom_nonneg
    have : dInitAtom (Sum.elim τ (dInitAtom τ • β)) = dInitAtom τ * dInitAtom β := by
      simp only [dInitAtom, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.smul_apply,
        smul_eq_mul, ← Finset.mul_sum]
      ring
    rw [this]; exact mul_nonneg h1 h2
  · exact g69d1_conv_abstract _ _ _ (fun k => τ ⬝ᵥ (T ^ k *ᵥ fun _ => (1:ℝ)))
      (fun k => β ⬝ᵥ (S ^ k *ᵥ fun _ => (1:ℝ))) _
      (g69d1_hgen τ T).1 (g69d1_hgen τ T).2 (g69d1_hgen β S).1 (g69d1_hgen β S).2
      (g69d1_hgen _ _).1 (g69d1_hgen _ _).2 (g69d1_conv_U τ T β S)

/-- Theorem 2.6.1 (Latouche–Ramaswami, p. 51): if `X` is `PH_d(τ, T)` with `n` phases and `Y`,
independent of `X`, is `PH_d(β, S)` with `m` phases, then `X + Y` is `PH_d(γ, C)` with `n + m`
phases, `γ = [τ, τ₀β]`, `C = [[T, t·β], [0, S]]`, `(t·β)_ij = t_i β_j`. The law of the
independent sum is the convolution of the two probability mass functions,
`P[X + Y = k] = Σ_{a=0}^{k} P[X = a] P[Y = k − a]`. -/
theorem solution {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ) (β : κ → ℝ) (S : Matrix κ κ ℝ)
    (hX : IsPHdRep τ T) (hY : IsPHdRep β S) :
    IsPHdRep (Sum.elim τ (dInitAtom τ • β)) (Matrix.fromBlocks T (vecMulVec (dExitProbs T) β) 0 S) ∧
    ∀ k : ℕ,
      dpmf (Sum.elim τ (dInitAtom τ • β)) (Matrix.fromBlocks T (vecMulVec (dExitProbs T) β) 0 S) k =
        ∑ a ∈ Finset.range (k + 1), dpmf τ T a * dpmf β S (k - a) := by
  exact g69d1_conv τ T β S hX hY

