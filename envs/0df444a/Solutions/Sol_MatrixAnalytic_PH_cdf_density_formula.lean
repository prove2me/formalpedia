-- Prove2me | solution 1 for MatrixAnalytic.PH.cdf_density_formula
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:55:30.447045+00:00
-- url     : https://prove2.me/submissions/028b6c17-2dcf-437f-be37-3e76cf494a7d

import Mathlib
import Definitions.Def_MatrixAnalytic_PH_Continuous

open Matrix
open MatrixAnalytic.PH
open MatrixAnalytic.PH
section g69d1sec
open scoped Norms.Operator

@[simp] theorem g69d1_G_n {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℝ) (b) :
    generator T none b = 0 := rfl
@[simp] theorem g69d1_G_sn {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℝ) (j : ι) :
    generator T (some j) none = exitRates T j := rfl
@[simp] theorem g69d1_G_ss {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℝ) (i j : ι) :
    generator T (some i) (some j) = T i j := rfl

theorem g69d1_Gpow_none {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℝ) (k : ℕ)
    (b : Option ι) : (generator T ^ (k + 1)) none b = 0 := by
  rw [pow_succ', Matrix.mul_apply]; simp

theorem g69d1_Gpow_some {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℝ) (k : ℕ) :
    ∀ i j, (generator T ^ k) (some i) (some j) = (T ^ k) i j := by
  induction k with
  | zero => intro i j; simp [Matrix.one_apply]
  | succ k ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply, Fintype.sum_option, pow_succ, Matrix.mul_apply]
    simp [ih]

theorem g69d1_G_rowsum {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℝ) (k : ℕ) :
    (generator T ^ (k + 1)) *ᵥ (fun _ => (1:ℝ)) = 0 := by
  have h1 : generator T *ᵥ (fun _ => (1:ℝ)) = 0 := by
    funext a
    cases a with
    | none => simp [mulVec, dotProduct, Fintype.sum_option]
    | some i => simp [mulVec, dotProduct, Fintype.sum_option, exitRates]
  rw [pow_succ, ← mulVec_mulVec, h1, mulVec_zero]

theorem g69d1_expser {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℝ) (a b : m) :
    HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹ • M ^ n) a b) (NormedSpace.exp M a b) := by
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) M
  exact Pi.hasSum.1 (Pi.hasSum.1 h a) b

theorem g69d1_exp_ss {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℝ) (x : ℝ)
    (i j : ι) : transFun T x (some i) (some j) = NormedSpace.exp (x • T) i j := by
  have h1 := g69d1_expser (x • generator T) (some i) (some j)
  have h2 := g69d1_expser (x • T) i j
  simp only [smul_pow, Matrix.smul_apply, g69d1_Gpow_some] at h1 h2
  exact h1.unique h2

theorem g69d1_exp_nn {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℝ) (x : ℝ) :
    transFun T x none none = 1 := by
  have h1 := g69d1_expser (x • generator T) none none
  have h2 : HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹ • (x • generator T) ^ n) none none)
      1 := by
    convert hasSum_ite_eq 0 (1:ℝ) using 1
    funext n
    cases n with
    | zero => simp
    | succ n => simp [smul_pow, g69d1_Gpow_none]
  exact h1.unique h2

theorem g69d1_exp_rowsum {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℝ) (x : ℝ)
    (a : Option ι) : ∑ b, transFun T x a b = 1 := by
  have h1 : HasSum (fun n : ℕ => ∑ b, ((n.factorial : ℝ)⁻¹ • (x • generator T) ^ n) a b)
      (∑ b, transFun T x a b) := hasSum_sum fun b _ => g69d1_expser _ a b
  have h2 : HasSum (fun n : ℕ => ∑ b, ((n.factorial : ℝ)⁻¹ • (x • generator T) ^ n) a b) 1 := by
    convert hasSum_ite_eq 0 (1:ℝ) using 1
    funext n
    cases n with
    | zero => simp [Matrix.one_apply]
    | succ n =>
      have := congrFun (g69d1_G_rowsum T n) a
      simp only [mulVec, dotProduct, mul_one, Pi.zero_apply] at this
      simp [smul_pow, ← Finset.mul_sum, this]
  exact h1.unique h2

theorem g69d1_cdf_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ) (x : ℝ) :
    cdf τ T x = 1 - τ ⬝ᵥ (NormedSpace.exp (x • T) *ᵥ fun _ => (1 : ℝ)) := by
  have hsn : ∀ i, transFun T x (some i) none = 1 - (NormedSpace.exp (x • T) *ᵥ fun _ => (1 : ℝ)) i := by
    intro i
    have := g69d1_exp_rowsum T x (some i)
    rw [Fintype.sum_option] at this
    simp only [g69d1_exp_ss, mulVec, dotProduct, mul_one] at this ⊢
    linarith
  unfold cdf
  rw [Fintype.sum_option]
  simp only [initDist, g69d1_exp_nn, hsn, mul_sub, mul_one, Finset.sum_sub_distrib, initAtom,
    dotProduct]
  ring

theorem g69d1_cdf_deriv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ) (x : ℝ) :
    HasDerivAt (cdf τ T) (τ ⬝ᵥ (NormedSpace.exp (x • T) *ᵥ exitRates T)) x := by
  have hc : cdf τ T = fun y => 1 - τ ⬝ᵥ (NormedSpace.exp (y • T) *ᵥ fun _ => (1 : ℝ)) :=
    funext fun y => g69d1_cdf_eq τ T y
  rw [hc]
  let L0 : Matrix ι ι ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun M => τ ⬝ᵥ (M *ᵥ fun _ => (1 : ℝ))
      map_add' := by intro M N; simp [add_mulVec, dotProduct_add]
      map_smul' := by intro c M; simp [smul_mulVec, dotProduct_smul] }
  let L : Matrix ι ι ℝ →L[ℝ] ℝ := LinearMap.toContinuousLinearMap L0
  have hd := (hasDerivAt_exp_smul_const (𝕂 := ℝ) T x)
  have h2 := L.hasFDerivAt.comp_hasDerivAt x hd
  have h3 := h2.const_sub 1
  refine h3.congr_deriv ?_
  show -(τ ⬝ᵥ ((NormedSpace.exp (x • T) * T) *ᵥ fun _ => (1 : ℝ))) = _
  rw [show exitRates T = -(T *ᵥ fun _ => (1:ℝ)) from rfl, mulVec_neg, ← mulVec_mulVec,
    dotProduct_neg]

end g69d1sec

/-- Theorem 2.4.1 (Latouche–Ramaswami, p. 41): if `X` is `PH(τ, T)`, its distribution function is
`F(x) = 1 − τ exp(Tx) 𝟙` for `x ≥ 0` (2.7) and its density is `f(x) = τ exp(Tx) t` for `x > 0`
(2.8), where `t = −T𝟙`. -/
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ) (hrep : IsPHRep τ T) :
    (∀ x : ℝ, 0 ≤ x →
      cdf τ T x = 1 - τ ⬝ᵥ (NormedSpace.exp (x • T) *ᵥ fun _ => (1 : ℝ))) ∧
    (∀ x : ℝ, 0 < x →
      HasDerivAt (cdf τ T) (τ ⬝ᵥ (NormedSpace.exp (x • T) *ᵥ exitRates T)) x) := by
  exact ⟨fun x _ => g69d1_cdf_eq τ T x, fun x _ => g69d1_cdf_deriv τ T x⟩

