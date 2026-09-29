-- Prove2me | solution 1 for HighDimStat.SparseLinear.lasso_l2_error_bound
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-27T06:26:17.940814+00:00
-- url     : https://prove2.me/submissions/4d3cbc26-fa10-42a1-84b7-7c1b19b0c311

import Mathlib
import Definitions.Def_HighDimStat_SparseLinear_HasSupport
import Definitions.Def_HighDimStat_SparseLinear_RestrictedEigenvalue
import Definitions.Def_HighDimStat_SparseLinear_IsLagrangianLassoSolution
import Definitions.Def_HighDimStat_SparseLinear_L1Norm
import Definitions.Def_HighDimStat_SparseLinear_LInftyNorm

open HighDimStat.SparseLinear

/-- Counterexample: nothing forces `λ > 0`. With `λ = 0` and noiseless data the Lagrangian Lasso
is least squares, which need not recover `θ*` when `X` has a kernel direction outside the cone.
Take `n = 1`, `d = 2`, `X = [1 0]`, `w = 0`, `θ* = 0`, `S = {0}`, `κ = 1/10`, `λ = 0` and
`θ̂ = e₂`. -/
theorem solution : ¬ (∀ {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ)
    (θstar θhat : Fin d → ℝ) (S : Finset (Fin d)) (κ lam : ℝ)
    (hSupport : HasSupport θstar S)
    (hκ : 0 < κ)
    (hRE : RestrictedEigenvalue X S κ 3)
    (hlam : 2 * linfNorm (fun j => X.transpose.mulVec w j / (n : ℝ)) ≤ lam)
    (hsol : IsLagrangianLassoSolution X (X.mulVec θstar + w) lam θhat),
    Real.sqrt (∑ j, (θhat j - θstar j) ^ 2) ≤ (3 / κ) * Real.sqrt (S.card : ℝ) * lam ∧
    l1Norm (fun j => θhat j - θstar j) ≤
      4 * Real.sqrt (S.card : ℝ) * Real.sqrt (∑ j, (θhat j - θstar j) ^ 2)) := by
  intro H
  set X : Matrix (Fin 1) (Fin 2) ℝ := !![1, 0] with hX
  have hsupp : HasSupport (0 : Fin 2 → ℝ) {0} := fun j _ => rfl
  have hRE : RestrictedEigenvalue X {0} (1 / 10) 3 := by
    intro Δ hC
    unfold ConeSet at hC
    have hc : ({0}ᶜ : Finset (Fin 2)) = {1} := by decide
    rw [hc] at hC
    simp only [Finset.sum_singleton] at hC
    simp [hX, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have h1 := abs_nonneg (Δ 1)
    have h0 := abs_nonneg (Δ 0)
    have hsq : Δ 1 ^ 2 ≤ 9 * Δ 0 ^ 2 := by
      have := mul_le_mul hC hC h1 (by linarith)
      rw [← sq_abs (Δ 1), ← sq_abs (Δ 0)]
      nlinarith
    nlinarith
  have hlam : 2 * linfNorm (fun j => X.transpose.mulVec (0 : Fin 1 → ℝ) j / ((1 : ℕ) : ℝ)) ≤ 0 := by
    unfold linfNorm
    simp
  have hsol : IsLagrangianLassoSolution X (X.mulVec (0 : Fin 2 → ℝ) + 0) 0 ![0, 1] := by
    intro β
    simp [hX, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    positivity
  have h := (H X 0 0 ![0, 1] {0} (1 / 10) 0 hsupp (by norm_num) hRE hlam hsol).1
  simp [Fin.sum_univ_two] at h
  linarith
