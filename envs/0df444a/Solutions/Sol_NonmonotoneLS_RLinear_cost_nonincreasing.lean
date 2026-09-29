-- Prove2me | solution 1 for NonmonotoneLS.RLinear.cost_nonincreasing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T19:18:25.650978+00:00
-- url     : https://prove2.me/submissions/b7af1d1d-e94c-46dd-b18a-424167403481

import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps
import Definitions.Def_NonmonotoneLS_RLinear_Run
import Definitions.Def_NonmonotoneLS_RLinear_Regions

open scoped InnerProductSpace
open NonmonotoneLS
open NonmonotoneLS.RLinear

/-- Section 3, proof of Theorem 3.1, first display (p. 1050): along a run with
`∀f(x_k) d_k ≤ 0` for each `k`, `f(x_{k+1}) ≤ C_k` and `C_{k+1} ≤ C_k` for each `k`, and every
iterate lies in the level set `𝓛 = {y : f(y) ≤ f(x₀)}`. -/
theorem solution {n : ℕ} (p : Shared.Params) (r : Rule)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η)
    (hdesc : ∀ k, ⟪gradient f (x k), d k⟫_ℝ ≤ 0) :
    (∀ k,
        f (x (k + 1)) ≤ Shared.costC f x η k ∧
        Shared.costC f x η (k + 1) ≤ Shared.costC f x η k) ∧
      ∀ k, x k ∈ levelSet f (x 0) := by
  have hη_nonneg (k : ℕ) : 0 ≤ η k := p.ηmin_nonneg.trans (hrun.eta_mem k).1
  have haccept (k : ℕ) : 0 < α k ∧ f (x k + α k • d k) ≤
      Shared.costC f x η k + p.δ * α k * ⟪gradient f (x k), d k⟫_ℝ := by
    cases r with
    | wolfe =>
        have hs := hrun.step k
        change Shared.IsWolfeStep p f (x k) (d k) (Shared.costC f x η k) (α k) at hs
        exact ⟨hs.1, hs.2.1⟩
    | armijo =>
        have hs := hrun.step k
        change Shared.IsArmijoStep p f (x k) (d k) (Shared.costC f x η k) (α k) at hs
        rcases hs with ⟨αbar, hαbar, h, hαeq, hgreatest⟩
        have hmem := hgreatest.1
        change f (x k + (αbar * p.ρ ^ h) • d k) ≤ Shared.costC f x η k +
            p.δ * (αbar * p.ρ ^ h) * ⟪gradient f (x k), d k⟫_ℝ ∧
            αbar * p.ρ ^ h ≤ p.μ at hmem
        have hρpos : 0 < p.ρ := by linarith [p.one_lt_ρ]
        have hρpowpos : 0 < p.ρ ^ h := zpow_pos hρpos h
        have hαpos : 0 < α k := by
          rw [hαeq]
          exact mul_pos hαbar hρpowpos
        refine ⟨hαpos, ?_⟩
        simpa [hαeq] using hmem.1
  have hstep_le_cost (k : ℕ) :
      f (x (k + 1)) ≤ Shared.costC f x η k := by
    have ha := haccept k
    have hδα : 0 ≤ p.δ * α k := mul_nonneg p.δ_pos.le ha.1.le
    have hcorr : p.δ * α k * ⟪gradient f (x k), d k⟫_ℝ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hδα (hdesc k)
    calc
      f (x (k + 1)) = f (x k + α k • d k) := by rw [hrun.update k]
      _ ≤ Shared.costC f x η k + p.δ * α k * ⟪gradient f (x k), d k⟫_ℝ := ha.2
      _ ≤ Shared.costC f x η k := by
          linarith
  have hQ_pos : ∀ k : ℕ, 0 < Shared.costQ η k := by
    intro k
    induction k with
    | zero =>
        simp [Shared.costQ]
    | succ k ih =>
        change 0 < η k * Shared.costQ η k + 1
        exact add_pos_of_nonneg_of_pos (mul_nonneg (hη_nonneg k) ih.le) zero_lt_one
  have hC_nonincreasing (k : ℕ) :
      Shared.costC f x η (k + 1) ≤ Shared.costC f x η k := by
    have ht0 : 0 ≤ η k * Shared.costQ η k :=
      mul_nonneg (hη_nonneg k) (hQ_pos k).le
    have hden : 0 < η k * Shared.costQ η k + 1 :=
      add_pos_of_nonneg_of_pos ht0 zero_lt_one
    have hfnext := hstep_le_cost k
    change (η k * Shared.costQ η k * Shared.costC f x η k + f (x (k + 1))) /
        (η k * Shared.costQ η k + 1) ≤ Shared.costC f x η k
    rw [div_le_iff₀ hden]
    nlinarith
  have hC_le_C0 :
      ∀ k : ℕ, Shared.costC f x η k ≤ Shared.costC f x η 0 := by
    intro k
    induction k with
    | zero =>
        exact le_rfl
    | succ k ih =>
        exact (hC_nonincreasing k).trans ih
  have hx_level :
      ∀ k : ℕ, x k ∈ levelSet f (x 0) := by
    intro k
    cases k with
    | zero =>
        change f (x 0) ≤ f (x 0)
        exact le_rfl
    | succ k =>
        change f (x (k + 1)) ≤ f (x 0)
        calc
          f (x (k + 1)) ≤ Shared.costC f x η k := hstep_le_cost k
          _ ≤ Shared.costC f x η 0 := hC_le_C0 k
          _ = f (x 0) := by
            simp [Shared.costC]
  exact ⟨
    fun k => ⟨hstep_le_cost k, hC_nonincreasing k⟩,
    hx_level
  ⟩
