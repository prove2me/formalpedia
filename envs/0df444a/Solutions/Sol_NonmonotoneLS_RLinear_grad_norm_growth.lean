-- Prove2me | solution 1 for NonmonotoneLS.RLinear.grad_norm_growth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T20:51:26.099972+00:00
-- url     : https://prove2.me/submissions/844c1f7c-39e6-43d1-8857-c4a0200d05a9

import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps
import Definitions.Def_NonmonotoneLS_RLinear_Run
import Definitions.Def_NonmonotoneLS_RLinear_Regions
import Definitions.Def_NonmonotoneLS_RLinear_Constants

open scoped InnerProductSpace NNReal
open Filter
open NonmonotoneLS
open NonmonotoneLS.RLinear
set_option maxHeartbeats 800000

/-- Eq. (3.7) (p. 1050): along a run whose directions satisfy (2.4)-(2.5) with constants
`c₁, c₂ > 0` at every `k`, whose steps satisfy `α_k ≤ μ`, and for which `∇f` is `L`-Lipschitz on
`L̄`, `‖∇f(x_{k+1})‖ ≤ b ‖∇f(x_k)‖` for every `k`, with `b = 1 + μc₂L`. -/
theorem solution {n : ℕ} (p : Shared.Params) (r : Rule) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hdir : DirectionBounds f x d c₁ c₂)
    (hαμ : ∀ k, α k ≤ p.μ)
    (L : ℝ≥0) (hLip : LipschitzOnWith L (gradient f) (Lbar p f x d)) :
    ∀ k, ‖gradient f (x (k + 1))‖ ≤ bConst p c₂ L * ‖gradient f (x k)‖ := by
  have hdesc (k : ℕ) : ⟪gradient f (x k), d k⟫_ℝ ≤ 0 := by
    have hsq : 0 ≤ c₁ * ‖gradient f (x k)‖ ^ 2 :=
      mul_nonneg hc₁.le (sq_nonneg ‖gradient f (x k)‖)
    have hneg : -c₁ * ‖gradient f (x k)‖ ^ 2 ≤ 0 := by
      simpa only [neg_mul] using neg_nonpos.mpr hsq
    exact (hdir k).1.trans hneg
  have hη_nonneg (k : ℕ) : 0 ≤ η k := p.ηmin_nonneg.trans (hrun.eta_mem k).1
  have haccept (k : ℕ) :
      0 < α k ∧ f (x k + α k • d k) ≤
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
        have hαpos : 0 < α k := by rw [hαeq]; exact mul_pos hαbar (zpow_pos hρpos h)
        refine ⟨hαpos, ?_⟩
        simpa [hαeq] using hmem.1
  have hstep_le_cost (k : ℕ) : f (x (k + 1)) ≤ Shared.costC f x η k := by
    have ha := haccept k
    have hδα : 0 ≤ p.δ * α k := mul_nonneg p.δ_pos.le ha.1.le
    have hcorr : p.δ * α k * ⟪gradient f (x k), d k⟫_ℝ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hδα (hdesc k)
    calc
      f (x (k + 1)) = f (x k + α k • d k) := by rw [hrun.update k]
      _ ≤ Shared.costC f x η k + p.δ * α k * ⟪gradient f (x k), d k⟫_ℝ := ha.2
      _ ≤ Shared.costC f x η k := by linarith
  have hQ_pos : ∀ k : ℕ, 0 < Shared.costQ η k := by
    intro k
    induction k with
    | zero => simp [Shared.costQ]
    | succ k ih =>
        change 0 < η k * Shared.costQ η k + 1
        exact add_pos_of_nonneg_of_pos (mul_nonneg (hη_nonneg k) ih.le) zero_lt_one
  have hC_nonincreasing (k : ℕ) : Shared.costC f x η (k + 1) ≤ Shared.costC f x η k := by
    have ht0 : 0 ≤ η k * Shared.costQ η k := mul_nonneg (hη_nonneg k) (hQ_pos k).le
    have hden : 0 < η k * Shared.costQ η k + 1 :=
      add_pos_of_nonneg_of_pos ht0 zero_lt_one
    have hfnext := hstep_le_cost k
    change (η k * Shared.costQ η k * Shared.costC f x η k + f (x (k + 1))) /
        (η k * Shared.costQ η k + 1) ≤ Shared.costC f x η k
    rw [div_le_iff₀ hden]
    nlinarith
  have hC_le_C0 : ∀ k : ℕ, Shared.costC f x η k ≤ Shared.costC f x η 0 := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact (hC_nonincreasing k).trans ih
  have hx_level : ∀ k : ℕ, x k ∈ levelSet f (x 0) := by
    intro k
    cases k with
    | zero => change f (x 0) ≤ f (x 0); exact le_rfl
    | succ k =>
        change f (x (k + 1)) ≤ f (x 0)
        calc
          f (x (k + 1)) ≤ Shared.costC f x η k := hstep_le_cost k
          _ ≤ Shared.costC f x η 0 := hC_le_C0 k
          _ = f (x 0) := by simp [Shared.costC]
  have hx_bar (k : ℕ) : x k ∈ Lbar p f x d := by
    change Metric.infEDist (x k) (levelSet f (x 0)) ≤ ENNReal.ofReal p.μ * dmax d
    rw [Metric.infEDist_zero_of_mem (hx_level k)]
    exact bot_le
  intro k
  have hαpos : 0 < α k := (haccept k).1
  have hxsub : x (k + 1) - x k = α k • d k := by
    rw [hrun.update k]
    abel
  have hstepnorm : ‖x (k + 1) - x k‖ = α k * ‖d k‖ := by
    rw [hxsub, norm_smul, Real.norm_eq_abs, abs_of_pos hαpos]
  have hmove : ‖x (k + 1) - x k‖ ≤ p.μ * c₂ * ‖gradient f (x k)‖ := by
    calc
      ‖x (k + 1) - x k‖ = α k * ‖d k‖ := hstepnorm
      _ ≤ p.μ * ‖d k‖ := mul_le_mul_of_nonneg_right (hαμ k) (norm_nonneg _)
      _ ≤ p.μ * (c₂ * ‖gradient f (x k)‖) :=
        mul_le_mul_of_nonneg_left (hdir k).2 p.μ_pos.le
      _ = p.μ * c₂ * ‖gradient f (x k)‖ := by ring
  have hlip : ‖gradient f (x (k + 1)) - gradient f (x k)‖ ≤
      (L : ℝ) * ‖x (k + 1) - x k‖ := by
    have hd := hLip.dist_le_mul (x (k + 1)) (hx_bar (k + 1)) (x k) (hx_bar k)
    simpa only [dist_eq_norm] using hd
  have hgrad : ‖gradient f (x (k + 1)) - gradient f (x k)‖ ≤
      (L : ℝ) * (p.μ * c₂ * ‖gradient f (x k)‖) :=
    hlip.trans <| mul_le_mul_of_nonneg_left hmove (by positivity)
  calc
    ‖gradient f (x (k + 1))‖ ≤ ‖gradient f (x (k + 1)) - gradient f (x k)‖ +
        ‖gradient f (x k)‖ := by
      simpa only [sub_add_cancel] using
        (norm_add_le (gradient f (x (k + 1)) - gradient f (x k)) (gradient f (x k)))
    _ ≤ (L : ℝ) * (p.μ * c₂ * ‖gradient f (x k)‖) + ‖gradient f (x k)‖ :=
      add_le_add_left hgrad _
    _ = bConst p c₂ L * ‖gradient f (x k)‖ := by simp only [bConst]; ring
