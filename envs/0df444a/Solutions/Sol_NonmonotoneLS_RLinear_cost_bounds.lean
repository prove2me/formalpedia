-- Prove2me | solution 1 for NonmonotoneLS.RLinear.cost_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T19:40:36.734977+00:00
-- url     : https://prove2.me/submissions/5eb682bc-6ca1-40cc-97c9-1e1ea86544b8

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

/-- Lemma 1.1, first sentence (p. 1045): if `∀k, ⟨∇f(x_k), d_k⟩ ≤ 0` then along
the run `f(x_k) ≤ C_k ≤ A_k` for every `k`.  Following Zhang–Hager, but the
auxiliary function `D_k` is replaced by elementary cross-multiplication. -/
theorem solution {n : ℕ} (p : Shared.Params) (r : Rule) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η)
    (hdesc : ∀ k, ⟪gradient f (x k), d k⟫_ℝ ≤ 0) :
    ∀ k, f (x k) ≤ Shared.costC f x η k ∧ Shared.costC f x η k ≤ Shared.avgA f x k := by
  have hη0 (k : ℕ) : 0 ≤ η k := le_trans p.ηmin_nonneg (hrun.eta_mem k).1
  have hη1 (k : ℕ) : η k ≤ 1 := le_trans (hrun.eta_mem k).2 p.ηmax_le_one
  -- Both rules bound the step value by `C_k + p.δ * α k * ⟨∇f (x k), d k⟩` with
  -- `α k > 0`, and `hdesc` makes that correction non-positive.  For Armijo only
  -- membership in the admissible set is used, never its maximality.
  have hstep (k : ℕ) : f (x (k + 1)) ≤ Shared.costC f x η k := by
    have hs : IsStep r p f (x k) (d k) (Shared.costC f x η k) (α k) := hrun.step k
    -- Both rules state the same sufficient-decrease bound; only `α k > 0` and the
    -- form of the step witness differ.
    obtain ⟨hα, hdecr⟩ : 0 < α k ∧
        f (x k + α k • d k) ≤ Shared.costC f x η k + p.δ * α k * ⟪gradient f (x k), d k⟫_ℝ := by
      cases r with
      | wolfe =>
          have hsw : Shared.IsWolfeStep p f (x k) (d k) (Shared.costC f x η k) (α k) := by
            simpa [IsStep] using hs
          exact ⟨hsw.1, hsw.2.1⟩
      | armijo =>
          have hsa : Shared.IsArmijoStep p f (x k) (d k) (Shared.costC f x η k) (α k) := by
            simpa [IsStep] using hs
          obtain ⟨αbar, hαbar, h, hαeq, hg⟩ := hsa
          have hmem := hg.1
          change
            f (x k + (αbar * p.ρ ^ h) • d k) ≤
                Shared.costC f x η k +
                  p.δ * (αbar * p.ρ ^ h) *
                    ⟪gradient f (x k), d k⟫_ℝ ∧
              αbar * p.ρ ^ h ≤ p.μ at hmem
          have hρ : 0 < p.ρ := by linarith [p.one_lt_ρ]
          refine ⟨?_, ?_⟩
          · rw [hαeq]; exact mul_pos hαbar (zpow_pos hρ h)
          · rw [← hαeq] at hmem; exact hmem.1
    calc f (x (k + 1)) = f (x k + α k • d k) := by rw [hrun.update k]
      _ ≤ Shared.costC f x η k + p.δ * α k * ⟪gradient f (x k), d k⟫_ℝ := hdecr
      _ ≤ Shared.costC f x η k := by
        linarith [mul_nonpos_of_nonneg_of_nonpos (mul_nonneg p.δ_pos.le hα.le) (hdesc k)]
  -- `1 ≤ Q_k ≤ k+1`, so every denominator below is positive.
  have hQ : ∀ k : ℕ, (1 : ℝ) ≤ Shared.costQ η k ∧ Shared.costQ η k ≤ (k : ℝ) + 1 := by
    intro k
    induction k with
    | zero => simp [Shared.costQ]
    | succ k ih =>
        have hQ0 : 0 ≤ Shared.costQ η k := by linarith [ih.1]
        refine ⟨?_, ?_⟩
        · change (1 : ℝ) ≤ η k * Shared.costQ η k + 1
          linarith [mul_nonneg (hη0 k) hQ0]
        · change η k * Shared.costQ η k + 1 ≤ ((Nat.succ k : ℕ) : ℝ) + 1
          norm_num only [Nat.cast_succ]
          linarith [mul_nonneg (sub_nonneg.mpr (hη1 k)) hQ0]
  intro k
  induction k with
  | zero => simp [Shared.costC, Shared.avgA]
  | succ k ih =>
      have hQk := hQ k
      have hQk0 : 0 ≤ Shared.costQ η k := by linarith [hQk.1]
      have hQkle : (1 - η k) * Shared.costQ η k ≥ 0 :=
        mul_nonneg (sub_nonneg.mpr (hη1 k)) hQk0
      have ht0 : 0 ≤ η k * Shared.costQ η k := mul_nonneg (hη0 k) hQk0
      have htK : η k * Shared.costQ η k ≤ (k : ℝ) + 1 := by
        nlinarith
      have hden : 0 < η k * Shared.costQ η k + 1 := by linarith
      have hKpos : 0 < (k : ℝ) + 1 := by positivity
      have hKden : 0 < ((k : ℝ) + 1) + 1 := by positivity
      have hC : Shared.costC f x η (k + 1) = (η k * Shared.costQ η k * Shared.costC f x η k + f (x (k + 1))) / (η k * Shared.costQ η k + 1) := by
        simp [Shared.costC, Shared.costQ]
      -- Lower bound `f_{k+1} ≤ C_{k+1}`: after clearing the positive denominator
      -- this is `t (C_k - f_{k+1}) ≥ 0` with `t = η_k Q_k ≥ 0`.
      have hlo : f (x (k + 1)) ≤ (η k * Shared.costQ η k * Shared.costC f x η k + f (x (k + 1))) / (η k * Shared.costQ η k + 1) := by
        rw [le_div_iff₀ hden]
        nlinarith [mul_nonneg ht0 (sub_nonneg.mpr (hstep k))]
      -- `D(t) = (t C + f)/(t+1)` is increasing because `(K-t)(C-f) ≥ 0`; this
      -- replaces differentiating the paper's auxiliary `D_k`.
      have hmono : (η k * Shared.costQ η k * Shared.costC f x η k + f (x (k + 1))) / (η k * Shared.costQ η k + 1) ≤ (((k : ℝ) + 1) * Shared.costC f x η k + f (x (k + 1))) / (((k : ℝ) + 1) + 1) := by
        rw [div_le_div_iff₀ hden hKden]
        nlinarith [mul_nonneg (sub_nonneg.mpr htK) (sub_nonneg.mpr (hstep k))]
      -- `C_k ≤ A_k` gives `(k+1) C_k ≤ Σ_{i≤k} f_i`; adding `f_{k+1}` gives `A_{k+1}`.
      have hav : (((k : ℝ) + 1) * Shared.costC f x η k + f (x (k + 1))) / (((k : ℝ) + 1) + 1) ≤ Shared.avgA f x (k + 1) := by
        have hih := ih.2
        rw [Shared.avgA] at hih
        have hnum : ((k : ℝ) + 1) * Shared.costC f x η k + f (x (k + 1))
            ≤ ∑ i ∈ Finset.range ((k + 1) + 1), f (x i) := by
          rw [Finset.sum_range_succ]
          nlinarith [(le_div_iff₀ hKpos).1 hih]
        rw [Shared.avgA]
        have hK2 : 0 < ((k + 1 : ℕ) : ℝ) + 1 := by positivity
        have hcast : ((k : ℝ) + 1) + 1 = ((k + 1 : ℕ) : ℝ) + 1 := by
          push_cast
          ring
        rw [hcast]
        exact (div_le_div_iff_of_pos_right hK2).2 hnum
      refine ⟨?_, ?_⟩
      · rw [hC]; exact hlo
      · rw [hC]; exact hmono.trans hav
