-- Prove2me | solution 1 for GreedyRS.Budget.lemma6_greedy_phase_budget
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T11:44:06.587959+00:00
-- url     : https://prove2.me/submissions/b1edface-8f40-42ff-9433-81d2d9de96b4

import Mathlib
import Definitions.Def_GreedyRS_Greedy_Setting
import Theorems.Thm_GreedyRS_Budget_ec2_4_tail_sum_bound
import Theorems.Thm_GreedyRS_Budget_ec2_4_normal_tail_bound
import Theorems.Thm_GreedyRS_Budget_ec2_4_geometric_sum

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem solution (γ γ0 σbar : ℝ) (hσbar : 0 < σbar) (hγ0 : γ0 ∈ Set.Ioo 0 γ)
    (n0 : ℕ) (hn0 : 1 ≤ n0) :
    let κ := (γ - γ0) ^ 2 / (2 * σbar ^ 2)
    let β := (1 - Real.exp (-κ))⁻¹
    0 < β ∧ 0 < κ ∧
      GreedyRS.Greedy.Cn0 ((γ - γ0) / σbar) n0 ≤ (n0 : ℝ≥0∞) + ENNReal.ofReal (β * Real.exp (-κ * n0)) := by
  intro κ β
  obtain ⟨h0, h1⟩ := hγ0
  set x := (γ - γ0) / σbar with hxdef
  have hx : 0 < x := div_pos (by linarith) hσbar
  have hκx : κ = x ^ 2 / 2 := by
    simp only [κ, hxdef]; field_simp
  have hκ : 0 < κ := by rw [hκx]; positivity
  have hr1 : Real.exp (-κ) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hβ : 0 < β := inv_pos.2 (by linarith)
  refine ⟨hβ, hκ, ?_⟩
  have hsum : Summable (fun n : ℕ => Real.exp (-((n0 + n : ℕ) : ℝ) * x ^ 2 / 2)) := by
    have hg := (summable_geometric_of_lt_one (Real.exp_pos (-x ^ 2 / 2)).le
      (Real.exp_lt_one_iff.2 (by nlinarith))).mul_left (Real.exp (-(n0 : ℝ) * x ^ 2 / 2))
    refine hg.congr (fun n => ?_)
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1; push_cast; ring
  calc GreedyRS.Greedy.Cn0 x n0
      ≤ (n0 : ℝ≥0∞) + ∑' n : ℕ,
          ENNReal.ofReal (1 - GreedyRS.Greedy.Phi (Real.sqrt ((n0 + n : ℕ) : ℝ) * x)) :=
        GreedyRS.Budget.ec2_4_tail_sum_bound x hx n0 hn0
    _ ≤ (n0 : ℝ≥0∞) + ∑' n : ℕ,
          ENNReal.ofReal (Real.exp (-((n0 + n : ℕ) : ℝ) * x ^ 2 / 2)) := by
        gcongr with n
        have hpos : (0 : ℝ) < ((n0 + n : ℕ) : ℝ) := by
          have : 1 ≤ n0 + n := by omega
          exact_mod_cast this
        have ht : 0 < Real.sqrt ((n0 + n : ℕ) : ℝ) * x := mul_pos (Real.sqrt_pos.2 hpos) hx
        have := GreedyRS.Budget.ec2_4_normal_tail_bound _ ht
        rw [mul_pow, Real.sq_sqrt hpos.le] at this
        convert this using 2; ring
    _ = (n0 : ℝ≥0∞) + ENNReal.ofReal (∑' n : ℕ, Real.exp (-((n0 + n : ℕ) : ℝ) * x ^ 2 / 2)) := by
        rw [ENNReal.ofReal_tsum_of_nonneg (fun n => (Real.exp_pos _).le) hsum]
    _ = (n0 : ℝ≥0∞) + ENNReal.ofReal (β * Real.exp (-κ * n0)) := by
        rw [GreedyRS.Budget.ec2_4_geometric_sum x hx.ne' n0]
        congr 2
        simp only [β, hκx]
        rw [div_eq_inv_mul]
        congr 2
        · congr 2; ring
        · ring
