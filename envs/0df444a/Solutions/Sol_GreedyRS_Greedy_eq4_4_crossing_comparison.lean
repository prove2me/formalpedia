-- Prove2me | solution 1 for GreedyRS.Greedy.eq4_4_crossing_comparison
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T11:02:51.357794+00:00
-- url     : https://prove2.me/submissions/03a12c8b-340c-49f1-a374-76e2cdc7a5c9

import Mathlib
import Definitions.Def_GreedyRS_Greedy_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open GreedyRS.Greedy in
theorem solution (x : ℕ → ℕ → ℝ) (μ : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (γ σbar γ0 : ℝ) (hσbar : 0 < σbar) (hγ0 : γ0 ∈ Set.Ioo 0 γ)
    (i : ℕ) (hi : 1 ≤ i) (hgap : μ i ≤ μ 0 - γ) (hvar : (v i : ℝ) ≤ σbar ^ 2)
    (hvpos : 0 < v i)
    (hmin : GreedyRS.Greedy.AboveFrom (GreedyRS.Greedy.runMean x 0) 1 (μ 0 - γ0)) :
    GreedyRS.Greedy.crossBelow (GreedyRS.Greedy.runMean x i)
        (GreedyRS.Greedy.boundary (GreedyRS.Greedy.runMean x 0) 1) 1 ≤
      GreedyRS.Greedy.crossTime ((γ - γ0) / σbar) 1
        (fun j => (x i j - μ i) / Real.sqrt (v i)) := by
  set s := Real.sqrt (v i) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (by exact_mod_cast hvpos)
  have hsσ : s ≤ σbar := by
    rw [hs]
    calc Real.sqrt (v i) ≤ Real.sqrt (σbar ^ 2) := Real.sqrt_le_sqrt hvar
      _ = σbar := Real.sqrt_sq hσbar.le
  have hg : 0 < γ - γ0 := by linarith [hγ0.2]
  unfold crossTime
  refine le_iInf₂ fun n hn => ?_
  obtain ⟨hn1, hz⟩ := hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn1
  -- the running mean of alternative `i` at `n` is below the boundary
  have hz' : (∑ j ∈ Finset.range n, x i j) / n < μ i + s * ((γ - γ0) / σbar) := by
    unfold zbar at hz
    rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, div_div, div_lt_iff₀ (by positivity)] at hz
    rw [div_lt_iff₀ hn']
    nlinarith
  have h2 : s * ((γ - γ0) / σbar) ≤ γ - γ0 := by
    rw [mul_div_assoc', div_le_iff₀ hσbar]
    nlinarith
  have hb : μ 0 - γ0 < boundary (runMean x 0) 1 := hmin.2
  have hlt : runMean x i n < boundary (runMean x 0) 1 := by
    have he : runMean x i n = (∑ j ∈ Finset.range n, x i j) / n := rfl
    rw [he]
    linarith
  unfold crossBelow
  exact iInf₂_le n ⟨hn1, hlt⟩
