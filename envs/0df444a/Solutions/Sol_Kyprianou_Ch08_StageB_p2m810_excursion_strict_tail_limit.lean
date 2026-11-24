-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_excursion_strict_tail_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:27:16.227305+00:00
-- url     : https://prove2.me/submissions/28d34ead-612c-4b82-9c0d-c58c3144c985

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Analysis.SpecificLimits.Basic
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Monotone convergence of height tails. -/
theorem solution :
    ∀ (n : Measure ℝ) (a : ℝ), n (Ici a) < ⊤ →
    Tendsto (fun k : ℕ => (n (Ici (a + 1 / ((k : ℝ)+1)))).toReal)
      atTop (nhds ((n (Ioi a)).toReal)) := by
  intro n a hf
  let c : ℕ → ℝ := fun k => a + 1 / ((k : ℝ)+1)
  have hc : Tendsto c atTop (nhds a) := by
    simpa [c] using (tendsto_const_nhds (x := a)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hp (k : ℕ) : a < c k := by dsimp [c]; linarith [show 0 < (1 : ℝ) / ((k : ℝ)+1) by positivity]
  have hm : Monotone (fun k => Ici (c k)) := by
    intro i j hij
    apply Ici_subset_Ici.mpr
    dsimp [c]
    apply add_le_add_right
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
  have h := tendsto_measure_iUnion_atTop (μ := n) hm
  rw [iUnion_Ici_eq_Ioi_of_lt_of_tendsto hp hc] at h
  exact (ENNReal.tendsto_toReal (ne_of_lt ((measure_mono Ioi_subset_Ici_self).trans_lt hf))).comp h
