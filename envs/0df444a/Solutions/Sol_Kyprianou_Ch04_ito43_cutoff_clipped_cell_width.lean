-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cutoff_clipped_cell_width
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:06:55.869352+00:00
-- url     : https://prove2.me/submissions/c55eea75-21b7-47da-a1a9-5527df9c8fe4

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution (T t : NNReal) (n k : ℕ) :
    let a := min t (T*(k:NNReal)/(n:NNReal))
    let b := min t (T*((k+1:ℕ):NNReal)/(n:NNReal))
    a ≤ b ∧ b ≤ t ∧ (b:ℝ)-(a:ℝ) ≤ (T:ℝ)/(n:ℝ) := by
  intro a b
  let c : NNReal := T*(k:NNReal)/(n:NNReal)
  let d : NNReal := T*((k+1:ℕ):NNReal)/(n:NNReal)
  have hcd : c ≤ d := by
    dsimp [c,d]
    gcongr
    omega
  refine ⟨min_le_min le_rfl hcd,min_le_left _ _,?_⟩
  have hw : (d:ℝ)-(c:ℝ) = (T:ℝ)/(n:ℝ) := by
    dsimp [c,d]
    push_cast
    ring
  change ((min t d:NNReal):ℝ)-((min t c:NNReal):ℝ) ≤ _
  rw [← hw]
  simp only [NNReal.coe_min]
  have hc : (c:ℝ) ≤ (d:ℝ) := by exact_mod_cast hcd
  by_cases h : (t:ℝ) ≤ c
  · rw [min_eq_left h,min_eq_left (h.trans hc)]
    linarith
  · rw [min_eq_right (le_of_not_ge h)]
    linarith [min_le_right (t:ℝ) (d:ℝ)]
