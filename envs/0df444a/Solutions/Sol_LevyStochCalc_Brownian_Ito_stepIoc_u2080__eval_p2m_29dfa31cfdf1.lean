-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.stepIoc_u2080__eval_p2m_29dfa31cfdf1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T23:17:22.355518+00:00
-- url     : https://prove2.me/submissions/38630db5-d8ae-47e9-922f-27a59ce2f3cf

import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraAssociativity_F001

open MeasureTheory
open scoped NNReal ENNReal

open LevyStochCalc.Brownian.Ito

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- The source-faithful elementary initial-window integrand is the
indicator of the half-open time interval. -/
theorem solution {b : ℝ} (hb : 0 < b) (s : ℝ) (ω : Ω) :
    (stepIoc₀ Ω hb).eval s ω =
      (Set.Ioc 0 b).indicator (fun _ => (1 : ℝ)) s := by
  have hrw : (stepIoc₀ Ω hb).eval s ω =
      ∑ i : Fin 1, if (![0, b] : Fin 2 → ℝ) i.castSucc < s
            ∧ s ≤ (![0, b] : Fin 2 → ℝ) i.succ
          then (![fun _ => (1 : ℝ)] : Fin 1 → Ω → ℝ) i ω else 0 := rfl
  rw [hrw, Fin.sum_univ_one]
  by_cases h : (0 : ℝ) < s ∧ s ≤ b
  · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr h)]
    simp [h]
  · rw [Set.indicator_of_notMem fun hm => h (Set.mem_Ioc.mp hm)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
      Fin.castSucc_zero, Fin.succ_zero_eq_one]
    exact if_neg h
