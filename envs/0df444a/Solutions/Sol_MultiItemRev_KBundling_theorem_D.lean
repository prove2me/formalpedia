-- Prove2me | solution 1 for MultiItemRev.KBundling.theorem_D
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T15:13:27.567751+00:00
-- url     : https://prove2.me/submissions/cba007b1-c9d1-4fa7-a2e8-badb68136693

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model
import Theorems.Thm_MultiItemRev_KBundling_explicit_bound

open MeasureTheory
open scoped NNReal ENNReal

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∀ (k : ℕ), 2 ≤ k →
      ∀ (ν : Measure ℝ≥0) [IsProbabilityMeasure ν],
        ENNReal.ofReal (c / Real.log (k : ℝ)) *
            MultiItemRev.Decomp.Rev (Measure.pi (fun _ : Fin k => ν)) ≤
          MultiItemRev.Decomp.BRev (Measure.pi (fun _ : Fin k => ν)) := by
  -- the constant `w` with `w e^{w+1} = 1` (Lambert-W of 1/e)
  obtain ⟨w, hwI, hw⟩ : ∃ w ∈ Set.Icc (0:ℝ) 1, w * Real.exp (w + 1) = 1 := by
    have hcont : ContinuousOn (fun w : ℝ => w * Real.exp (w + 1)) (Set.Icc 0 1) := by
      fun_prop
    have h1 : (1:ℝ) ∈ Set.Icc ((fun w : ℝ => w * Real.exp (w + 1)) 0)
        ((fun w : ℝ => w * Real.exp (w + 1)) 1) := by
      simp only [zero_mul, one_mul, Set.mem_Icc, zero_le_one, true_and]
      have := Real.add_one_le_exp (1 + 1 : ℝ)
      linarith
    exact intermediate_value_Icc (by norm_num) hcont h1
  have hw0 : 0 ≤ w := hwI.1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨Real.log 2 / (24 * (w + 1)), by positivity, ?_⟩
  intro k hk ν _
  have hB := MultiItemRev.KBundling.explicit_bound w hw k hk ν
  have hk2 : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hL : Real.log 2 ≤ Real.log (k:ℝ) := Real.log_le_log (by norm_num) hk2
  have hLpos : 0 < Real.log (k:ℝ) := lt_of_lt_of_le hlog2 hL
  set L := Real.log (k:ℝ)
  set c := Real.log 2 / (24 * (w + 1))
  set A := 8 * (w + 1) * (Real.logb 2 (k:ℝ) + 2)
  have hc0 : 0 ≤ c / L := by positivity
  have hA0 : 0 ≤ A := by
    have : 0 ≤ Real.logb 2 (k:ℝ) := Real.logb_nonneg (by norm_num) (by linarith)
    positivity
  have hprod : c / L * A ≤ 1 := by
    have hlogb : Real.logb 2 (k:ℝ) = L / Real.log 2 := rfl
    simp only [A, c, hlogb]
    rw [div_mul_eq_mul_div, div_le_one hLpos]
    field_simp
    nlinarith
  calc ENNReal.ofReal (c / L) * MultiItemRev.Decomp.Rev (Measure.pi (fun _ : Fin k => ν))
      ≤ ENNReal.ofReal (c / L) * (ENNReal.ofReal A *
          MultiItemRev.Decomp.BRev (Measure.pi (fun _ : Fin k => ν))) := by gcongr
    _ = ENNReal.ofReal (c / L * A) *
          MultiItemRev.Decomp.BRev (Measure.pi (fun _ : Fin k => ν)) := by
        rw [← mul_assoc, ENNReal.ofReal_mul hc0]
    _ ≤ 1 * MultiItemRev.Decomp.BRev (Measure.pi (fun _ : Fin k => ν)) := by
        gcongr
        exact ENNReal.ofReal_le_one.mpr hprod
    _ = _ := one_mul _
