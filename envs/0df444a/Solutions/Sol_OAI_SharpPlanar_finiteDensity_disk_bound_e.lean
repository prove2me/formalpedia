-- Prove2me | solution 1 for OAI.SharpPlanar.finiteDensity_disk_bound_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:45:02.477136+00:00
-- url     : https://prove2.me/submissions/9bc7f585-5ad5-4566-a8c6-85dd5a6e884d

import Mathlib
import Definitions.Def_OAIQ098E018
import Theorems.Thm_OAI_SharpPlanar_complexU_disk_bound_e
import Theorems.Thm_OAI_SharpPlanar_complexV_disk_bound_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Cardinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian cardinal functions for planar packing

The cardinal family and Fourier kernel follow the construction in
*A sharp Fourier certificate for planar circle packing* (OpenAI, 2026).
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar
open MeasureTheory Set


lemma finiteDensity_disk_bound_e_oai (c d : ℕ → ℝ)
    (hw : ∑ n ∈ Finset.range 101, (|c n|+|d n|) ≤ 3)
    {j : ℕ} (hj : j < 6) {t : ℂ} (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) :
    ‖finiteDensity c d j t‖ ≤ 1000*Real.exp (100*Real.pi/6) := by
  unfold finiteDensity
  calc
    _ ≤ ∑ n ∈ Finset.range 101, ‖(c n:ℂ)*complexU n j t + (d n:ℂ)*complexV n j t‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range 101, (|c n|+|d n|)*(250*Real.exp (100*Real.pi/6)) := by
      apply Finset.sum_le_sum
      intro n hn
      calc
        _ ≤ ‖(c n:ℂ)*complexU n j t‖ + ‖(d n:ℂ)*complexV n j t‖ := norm_add_le _ _
        _ ≤ |c n| *(250*Real.exp (100*Real.pi/6)) + |d n| *(250*Real.exp (100*Real.pi/6)) := by
          simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
          gcongr
          · exact complexU_disk_bound_e hj (by have := Finset.mem_range.mp hn; omega) ht
          · exact complexV_disk_bound_e hj (by have := Finset.mem_range.mp hn; omega) ht
        _ = _ := by ring
    _ ≤ 3*(250*Real.exp (100*Real.pi/6)) := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right hw (by positivity)
    _ ≤ _ := by have := Real.exp_pos (100*Real.pi/6); linarith

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.finiteDensity_disk_bound_e_oai := @OAI.SharpPlanar.finiteDensity_disk_bound_e_oai
