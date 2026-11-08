-- Prove2me | solution 1 for OAI.SharpPlanar.directIntegrand_disk_bound_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:20:24.020808+00:00
-- url     : https://prove2.me/submissions/56930ea0-46d6-4222-86ca-437812083a07

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G1643
import Theorems.Thm_OAI_SharpPlanar_complexDirectFactor_disk_bound_g
import Theorems.Thm_OAI_SharpPlanar_finiteDensity_disk_bound_g
import Theorems.Thm_OAI_SharpPlanar_numerical_moment_bound_g

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
open Complex

lemma directIntegrand_disk_bound_g_oai (c d : ℕ → ℝ)
    (hw : ∑ n ∈ Finset.range 101, (|c n|+|d n|) ≤ 3)
    {j : ℕ} (hj : j < 6) {t : ℂ} (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6)
    {m y : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 100) (hy : |y| ≤ 3/2) (ell : ℕ) :
    ‖finiteDensity c d j t * complexDirectFactor m y ell t‖ ≤ (10:ℝ)^53 := by
  rw [norm_mul]
  calc
    _ ≤ (1000*Real.exp (100*Real.pi/6))*Real.exp (Real.pi*(100/6+13/8)) :=
      mul_le_mul (finiteDensity_disk_bound_g c d hw hj ht)
        (complexDirectFactor_disk_bound_g hj ht hm0 hm1 hy ell) (norm_nonneg _) (by positivity)
    _ ≤ 5000*Real.exp 111 := by
      rw [mul_assoc,← Real.exp_add]
      apply mul_le_mul (by norm_num) _ (Real.exp_pos _).le (by norm_num)
      apply Real.exp_le_exp.mpr
      have hp := Real.pi_lt_d4
      linarith
    _ ≤ _ := numerical_moment_bound_g.le

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.directIntegrand_disk_bound_g_oai := @OAI.SharpPlanar.directIntegrand_disk_bound_g_oai
