-- Prove2me | solution 1 for OAI.SharpPlanar.transformedIntegrand_disk_bound_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:47:38.440678+00:00
-- url     : https://prove2.me/submissions/2839bff2-129e-4fa5-b1f8-457c2ea56237

import Mathlib
import Definitions.Def_OAIQ098E018
import Theorems.Thm_OAI_SharpPlanar_complexTransformedFactor_disk_bound_e
import Theorems.Thm_OAI_SharpPlanar_finiteDensity_disk_bound_e
import Theorems.Thm_OAI_SharpPlanar_numerical_moment_bound_e

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

lemma transformedIntegrand_disk_bound_e_oai (c d : ℕ → ℝ)
    (hw : ∑ n ∈ Finset.range 101, (|c n|+|d n|) ≤ 3)
    {j : ℕ} (hj : j < 6) {t : ℂ} (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6)
    {m y : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 100) (hy : |y| ≤ 3/2) (ell : ℕ) :
    ‖finiteDensity c d j t * complexTransformedFactor m y ell t‖ ≤ (10:ℝ)^53 := by
  rw [norm_mul]
  calc
    _ ≤ (1000*Real.exp (100*Real.pi/6))*(5*Real.exp (Real.pi*(87/5))) :=
      mul_le_mul (finiteDensity_disk_bound_e c d hw hj ht)
        (complexTransformedFactor_disk_bound_e hj ht hm0 hm1 hy ell) (norm_nonneg _) (by positivity)
    _ = 5000*Real.exp ((100*Real.pi/6)+Real.pi*(87/5)) := by rw [Real.exp_add]; ring
    _ ≤ 5000*Real.exp 111 := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
      have hp := Real.pi_lt_d4
      linarith
    _ ≤ _ := numerical_moment_bound_e.le

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.transformedIntegrand_disk_bound_e_oai := @OAI.SharpPlanar.transformedIntegrand_disk_bound_e_oai
