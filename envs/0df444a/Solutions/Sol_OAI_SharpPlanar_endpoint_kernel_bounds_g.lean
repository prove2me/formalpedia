-- Prove2me | solution 1 for OAI.SharpPlanar.endpoint_kernel_bounds_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T21:21:17.502201+00:00
-- url     : https://prove2.me/submissions/9bc7bbea-8bae-44bb-a667-9830f43769a7

import Mathlib
import Definitions.Def_OAIQ098G362
import Theorems.Thm_OAI_SharpPlanar_lambda_sq_g
import Theorems.Thm_OAI_SharpPlanar_z_sq_g

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

theorem z_im (t : ℝ) : (z t).im = h * (B / (t ^ 2 + h ^ 2) - 1) := by
  simp [z, Complex.div_im, Complex.normSq, pow_two]
  ring

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar


lemma endpoint_kernel_bounds_g_oai (j : Fin 7) :
    ‖lambda ((j.val:ℝ)/6)‖ ≤ lambdaCap j ∧
    ‖z ((j.val:ℝ)/6)‖ ≤ zCap j ∧
    dampingCap j ≤ (z ((j.val:ℝ)/6)).im := by
  have hb : 0 ≤ lambdaCap j := by fin_cases j <;> (first | (simp [lambdaCap]; all_goals first | (norm_num [lambdaCap]; done) | rfl | decide) | (norm_num [lambdaCap]; done) | norm_num [lambdaCap])
  have ha : 0 ≤ zCap j := by fin_cases j <;> (first | (simp [zCap]; all_goals first | (norm_num [zCap]; done) | rfl | decide) | (norm_num [zCap]; done) | norm_num [zCap])
  refine ⟨(sq_le_sq₀ (norm_nonneg _) hb).mp ?_,(sq_le_sq₀ (norm_nonneg _) ha).mp ?_,?_⟩
  · rw [lambda_sq_g]; fin_cases j <;> (first | (simp [lambdaCap,h]; all_goals first | (norm_num [lambdaCap,h]; done) | rfl | decide) | (norm_num [lambdaCap,h]; done) | norm_num [lambdaCap,h])
  · rw [z_sq_g]; fin_cases j <;> (first | (simp [zCap,h]; all_goals first | (norm_num [zCap,h]; done) | rfl | decide) | (norm_num [zCap,h]; done) | norm_num [zCap,h])
  · rw [z_im]; fin_cases j <;> (first | (simp [dampingCap,h,B]; all_goals first | (norm_num [dampingCap,h,B]; done) | rfl | decide) | (norm_num [dampingCap,h,B]; done) | norm_num [dampingCap,h,B])

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.endpoint_kernel_bounds_g_oai := @OAI.SharpPlanar.endpoint_kernel_bounds_g_oai
