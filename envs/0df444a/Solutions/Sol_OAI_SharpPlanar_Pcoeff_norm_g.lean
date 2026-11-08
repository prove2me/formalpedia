-- Prove2me | solution 1 for OAI.SharpPlanar.Pcoeff_norm_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:12:59.423605+00:00
-- url     : https://prove2.me/submissions/c3abf065-6338-4533-8f84-31ec2c889264

import Mathlib
import Definitions.Def_OAIQ098G072
import Theorems.Thm_OAI_SharpPlanar_b_sq_g

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

theorem Pcoeff_norm_g_oai (j : ℕ) : ‖Pcoeff j‖ = coeffMass j := by
  have hb := b_sq_g
  rcases lt_or_ge j 7 with hj | hj
  · interval_cases j <;>
      apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num [coeffMass])).mp
    all_goals
      rw [← Complex.normSq_eq_norm_sq]
      norm_num [Pcoeff, coeffMass, Complex.normSq]
    all_goals nlinarith [hb]
  · have hj0 : j ≠ 0 := by omega
    have hj1 : j ≠ 1 := by omega
    have hj2 : j ≠ 2 := by omega
    have hj3 : j ≠ 3 := by omega
    have hj4 : j ≠ 4 := by omega
    have hj5 : j ≠ 5 := by omega
    have hj6 : j ≠ 6 := by omega
    simp [Pcoeff, coeffMass]


end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Pcoeff_norm_g_oai := @OAI.SharpPlanar.Pcoeff_norm_g_oai
