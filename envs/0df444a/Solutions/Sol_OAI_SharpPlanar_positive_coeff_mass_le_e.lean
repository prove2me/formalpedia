-- Prove2me | solution 1 for OAI.SharpPlanar.positive_coeff_mass_le_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:19:29.879234+00:00
-- url     : https://prove2.me/submissions/bbe22581-a7e5-4e68-8223-85a3412bf197

import Mathlib
import Definitions.Def_OAIQ098E001
import Theorems.Thm_OAI_SharpPlanar_positive_coeff_mass_e

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

lemma positive_coeff_mass_le_e_oai (j : ℕ) : ∑ l ∈ Finset.Icc (j+1) 6, ‖Pcoeff l‖ ≤ 10 := by
  rw [← positive_coeff_mass_e]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro l hl
    simp only [Finset.mem_Icc] at hl ⊢
    omega
  · intro l _ _; exact norm_nonneg _

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.positive_coeff_mass_le_e_oai := @OAI.SharpPlanar.positive_coeff_mass_le_e_oai
