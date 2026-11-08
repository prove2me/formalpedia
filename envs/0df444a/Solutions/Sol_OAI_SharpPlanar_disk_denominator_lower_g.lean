-- Prove2me | solution 1 for OAI.SharpPlanar.disk_denominator_lower_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:15:07.798219+00:00
-- url     : https://prove2.me/submissions/e773a34b-e39a-45b3-aaeb-0faf29ea37ee

import Mathlib
import Definitions.Def_OAIQ098G072
import Theorems.Thm_OAI_SharpPlanar_disk_coordinate_bounds_g

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

lemma disk_denominator_lower_g_oai {j : ℕ} (hj : j < 6) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) :
    7/30 ≤ ‖t+Complex.I*(h:ℂ)‖ := by
  have hi := (disk_coordinate_bounds_g hj ht).2.1
  have hn := (le_abs_self (t+Complex.I*(h:ℂ)).im).trans (Complex.abs_im_le_norm _)
  simp only [Complex.add_im,Complex.I_mul_im,Complex.ofReal_re] at hn
  norm_num [h] at hn ⊢
  linarith

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.disk_denominator_lower_g_oai := @OAI.SharpPlanar.disk_denominator_lower_g_oai
