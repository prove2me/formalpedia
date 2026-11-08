-- Prove2me | solution 1 for OAI.SharpPlanar.disk_denominator_ne_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:16:28.110902+00:00
-- url     : https://prove2.me/submissions/3e4f88c4-edbf-4d37-bd7e-445b1d9740ad

import Mathlib
import Definitions.Def_OAIQ098G072
import Theorems.Thm_OAI_SharpPlanar_disk_denominator_lower_g

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

lemma disk_denominator_ne_g_oai {j : ℕ} (hj : j < 6) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) : t+Complex.I*(h:ℂ) ≠ 0 := by
  have hb := disk_denominator_lower_g hj ht
  intro he
  rw [he,norm_zero] at hb
  norm_num at hb

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.disk_denominator_ne_g_oai := @OAI.SharpPlanar.disk_denominator_ne_g_oai
