-- Prove2me | solution 1 for OAI.SharpPlanar.disk_z_imaginary_simple_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:18:57.017711+00:00
-- url     : https://prove2.me/submissions/18923ef2-9052-421b-b991-ce80bb4b18c7

import Mathlib
import Definitions.Def_OAIQ098G072
import Theorems.Thm_OAI_SharpPlanar_disk_z_imaginary_g

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

lemma disk_z_imaginary_simple_g_oai {j : ℕ} (hj : j < 6) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) :
    -(81/1000:ℝ) < (complexZ t).im := by
  have hh := disk_z_imaginary_g hj ht
  linarith

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.disk_z_imaginary_simple_g_oai := @OAI.SharpPlanar.disk_z_imaginary_simple_g_oai
