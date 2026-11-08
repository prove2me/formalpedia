-- Prove2me | solution 1 for OAI.SharpPlanar.z_sq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T19:51:01.602248+00:00
-- url     : https://prove2.me/submissions/53d390d3-338f-46bb-8e89-a813a303463c

import Mathlib
import Definitions.Def_OAIQ098G001

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


lemma z_re (t : ℝ) : (z t).re = -B*t/(t^2+h^2) := by
  simp [z,Complex.div_re,Complex.normSq_apply,pow_two]
lemma z_sq_g_oai (t : ℝ) : ‖z t‖^2 = (4/25:ℝ)+(304/225:ℝ)/(t^2+h^2) := by
  have hd : t^2+h^2 ≠ 0 := ne_of_gt (by unfold h; positivity : 0 < t^2+h^2)
  rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,z_re,z_im]
  dsimp [B,h] at hd ⊢
  field_simp
  ring

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.z_sq_g_oai := @OAI.SharpPlanar.z_sq_g_oai
