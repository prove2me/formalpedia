-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.v_norm_amplitude_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:42:18.377874+00:00
-- url     : https://prove2.me/submissions/2c3da008-0811-4b15-b699-e9db2200a24d

import Mathlib
import Definitions.Def_OAIQ098G235
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_unit_phase_norm_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_v_factored_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar.IntegerBasis
open IntegerIntervals IntegerAlpha

lemma v_norm_amplitude_g_oai (n j : ℕ) (t : ℝ) : ‖v n j t‖ = ‖vAmplitude n j‖ := by
  rw [v_factored_g]
  have he : 2*Complex.I*Real.pi*Complex.exp (-Complex.I*Real.pi*t*n)*basisAlpha n j =
      Complex.exp (-Complex.I*Real.pi*t*n)*vAmplitude n j := by
    unfold vAmplitude; ring
  rw [he,norm_mul,unit_phase_norm_g,one_mul]


end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.v_norm_amplitude_g_oai := @OAI.SharpPlanar.IntegerBasis.v_norm_amplitude_g_oai
