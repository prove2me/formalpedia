-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.v_norm_amplitude_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T04:38:41.705588+00:00
-- url     : https://prove2.me/submissions/107e105f-e0ea-4c5e-9755-362f98a82f7f

import Mathlib
import Definitions.Def_OAIQ098E087
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_unit_phase_norm_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma v_factored (n j : ℕ) (t : ℝ) : v n j t =
    2*Complex.I*Real.pi*Complex.exp (-Complex.I*Real.pi*t*n)*basisAlpha n j := by
  unfold v basisAlpha spectralCoefficient
  rfl

end SharpPlanar.IntegerBasis

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

namespace SharpPlanar.IntegerBasis
open IntegerIntervals IntegerAlpha

lemma v_norm_amplitude_e_oai (n j : ℕ) (t : ℝ) : ‖v n j t‖ = ‖vAmplitude n j‖ := by
  rw [v_factored]
  have he : 2*Complex.I*Real.pi*Complex.exp (-Complex.I*Real.pi*t*n)*basisAlpha n j =
      Complex.exp (-Complex.I*Real.pi*t*n)*vAmplitude n j := by
    unfold vAmplitude; ring
  rw [he,norm_mul,unit_phase_norm_e,one_mul]


end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.v_norm_amplitude_e_oai := @OAI.SharpPlanar.IntegerBasis.v_norm_amplitude_e_oai
