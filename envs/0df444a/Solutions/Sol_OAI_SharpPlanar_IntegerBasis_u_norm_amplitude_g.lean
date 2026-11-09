-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.u_norm_amplitude_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:12:33.29221+00:00
-- url     : https://prove2.me/submissions/4cff6893-f52d-48ba-bb5f-272403265410

import Mathlib
import Definitions.Def_OAIQ098G322
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_u_factored_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_unit_phase_norm_g

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

lemma u_norm_amplitude_g_oai (n j : ℕ) (t : ℝ) : ‖u n j t‖ = ‖uAmplitude n j t‖ := by
  rw [u_factored_g]
  have he : -2*(Real.pi:ℂ)^2*Complex.exp (-Complex.I*Real.pi*t*n)*
      (basisBeta n j-(t:ℂ)*basisAlpha n j) = Complex.exp (-Complex.I*Real.pi*t*n)*uAmplitude n j t := by
    unfold uAmplitude; ring
  rw [he,norm_mul,unit_phase_norm_g,one_mul]

end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.u_norm_amplitude_g_oai := @OAI.SharpPlanar.IntegerBasis.u_norm_amplitude_g_oai
