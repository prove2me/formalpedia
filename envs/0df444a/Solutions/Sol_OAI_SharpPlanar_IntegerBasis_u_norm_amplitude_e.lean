-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.u_norm_amplitude_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T04:56:31.861208+00:00
-- url     : https://prove2.me/submissions/b240093a-3b09-45d5-915b-40de5d6c4608

import Mathlib
import Definitions.Def_OAIQ098E111
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

lemma u_factored (n j : ℕ) (t : ℝ) : u n j t =
    -2*(Real.pi:ℂ)^2*Complex.exp (-Complex.I*Real.pi*t*n)*
      (basisBeta n j-(t:ℂ)*basisAlpha n j) := by
  unfold u basisBeta basisAlpha spectralCoefficient
  congr 1
  rw [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  ring

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

lemma u_norm_amplitude_e_oai (n j : ℕ) (t : ℝ) : ‖u n j t‖ = ‖uAmplitude n j t‖ := by
  rw [u_factored]
  have he : -2*(Real.pi:ℂ)^2*Complex.exp (-Complex.I*Real.pi*t*n)*
      (basisBeta n j-(t:ℂ)*basisAlpha n j) = Complex.exp (-Complex.I*Real.pi*t*n)*uAmplitude n j t := by
    unfold uAmplitude; ring
  rw [he,norm_mul,unit_phase_norm_e,one_mul]

end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.u_norm_amplitude_e_oai := @OAI.SharpPlanar.IntegerBasis.u_norm_amplitude_e_oai
