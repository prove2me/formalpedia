-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.phase12_periodic_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T15:03:18.134853+00:00
-- url     : https://prove2.me/submissions/5372e14a-3c56-4f3e-bb08-4effc604a331

import Mathlib
import Definitions.Def_OAIQ098E018

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma phase12_periodic_e_oai (n : ℕ) : phase12 (n+12) = phase12 n := by
  unfold phase12
  have he : Complex.I*Real.pi*(((n+12:ℕ):ℂ)/6) =
      Complex.I*Real.pi*((n:ℂ)/6)+2*Real.pi*Complex.I := by push_cast <;> ring
  rw [he,Complex.exp_add,Complex.exp_two_pi_mul_I,mul_one]

end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.phase12_periodic_e_oai := @OAI.SharpPlanar.IntegerBasis.phase12_periodic_e_oai
