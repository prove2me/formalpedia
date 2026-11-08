-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.basisFunction_wave_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:07:04.707582+00:00
-- url     : https://prove2.me/submissions/e7b43f0e-def7-4a8f-b6ac-44c7c8af10d0

import Mathlib
import Definitions.Def_OAIQ098G072
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_u_factored_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_v_factored_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma basisFunction_wave_g_oai (d : Bool) (n j : ℕ) (t : ℝ) :
    basisFunction d n j t = waveAmplitude d n j t*Complex.exp (-Complex.I*Real.pi*t*n) := by
  cases d <;> simp only [basisFunction,waveAmplitude,Bool.false_eq_true,ite_false, if_false,ite_true, if_true]
  · rw [u_factored_g]; ring
  · rw [v_factored_g]; ring

end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.basisFunction_wave_g_oai := @OAI.SharpPlanar.IntegerBasis.basisFunction_wave_g_oai
