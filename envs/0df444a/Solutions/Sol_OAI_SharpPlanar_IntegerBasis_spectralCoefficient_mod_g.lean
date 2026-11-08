-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.spectralCoefficient_mod_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:09:51.41179+00:00
-- url     : https://prove2.me/submissions/273fb71f-2f3c-44ce-a7e9-59c680acb61f

import Mathlib
import Definitions.Def_OAIQ098G072
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_phase12_mod_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_spectralCoefficient_eq_phase_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma spectralCoefficient_mod_g_oai (n l : ℕ) :
    spectralCoefficient (n%12) l = spectralCoefficient n l := by
  simp only [spectralCoefficient_eq_phase_g]
  rw [← phase12_mod_g (l*(n%12)),← phase12_mod_g (l*n)]
  congr 2
  simp only [Nat.mul_mod, Nat.mod_mod]

end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.spectralCoefficient_mod_g_oai := @OAI.SharpPlanar.IntegerBasis.spectralCoefficient_mod_g_oai
