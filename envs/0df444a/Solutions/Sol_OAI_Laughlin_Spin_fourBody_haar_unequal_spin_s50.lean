-- Prove2me | solution 1 for OAI.Laughlin.Spin.fourBody_haar_unequal_spin_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T19:09:07.916903+00:00
-- url     : https://prove2.me/submissions/5b69bc47-c9a5-4395-9f7f-97d71b7c3b02

import Mathlib
import Definitions.Def_OAIQ050L024
import Theorems.Thm_OAI_Laughlin_Rotation_source_unequal_spin_haar_zero_s50
import Theorems.Thm_OAI_Laughlin_Spin_fourBody_haar_compressed_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_MultiplicityHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation MeasureTheory
open scoped BigOperators Matrix

theorem fourBody_haar_unequal_spin_s50_oai (Q D E : ℕ) (hD : D+2 ≤ Q) (hE : E+2 ≤ Q)
    (hDE : D ≠ E) (r : OddPairLabel D) (s : OddPairLabel E)
    (M : Matrix (FourWedgeIndex Q) (FourWedgeIndex Q) ℂ) :
    (retainedFourInclusion Q D hD r)ᴴ * matrixIntegral sourceHaar
      (conjugateOrbit (fourBodySpinRepresentation Q) M) * retainedFourInclusion Q E hE s = 0 := by
  rw [fourBody_haar_compressed_s50]
  apply source_unequal_spin_haar_zero_s50
  unfold fourSpinWeight
  omega

end Laughlin.Spin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Spin.fourBody_haar_unequal_spin_s50_oai := @OAI.Laughlin.Spin.fourBody_haar_unequal_spin_s50_oai
