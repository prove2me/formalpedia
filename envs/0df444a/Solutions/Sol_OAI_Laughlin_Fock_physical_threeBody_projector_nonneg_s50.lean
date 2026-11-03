-- Prove2me | solution 1 for OAI.Laughlin.Fock.physical_threeBody_projector_nonneg_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:26:47.741568+00:00
-- url     : https://prove2.me/submissions/d7bf9e0f-c319-496d-a9fc-64eea3a93a12

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L016
import Definitions.Def_OAIQ050L017
import Theorems.Thm_OAI_Laughlin_Fock_sourceThreeHighestEnd_haar_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Exterior_OccupationMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology

theorem occupationNormSq_nonneg (Q : ℕ) (x : Space Q) : 0 ≤ occupationNormSq Q x := by
  unfold occupationNormSq
  positivity

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_ProjectorBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix

theorem physical_threeBody_projector_nonneg_s50_oai (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (x : Space Q) :
    0 ≤ (contractionForm Q (sourceThreeEnd Q)
      ((threeSpinProjector Q hQ z).map Complex.ofReal) x).re := by
  rw [← sourceThreeHighestEnd_haar_s50 Q hQ z]
  exact mul_nonneg (by positivity) (integral_nonneg (fun g => occupationNormSq_nonneg Q _))

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.physical_threeBody_projector_nonneg_s50_oai := @OAI.Laughlin.Fock.physical_threeBody_projector_nonneg_s50_oai
