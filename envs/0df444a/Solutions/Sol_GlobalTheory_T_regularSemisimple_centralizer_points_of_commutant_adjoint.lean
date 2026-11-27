-- Prove2me | solution 1 for GlobalTheory.T.regularSemisimple_centralizer_points_of_commutant_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T06:25:05.233839+00:00
-- url     : https://prove2.me/submissions/58b58b90-5e66-481b-9d88-7af7316e379e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RegularSemisimpleCentralizerPointsOfCommutantAdj
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RegularSemisimpleCentralizerPointsOfCommutantAdjStatement
import Theorems.Thm_GlobalTheory_RegSS_pointsCentraliser_of_commutant_of_adjoint


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : GlobalTheory.RegSS.PointsCommutant → GlobalTheory.RegSS.PointsAdjoint → GlobalTheory.RegSS.PointsCentraliser := by
  first | exact @GlobalTheory.RegSS.pointsCentraliser_of_commutant_of_adjoint | exact GlobalTheory.RegSS.pointsCentraliser_of_commutant_of_adjoint | (intros; apply GlobalTheory.RegSS.pointsCentraliser_of_commutant_of_adjoint <;> assumption)
end _root_.GlobalTheory.T
