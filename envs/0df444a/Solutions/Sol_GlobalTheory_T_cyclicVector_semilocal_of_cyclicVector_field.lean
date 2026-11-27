-- Prove2me | solution 1 for GlobalTheory.T.cyclicVector_semilocal_of_cyclicVector_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T06:24:15.805264+00:00
-- url     : https://prove2.me/submissions/ce6de22a-a12c-48f2-a185-dc2f306e6488

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CyclicVectorSemilocalOfCyclicVectorField
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CyclicVectorSemilocalOfCyclicVectorFieldStatement
import Theorems.Thm_GlobalTheory_RegSS_Semilocal_cyclicSemilocal_of_cyclicField


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
theorem _root_.solution : GlobalTheory.RegSS.CyclicField → GlobalTheory.RegSS.CyclicSemilocal := by
  first | exact @GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField | exact GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField | (intros; apply GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField <;> assumption)
end _root_.GlobalTheory.T
