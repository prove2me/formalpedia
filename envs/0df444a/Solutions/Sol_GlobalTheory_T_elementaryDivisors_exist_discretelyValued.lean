-- Prove2me | solution 1 for GlobalTheory.T.elementaryDivisors_exist_discretelyValued
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:06:47.890931+00:00
-- url     : https://prove2.me/submissions/3575bee1-7e55-40d2-82c5-b31bf7b38926

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ElementaryDivisorsExistDiscretelyValued
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ElementaryDivisorsExistDiscretelyValuedStatement
import Theorems.Thm_GlobalTheory_InertZeta_elementaryDivisors_exist_discretely_valued


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : Smith := by
  first | exact @GlobalTheory.InertZeta.elementaryDivisors_exist_discretely_valued | exact GlobalTheory.InertZeta.elementaryDivisors_exist_discretely_valued | (intros; apply GlobalTheory.InertZeta.elementaryDivisors_exist_discretely_valued <;> assumption)
end _root_.GlobalTheory.T
