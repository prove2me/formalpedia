-- Prove2me | solution 1 for GlobalTheory.T.matrixLengthExists_of_elementaryDivisors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:18:19.052403+00:00
-- url     : https://prove2.me/submissions/1d1db189-f607-43f5-bfff-36c8047e995a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MatrixLengthExistsOfElementaryDivisors
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MatrixLengthExistsOfElementaryDivisorsStatement
import Theorems.Thm_GlobalTheory_InertZeta_fracExists_of_smith


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
theorem _root_.solution : Smith → FracExists := by
  first | exact @GlobalTheory.InertZeta.fracExists_of_smith | exact GlobalTheory.InertZeta.fracExists_of_smith | (intros; apply GlobalTheory.InertZeta.fracExists_of_smith <;> assumption)
end _root_.GlobalTheory.T
