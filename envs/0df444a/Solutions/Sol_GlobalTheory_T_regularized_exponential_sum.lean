-- Prove2me | solution 1 for GlobalTheory.T.regularized_exponential_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:21:14.603831+00:00
-- url     : https://prove2.me/submissions/2b5a40f2-e420-4356-ab43-b73dd310938a

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RegularizedExponentialSum
import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_FibreFactorHolds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RegularizedExponentialSumStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_ExpSums_expSum_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Classical
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F
set_option maxHeartbeats 1000000
namespace PositivityTheory.Rg.BcB.F
namespace _root_.GlobalTheory.T
theorem _root_.solution : PositivityTheory.Rg.BcB.F.ExpSum := by
  first | exact @GlobalTheory.CompanionTheory.ExpSums.expSum_holds | exact GlobalTheory.CompanionTheory.ExpSums.expSum_holds | (intros; apply GlobalTheory.CompanionTheory.ExpSums.expSum_holds <;> assumption)
end _root_.GlobalTheory.T
end PositivityTheory.Rg.BcB.F
