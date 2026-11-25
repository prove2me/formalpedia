-- Prove2me | solution 1 for GlobalTheory.T.test_function_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:25:38.755991+00:00
-- url     : https://prove2.me/submissions/cff1cb7b-cd7e-474e-ae48-c5a63d4bf309

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TestFunctionExists
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TestFunctionExistsStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_MassTest_testEx


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Mass
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : TestEx := by
  first | exact @GlobalTheory.CompanionTheory.SW.MassTest.testEx | exact GlobalTheory.CompanionTheory.SW.MassTest.testEx | (intros; apply GlobalTheory.CompanionTheory.SW.MassTest.testEx <;> assumption)
end _root_.GlobalTheory.T
