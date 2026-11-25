-- Prove2me | solution 1 for GlobalTheory.T.mean_value_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:26:34.128028+00:00
-- url     : https://prove2.me/submissions/23b0b36b-a17b-416b-a5a1-6f696c0d340b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeanValueFormula
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeanValueFormulaStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_meanVal_of_equi_countBd


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
theorem _root_.solution : Equi → CountBd → MeanVal := by
  first | exact @GlobalTheory.CompanionTheory.Mass.MeanV.meanVal_of_equi_countBd | exact GlobalTheory.CompanionTheory.Mass.MeanV.meanVal_of_equi_countBd | (intros; apply GlobalTheory.CompanionTheory.Mass.MeanV.meanVal_of_equi_countBd <;> assumption)
end _root_.GlobalTheory.T
