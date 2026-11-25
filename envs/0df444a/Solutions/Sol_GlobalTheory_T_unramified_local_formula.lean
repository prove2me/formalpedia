-- Prove2me | solution 1 for GlobalTheory.T.unramified_local_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:25:44.964076+00:00
-- url     : https://prove2.me/submissions/c0a542ea-ddb5-4704-af25-3874165bcc36

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedLocalFormula
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedLocalFormulaStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_unrFormula


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : PositivityTheory.PfSWUS.Loc.UnrFormula := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.unrFormula | exact GlobalTheory.CompanionTheory.UnrDens.unrFormula | (intros; apply GlobalTheory.CompanionTheory.UnrDens.unrFormula <;> assumption)
end _root_.GlobalTheory.T
