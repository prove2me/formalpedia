-- Prove2me | solution 1 for GlobalTheory.T.consequence_of_mackey
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:33:55.098204+00:00
-- url     : https://prove2.me/submissions/7937dfd6-9374-4aa5-99f6-34466def9e89

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConsequenceOfMackey
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConsequenceOfMackeyStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_FromMackey_fromMackey


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.FromMackey := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.FromMackey.fromMackey | exact GlobalTheory.CompanionTheory.TyFin.FromMackey.fromMackey | (intros; apply GlobalTheory.CompanionTheory.TyFin.FromMackey.fromMackey <;> assumption)
end _root_.GlobalTheory.T
