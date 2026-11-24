-- Prove2me | solution 1 for GlobalTheory.T.pattern_group_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:21:14.608556+00:00
-- url     : https://prove2.me/submissions/974af8d0-c6ad-4988-8c57-0cd39fd0203d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatementStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_PatGrp_patGroup


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
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.PatGroup := by
  first | exact @GlobalTheory.CompanionTheory.PatGrp.patGroup | exact GlobalTheory.CompanionTheory.PatGrp.patGroup | (intros; apply GlobalTheory.CompanionTheory.PatGrp.patGroup <;> assumption)
end _root_.GlobalTheory.T
