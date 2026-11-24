-- Prove2me | solution 1 for GlobalTheory.T.same_partition_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:22:26.13733+00:00
-- url     : https://prove2.me/submissions/656924a9-7bcf-4776-ba9e-a131ecbf6e98

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SamePartitionStatement
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SamePartitionStatementStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFinSamePart_samePart


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
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.SamePart := by
  first | exact @GlobalTheory.CompanionTheory.TyFinSamePart.samePart | exact GlobalTheory.CompanionTheory.TyFinSamePart.samePart | (intros; apply GlobalTheory.CompanionTheory.TyFinSamePart.samePart <;> assumption)
end _root_.GlobalTheory.T
