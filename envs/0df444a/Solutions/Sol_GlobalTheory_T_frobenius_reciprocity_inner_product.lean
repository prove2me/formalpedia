-- Prove2me | solution 1 for GlobalTheory.T.frobenius_reciprocity_inner_product
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:10:46.521946+00:00
-- url     : https://prove2.me/submissions/940fb8fa-2be3-4e64-be67-bf88e57628f7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FrobeniusReciprocityInnerProduct
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FrobeniusReciprocityInnerProductStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_frobIp


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
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.FrobIp := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.frobIp | exact GlobalTheory.CompanionTheory.TyFin.frobIp | (intros; apply GlobalTheory.CompanionTheory.TyFin.frobIp <;> assumption)
end _root_.GlobalTheory.T
