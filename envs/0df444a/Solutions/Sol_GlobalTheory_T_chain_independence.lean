-- Prove2me | solution 1 for GlobalTheory.T.chain_independence
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:04:21.978289+00:00
-- url     : https://prove2.me/submissions/82317d07-c427-447b-a58a-0da24ba550c1

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChainIndependence
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChainIndependenceStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_chainIndep


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
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.ChainIndep := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.chainIndep | exact GlobalTheory.CompanionTheory.TyFin.chainIndep | (intros; apply GlobalTheory.CompanionTheory.TyFin.chainIndep <;> assumption)
end _root_.GlobalTheory.T
