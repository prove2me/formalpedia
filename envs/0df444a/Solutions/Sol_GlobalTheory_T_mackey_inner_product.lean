-- Prove2me | solution 1 for GlobalTheory.T.mackey_inner_product
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:18:25.33026+00:00
-- url     : https://prove2.me/submissions/ed185561-92b9-46f6-b614-1b8df4c1a4a6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MackeyInnerProduct
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MackeyInnerProductStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_MackeyFn_mackeyIp


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
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.MackeyIp := by
  first | exact @GlobalTheory.CompanionTheory.MackeyFn.mackeyIp | exact GlobalTheory.CompanionTheory.MackeyFn.mackeyIp | (intros; apply GlobalTheory.CompanionTheory.MackeyFn.mackeyIp <;> assumption)
end _root_.GlobalTheory.T
