-- Prove2me | solution 1 for GlobalTheory.T.additiveSystem_generalLemma_all_orders
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:45:06.309511+00:00
-- url     : https://prove2.me/submissions/e8c194a8-82b8-498d-bb0a-dbeb451e8b1a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemGeneralLemmaAllOrders
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemGeneralLemmaAllOrdersStatement
import Theorems.Thm_GlobalTheory_PMonE_generalLemma_allOrders


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ N : ℕ, GLOnto N ∧ GLCount N := by
  first | exact @GlobalTheory.PMonE.generalLemma_allOrders | exact GlobalTheory.PMonE.generalLemma_allOrders | (intros; apply GlobalTheory.PMonE.generalLemma_allOrders <;> assumption)
end _root_.GlobalTheory.T
