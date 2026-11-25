-- Prove2me | solution 1 for GlobalTheory.PMonE.generalLemma_allOrders
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:37:45.218347+00:00
-- url     : https://prove2.me/submissions/a7ac947a-79f0-448f-9088-bec50ced2086

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemSurjectivityAndCountOrderZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemGeneralLemmaOrderOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemIntegralSurjectivityOfOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemIntegralSolutionCountOfOrderOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemGeneralLemmaAllOrders
import Theorems.Thm_GlobalTheory_T_additiveSystemIntegralSolutionCount_of_order_one
import Theorems.Thm_GlobalTheory_T_additiveSystemIntegralSurjectivity_of_one
import Theorems.Thm_GlobalTheory_T_additiveSystem_generalLemma_orderOne
import Theorems.Thm_GlobalTheory_T_additiveSystem_surjectivity_and_count_order_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PMonE
open GlobalTheory
namespace GlobalTheory
namespace PMonE
theorem _root_.solution : ∀ N : ℕ, GLOnto N ∧ GLCount N := by
  intro N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact GlobalTheory.T.additiveSystem_surjectivity_and_count_order_zero
  · exact ⟨GlobalTheory.T.additiveSystemIntegralSurjectivity_of_one N hN GlobalTheory.T.additiveSystem_generalLemma_orderOne.1, GlobalTheory.T.additiveSystemIntegralSolutionCount_of_order_one N hN GlobalTheory.T.additiveSystem_generalLemma_orderOne.2⟩
end PMonE
end GlobalTheory
