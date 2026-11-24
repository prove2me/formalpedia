-- Prove2me | solution 1 for GlobalTheory.SgAlg.WittSplit.finrank_sup_singleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:45:40.579055+00:00
-- url     : https://prove2.me/submissions/2551d45e-d583-47b5-93e6-9ad881aa1a88

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittFreeTuplesSplitQuadraticEtale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SgAlg Matrix Module
noncomputable section
open GlobalTheory GlobalTheory.SgAlg GlobalTheory.SgAlg.WittSplit
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
namespace GlobalTheory.SgAlg.WittSplit
theorem _root_.solution (U : Submodule K V) {v : V} (hv : v ∉ U) :
    finrank K (U ⊔ K ∙ v : Submodule K V) = finrank K U + 1 := by
  have hv0 : v ≠ 0 := fun h => hv (h ▸ U.zero_mem)
  have e := Submodule.finrank_sup_add_finrank_inf_eq U (K ∙ v)
  rw [(Submodule.disjoint_span_singleton_of_notMem hv).eq_bot, finrank_bot,
    finrank_span_singleton hv0] at e
  omega
end GlobalTheory.SgAlg.WittSplit
