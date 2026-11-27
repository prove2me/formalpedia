-- Prove2me | solution 1 for GlobalTheory.properlyDiscontinuousSMul_of_discrete_of_properSMul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:41:08.858629+00:00
-- url     : https://prove2.me/submissions/57057127-d362-47a1-b3fc-7427b4e83e57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsFundamentalDomainAndQuotMeasureEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Topology Filter
open scoped Pointwise ENNReal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {G X : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MulAction G X] [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] [ProperSMul G X] (Γ : Subgroup G) [DiscreteTopology Γ] :
    ProperlyDiscontinuousSMul Γ X := by
  have : IsClosed (Γ : Set G) := Subgroup.isClosed_of_discrete
  have : ContinuousSMul G X := ProperSMul.toContinuousSMul
  rw [properlyDiscontinuousSMul_iff_properSMul]
  infer_instance
end GlobalTheory
