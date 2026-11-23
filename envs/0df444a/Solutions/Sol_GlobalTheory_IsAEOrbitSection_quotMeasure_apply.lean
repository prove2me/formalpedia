-- Prove2me | solution 1 for GlobalTheory.IsAEOrbitSection.quotMeasure_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:18:50.923066+00:00
-- url     : https://prove2.me/submissions/88321758-1fd1-493b-b1bc-3c436706d0d9

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
variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X] {μ : Measure X}
variable [Countable G] [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ]
open GlobalTheory.IsAEOrbitSection
variable {D D' : Set X}
namespace GlobalTheory.IsAEOrbitSection
theorem _root_.solution (hD : IsAEOrbitSection G D μ)
    {U : Set (Quotient (MulAction.orbitRel G X))} (hU : MeasurableSet U) :
    quotMeasure G μ U = μ (Quotient.mk (MulAction.orbitRel G X) ⁻¹' U ∩ D) := by
  rw [hD.quotMeasure_eq, measure_map_restrict_apply μ D hU]
end GlobalTheory.IsAEOrbitSection
