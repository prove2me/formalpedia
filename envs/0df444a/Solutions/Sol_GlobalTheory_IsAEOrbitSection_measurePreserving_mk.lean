-- Prove2me | solution 1 for GlobalTheory.IsAEOrbitSection.measurePreserving_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:18:50.782802+00:00
-- url     : https://prove2.me/submissions/e68a42ce-e4bf-413c-9300-3447a7d6a094

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
theorem _root_.solution (hD : IsAEOrbitSection G D μ) :
    MeasurePreserving (Quotient.mk (MulAction.orbitRel G X)) (μ.restrict D) (quotMeasure G μ) :=
  ⟨measurable_quotient_mk' (s := MulAction.orbitRel G X), hD.quotMeasure_eq.symm⟩
end GlobalTheory.IsAEOrbitSection
