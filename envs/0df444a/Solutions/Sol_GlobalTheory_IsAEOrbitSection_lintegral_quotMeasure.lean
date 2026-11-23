-- Prove2me | solution 1 for GlobalTheory.IsAEOrbitSection.lintegral_quotMeasure
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:19.648872+00:00
-- url     : https://prove2.me/submissions/b2ed8032-7a9c-48d3-9f81-dd4ebf430c28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsFundamentalDomainAndQuotMeasureEq
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_measurePreserving_mk

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
    {f : Quotient (MulAction.orbitRel G X) → ℝ≥0∞} (hf : AEMeasurable f (quotMeasure G μ)) :
    ∫⁻ q, f q ∂quotMeasure G μ = ∫⁻ x in D, f (Quotient.mk _ x) ∂μ := by
  rw [hD.quotMeasure_eq] at hf ⊢
  exact lintegral_map' hf hD.measurePreserving_mk.measurable.aemeasurable
end GlobalTheory.IsAEOrbitSection
