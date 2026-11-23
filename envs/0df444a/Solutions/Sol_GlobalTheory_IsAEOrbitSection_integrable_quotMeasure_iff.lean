-- Prove2me | solution 1 for GlobalTheory.IsAEOrbitSection.integrable_quotMeasure_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:19.598173+00:00
-- url     : https://prove2.me/submissions/e5e10635-cbc7-4101-a6dd-6ed48ca498dd

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
theorem _root_.solution (hD : IsAEOrbitSection G D μ) {E : Type*} [NormedAddCommGroup E]
    {f : Quotient (MulAction.orbitRel G X) → E} (hf : AEStronglyMeasurable f (quotMeasure G μ)) :
    Integrable f (quotMeasure G μ) ↔ IntegrableOn (fun x => f (Quotient.mk _ x)) D μ :=
  (hD.measurePreserving_mk.integrable_comp hf).symm
end GlobalTheory.IsAEOrbitSection
