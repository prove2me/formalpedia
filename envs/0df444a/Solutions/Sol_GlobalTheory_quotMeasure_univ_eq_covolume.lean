-- Prove2me | solution 1 for GlobalTheory.quotMeasure_univ_eq_covolume
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:10.428629+00:00
-- url     : https://prove2.me/submissions/487d7672-ff48-4c34-b51e-2b0c15c54e7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsFundamentalDomainAndQuotMeasureEq
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_quotMeasure_univ

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
namespace GlobalTheory
theorem _root_.solution [h : HasFundamentalDomain G X μ] :
    quotMeasure G μ univ = covolume G X μ := by
  obtain ⟨D, hD⟩ := h.ExistsIsFundamentalDomain
  rw [(isAEOrbitSection_of_isFundamentalDomain hD).quotMeasure_univ, hD.covolume_eq_volume]
end GlobalTheory
