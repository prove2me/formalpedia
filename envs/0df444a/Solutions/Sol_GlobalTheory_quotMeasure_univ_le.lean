-- Prove2me | solution 1 for GlobalTheory.quotMeasure_univ_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:18:58.95722+00:00
-- url     : https://prove2.me/submissions/a1e2df2a-4126-45df-ab6d-0a6e52a36f53

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
namespace GlobalTheory
theorem _root_.solution {B : Set X} (hB : NullMeasurableSet B μ)
    (hc : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ B) : quotMeasure G μ univ ≤ μ B := by
  refine (quotMeasure_le_map_restrict hB hc univ).trans_eq ?_
  rw [measure_map_restrict_apply μ B MeasurableSet.univ, preimage_univ, univ_inter]
end GlobalTheory
