-- Prove2me | solution 1 for GlobalTheory.IsAEOrbitSection.quotMeasure_univ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:18.28981+00:00
-- url     : https://prove2.me/submissions/192ef611-6435-4dae-b669-453d7e821d48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsFundamentalDomainAndQuotMeasureEq
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_quotMeasure_apply

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
theorem _root_.solution (hD : IsAEOrbitSection G D μ) : quotMeasure G μ univ = μ D := by
  rw [hD.quotMeasure_apply MeasurableSet.univ, preimage_univ, univ_inter]
end GlobalTheory.IsAEOrbitSection
