-- Prove2me | solution 1 for GlobalTheory.IsAEOrbitSection.quotMeasure_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:04.161798+00:00
-- url     : https://prove2.me/submissions/c3747e45-2fb9-456c-89c0-81af440b504f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsFundamentalDomainAndQuotMeasureEq
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_quotMeasure_apply_eq_zero_iff

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
theorem _root_.solution (hD : IsAEOrbitSection G D μ) : quotMeasure G μ = 0 ↔ μ = 0 := by
  rw [← Measure.measure_univ_eq_zero, hD.quotMeasure_apply_eq_zero_iff MeasurableSet.univ,
    preimage_univ, Measure.measure_univ_eq_zero]
end GlobalTheory.IsAEOrbitSection
