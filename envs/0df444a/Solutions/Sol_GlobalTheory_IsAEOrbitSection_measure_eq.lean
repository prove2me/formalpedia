-- Prove2me | solution 1 for GlobalTheory.IsAEOrbitSection.measure_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:04.103142+00:00
-- url     : https://prove2.me/submissions/87bf540e-7f76-41ea-a985-dbc6bbfa25bc

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
open GlobalTheory.IsAEOrbitSection
variable {D D' : Set X}
namespace GlobalTheory.IsAEOrbitSection
theorem _root_.solution (hD : IsAEOrbitSection G D μ) (hD' : IsAEOrbitSection G D' μ) : μ D = μ D' :=
  hD.quotMeasure_univ.symm.trans hD'.quotMeasure_univ
end GlobalTheory.IsAEOrbitSection
