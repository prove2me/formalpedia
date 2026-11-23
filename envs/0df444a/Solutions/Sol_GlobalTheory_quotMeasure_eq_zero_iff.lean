-- Prove2me | solution 1 for GlobalTheory.quotMeasure_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:36.180711+00:00
-- url     : https://prove2.me/submissions/7bce50f9-3174-40d8-a233-ecd564b8cf3f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsFundamentalDomainAndQuotMeasureEq
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_quotMeasure_eq_zero_iff
import Theorems.Thm_GlobalTheory_exists_isAEOrbitSection

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
variable (G X : Type*) [Group G] [Countable G] [MulAction G X] [TopologicalSpace X] [T2Space X]
  [SecondCountableTopology X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [ContinuousConstSMul G X]
variable {X}
namespace GlobalTheory
theorem _root_.solution [ProperlyDiscontinuousSMul G X] (μ : Measure X)
    [SMulInvariantMeasure G X μ] : quotMeasure G μ = 0 ↔ μ = 0 := by
  obtain ⟨D, -, hD⟩ := exists_isAEOrbitSection G μ
  exact hD.quotMeasure_eq_zero_iff
end GlobalTheory
