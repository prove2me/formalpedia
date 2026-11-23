-- Prove2me | solution 1 for GlobalTheory.exists_isAEOrbitSection
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:19.675768+00:00
-- url     : https://prove2.me/submissions/d4a1c4dc-f6a6-4c50-9609-01c1b0c496c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsFundamentalDomainAndQuotMeasureEq
import Theorems.Thm_GlobalTheory_exists_measurableSet_orbitSection

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
theorem _root_.solution [ProperlyDiscontinuousSMul G X] (μ : Measure X) :
    ∃ D : Set X, MeasurableSet D ∧ IsAEOrbitSection G D μ := by
  obtain ⟨D, hD, hc, hu⟩ := exists_measurableSet_orbitSection G X
  exact ⟨D, hD, isAEOrbitSection_of_forall hD hc hu μ⟩
end GlobalTheory
