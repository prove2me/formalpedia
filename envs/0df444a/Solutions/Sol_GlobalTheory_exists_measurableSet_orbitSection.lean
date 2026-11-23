-- Prove2me | solution 1 for GlobalTheory.exists_measurableSet_orbitSection
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:18:58.598989+00:00
-- url     : https://prove2.me/submissions/3246a38b-9f3e-47cf-8398-e4e1acc81454

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
variable (G X : Type*) [Group G] [Countable G] [MulAction G X] [TopologicalSpace X] [T2Space X]
  [SecondCountableTopology X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [ContinuousConstSMul G X]
namespace GlobalTheory
theorem _root_.solution [ProperlyDiscontinuousSMul G X] :
    ∃ D : Set X, MeasurableSet D ∧ (∀ x, ∃ g : G, g • x ∈ D) ∧
      ∀ x ∈ D, ∀ g : G, g • x ∈ D → g • x = x := by
  refine exists_measurableSet_orbitSection_of_discreteOrbits
    (fun g => (isClosed_eq (continuous_const_smul g) continuous_id).measurableSet) fun x => ?_
  obtain ⟨U, hU, h⟩ := ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self G x
  exact ⟨U, hU, fun g hg => h g ⟨g • x, ⟨x, mem_of_mem_nhds hU, rfl⟩, hg⟩⟩
end GlobalTheory
