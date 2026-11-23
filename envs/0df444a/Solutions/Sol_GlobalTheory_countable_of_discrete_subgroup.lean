-- Prove2me | solution 1 for GlobalTheory.countable_of_discrete_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:18:59.094591+00:00
-- url     : https://prove2.me/submissions/9a3b61cc-a2cb-427a-8924-231bb5388140

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
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] (Γ : Subgroup G) [DiscreteTopology Γ]
namespace GlobalTheory
theorem _root_.solution : Countable Γ :=
  TopologicalSpace.separableSpace_iff_countable.1 inferInstance
end GlobalTheory
