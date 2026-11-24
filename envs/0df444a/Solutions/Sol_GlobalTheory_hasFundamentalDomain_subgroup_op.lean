-- Prove2me | solution 1 for GlobalTheory.hasFundamentalDomain_subgroup_op
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:58:58.181547+00:00
-- url     : https://prove2.me/submissions/2ef16cee-c5bf-447e-aefe-c946c9ce394f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsFundamentalDomainAndQuotMeasureEq
import Theorems.Thm_GlobalTheory_exists_isFundamentalDomain_subgroup_op

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
variable [MeasurableSpace G] [BorelSpace G]
namespace GlobalTheory
theorem _root_.solution (μ : Measure G) : HasFundamentalDomain Γ.op G μ := by
  obtain ⟨D, -, -, h⟩ := exists_isFundamentalDomain_subgroup_op Γ
  exact ⟨D, h μ⟩
end GlobalTheory
