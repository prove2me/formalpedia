-- Prove2me | solution 1 for GlobalTheory.hasFundamentalDomain_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:58:57.082416+00:00
-- url     : https://prove2.me/submissions/d5f3ef0c-74a9-47b2-93f0-ebe8f0a7d44e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsFundamentalDomainAndQuotMeasureEq
import Theorems.Thm_GlobalTheory_exists_isFundamentalDomain_subgroup

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
theorem _root_.solution (μ : Measure G) : HasFundamentalDomain Γ G μ := by
  obtain ⟨D, -, -, h⟩ := exists_isFundamentalDomain_subgroup Γ
  exact ⟨D, h μ⟩
end GlobalTheory
