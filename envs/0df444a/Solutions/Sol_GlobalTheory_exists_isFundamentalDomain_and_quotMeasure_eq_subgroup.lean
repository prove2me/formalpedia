-- Prove2me | solution 1 for GlobalTheory.exists_isFundamentalDomain_and_quotMeasure_eq_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:42:34.938569+00:00
-- url     : https://prove2.me/submissions/153217cb-124f-4ff9-8fbc-8bc239f1405e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsFundamentalDomainAndQuotMeasureEq
import Theorems.Thm_GlobalTheory_countable_of_discrete_subgroup
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
theorem _root_.solution (μ : Measure G)
    [μ.IsMulLeftInvariant] :
    (∃ D : Set G, MeasurableSet D ∧ IsFundamentalDomain Γ D μ) ∧
      ∀ D : Set G, IsFundamentalDomain Γ D μ →
        (μ.restrict D).map (Quotient.mk (MulAction.orbitRel Γ G)) = quotMeasure Γ μ := by
  have := countable_of_discrete_subgroup Γ
  obtain ⟨D, hD, -, h⟩ := exists_isFundamentalDomain_subgroup Γ
  exact ⟨⟨D, hD, h μ⟩, fun D h => (quotMeasure_eq_of_isFundamentalDomain h).symm⟩
end GlobalTheory
