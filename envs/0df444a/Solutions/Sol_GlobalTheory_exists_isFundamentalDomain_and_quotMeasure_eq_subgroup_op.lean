-- Prove2me | solution 1 for GlobalTheory.exists_isFundamentalDomain_and_quotMeasure_eq_subgroup_op
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:42:35.9218+00:00
-- url     : https://prove2.me/submissions/d1eece2e-9e15-44c4-b622-ba255b47daa5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsFundamentalDomainAndQuotMeasureEq
import Theorems.Thm_GlobalTheory_countable_of_discrete_subgroup
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
theorem _root_.solution (μ : Measure G)
    [μ.IsMulRightInvariant] :
    (∃ D : Set G, MeasurableSet D ∧ IsFundamentalDomain Γ.op D μ) ∧
      ∀ D : Set G, IsFundamentalDomain Γ.op D μ →
        (μ.restrict D).map (Quotient.mk (MulAction.orbitRel Γ.op G)) = quotMeasure Γ.op μ := by
  have := countable_of_discrete_subgroup Γ
  obtain ⟨D, hD, -, h⟩ := exists_isFundamentalDomain_subgroup_op Γ
  exact ⟨⟨D, hD, h μ⟩, fun D h => (quotMeasure_eq_of_isFundamentalDomain h).symm⟩
end GlobalTheory
