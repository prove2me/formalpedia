-- Prove2me | solution 1 for GlobalTheory.RowFubini.relIndex_eq_of_le_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:07:16.577087+00:00
-- url     : https://prove2.me/submissions/ff7225c4-c5ff-43fb-8a88-71bf471088c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarTraceConjEqConstMulKernelImage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Pointwise ENNReal
open GlobalTheory GlobalTheory.RowFubini
namespace GlobalTheory.RowFubini
theorem _root_.solution {G : Type*} [Group G] (H s t : Subgroup G) (hst : s ≤ t)
    (hcov : ∀ g ∈ t, ∃ a ∈ s, a⁻¹ * g ∈ H) : H.relIndex s = H.relIndex t := by
  unfold Subgroup.relIndex Subgroup.index
  refine Nat.card_congr (Equiv.ofBijective (Subgroup.quotientSubgroupOfEmbeddingOfLE H hst)
    ⟨(Subgroup.quotientSubgroupOfEmbeddingOfLE H hst).injective, ?_⟩)
  intro q
  induction q using QuotientGroup.induction_on with
  | H g =>
    obtain ⟨a, ha, hg⟩ := hcov g g.2
    refine ⟨QuotientGroup.mk ⟨a, ha⟩, ?_⟩
    rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simpa using hg
end GlobalTheory.RowFubini
