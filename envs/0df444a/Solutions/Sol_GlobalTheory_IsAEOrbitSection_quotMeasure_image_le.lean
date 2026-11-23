-- Prove2me | solution 1 for GlobalTheory.IsAEOrbitSection.quotMeasure_image_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:19.618448+00:00
-- url     : https://prove2.me/submissions/d4d3538c-dd9c-4d49-9e3a-ca392be94a83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsFundamentalDomainAndQuotMeasureEq
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_quotMeasure_apply

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
theorem _root_.solution (hD : IsAEOrbitSection G D μ) {A : Set X} (hA : MeasurableSet A) :
    MeasurableSet (Quotient.mk (MulAction.orbitRel G X) '' A) ∧
      quotMeasure G μ (Quotient.mk (MulAction.orbitRel G X) '' A) ≤ μ A := by
  have hm : MeasurableSet (Quotient.mk (MulAction.orbitRel G X) '' A) := by
    have : Quotient.mk (MulAction.orbitRel G X) ⁻¹' Quotient.mk (MulAction.orbitRel G X) '' A = _ :=
      MulAction.quotient_preimage_image_eq_union_mul A (G := G)
    rw [measurableSet_quotient, Quotient.mk''_eq_mk, this]
    exact MeasurableSet.iUnion fun g => hA.const_smul g
  refine ⟨hm, ?_⟩
  rw [hD.quotMeasure_apply hm]
  refine measure_le_of_ae_unique_of_ae_covers (G := G)
    ((measurableSet_quotient.1 hm).nullMeasurableSet.inter hD.nullMeasurableSet)
    hA.nullMeasurableSet ?_ (Eventually.of_forall ?_)
  · filter_upwards [hD.ae_unique] with x hx hxS g hg using hx hxS.2 g hg.2
  · rintro x ⟨⟨a, ha, hax⟩, -⟩
    obtain ⟨g, hg⟩ := Quotient.exact hax
    exact ⟨g, (show g • x = a from hg) ▸ ha⟩
end GlobalTheory.IsAEOrbitSection
