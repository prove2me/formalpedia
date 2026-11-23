-- Prove2me | solution 1 for GlobalTheory.IsAEOrbitSection.sigmaFinite_quotMeasure
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:10.478828+00:00
-- url     : https://prove2.me/submissions/03319cc3-ef96-40ff-b96f-0d5b2a0294f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsFundamentalDomainAndQuotMeasureEq
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_quotMeasure_image_le

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
theorem _root_.solution (hD : IsAEOrbitSection G D μ) [SigmaFinite μ] :
    SigmaFinite (quotMeasure G μ) := by
  refine ⟨⟨⟨fun n => Quotient.mk (MulAction.orbitRel G X) '' spanningSets μ n, fun _ => trivial,
    fun n => ?_, ?_⟩⟩⟩
  · exact (hD.quotMeasure_image_le (measurableSet_spanningSets μ n)).2.trans_lt
      (measure_spanningSets_lt_top μ n)
  · rw [← image_iUnion, iUnion_spanningSets]
    exact image_univ_of_surjective Quotient.mk_surjective
end GlobalTheory.IsAEOrbitSection
