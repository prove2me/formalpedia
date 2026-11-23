-- Prove2me | solution 1 for GlobalTheory.IsAEOrbitSection.quotMeasure_apply_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:18.4128+00:00
-- url     : https://prove2.me/submissions/2d7da423-e3c4-4c23-ad96-4af404a23bf1

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
theorem _root_.solution (hD : IsAEOrbitSection G D μ)
    {U : Set (Quotient (MulAction.orbitRel G X))} (hU : MeasurableSet U) :
    quotMeasure G μ U = 0 ↔ μ (Quotient.mk (MulAction.orbitRel G X) ⁻¹' U) = 0 := by
  rw [hD.quotMeasure_apply hU]
  refine ⟨fun h => ?_, fun h => measure_mono_null inter_subset_left h⟩
  have h1 : ∀ᵐ x ∂μ, ∀ g : G, g • x ∉ Quotient.mk (MulAction.orbitRel G X) ⁻¹' U ∩ D :=
    ae_all_iff.2 fun g => (measurePreserving_smul g μ).quasiMeasurePreserving.ae
      (p := fun x => x ∉ Quotient.mk (MulAction.orbitRel G X) ⁻¹' U ∩ D)
      (measure_eq_zero_iff_ae_notMem.1 h)
  refine measure_mono_null (fun x hx => ?_) (h1.and hD.ae_covers)
  rintro ⟨h2, g, hg⟩
  refine h2 g ⟨?_, hg⟩
  have : Quotient.mk (MulAction.orbitRel G X) (g • x) = Quotient.mk (MulAction.orbitRel G X) x :=
    Quotient.sound ⟨g, rfl⟩
  rw [mem_preimage, this]
  exact hx
end GlobalTheory.IsAEOrbitSection
