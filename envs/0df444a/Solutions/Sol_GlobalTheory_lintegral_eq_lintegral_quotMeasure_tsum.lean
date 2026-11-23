-- Prove2me | solution 1 for GlobalTheory.lintegral_eq_lintegral_quotMeasure_tsum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:11.977394+00:00
-- url     : https://prove2.me/submissions/5a9282e8-cf01-4bc3-a871-034a8becc344

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsFundamentalDomainAndQuotMeasureEq
import Theorems.Thm_GlobalTheory_isAEOrbitSection_of_isFundamentalDomain_of_surjective
import Theorems.Thm_GlobalTheory_isFundamentalDomain_of_orbitSection
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_isFundamentalDomain
import Theorems.Thm_GlobalTheory_measure_fixed_eq_zero_of_isFundamentalDomain
import Theorems.Thm_GlobalTheory_quotMeasure_univ_le
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_map_restrict_eq
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_measurePreserving_mk
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_quotMeasure_apply
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_quotMeasure_univ
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_measure_eq
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_lintegral_quotMeasure
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_integral_quotMeasure
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_integrable_quotMeasure_iff
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_quotMeasure_apply_eq_zero_iff
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_quotMeasure_eq_zero_iff
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_quotMeasure_image_le
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_sigmaFinite_quotMeasure
import Theorems.Thm_GlobalTheory_quotMeasure_univ_eq_covolume

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
namespace GlobalTheory
theorem _root_.solution [h : HasFundamentalDomain G X μ] {f : X → ℝ≥0∞}
    (hf : Measurable f) {F : Quotient (MulAction.orbitRel G X) → ℝ≥0∞}
    (hF : ∀ x, F (Quotient.mk _ x) = ∑' g : G, f (g • x)) :
    ∫⁻ x, f x ∂μ = ∫⁻ q, F q ∂quotMeasure G μ := by
  obtain ⟨D, hD⟩ := h.ExistsIsFundamentalDomain
  have hm : ∀ g : G, Measurable fun x => f (g • x) := fun g => hf.comp (measurable_const_smul g)
  have hFm : Measurable F := by
    refine measurable_from_quotient.2 ?_
    have : F ∘ Quotient.mk'' = fun x => ∑' g : G, f (g • x) := funext hF
    rw [this]
    exact Measurable.tsum hm
  rw [(isAEOrbitSection_of_isFundamentalDomain hD).lintegral_quotMeasure hFm.aemeasurable,
    hD.lintegral_eq_tsum'' f, ← lintegral_tsum fun g => (hm g).aemeasurable]
  simp only [hF]
end GlobalTheory
