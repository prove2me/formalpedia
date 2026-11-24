-- Prove2me | solution 1 for GlobalTheory.WeilM.IsUnitaryOn.norm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:04.012049+00:00
-- url     : https://prove2.me/submissions/30205ae3-59e1-4d48-bd88-36139c9d6ec9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Theorems.Thm_GlobalTheory_WeilM_norm_eq_one_of_lintegral_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped NNReal Classical
open GlobalTheory GlobalTheory.WeilM
variable {R : Type} [CommRing R] {κ : Type} [Fintype κ] {G : Type} [Group G]
namespace GlobalTheory.WeilM
namespace IsUnitaryOn
theorem _root_.solution [TopologicalSpace R] {C : TestClass R} {om om' : G →* Module.End ℂ ((κ → R) → ℂ)}
    (h : IsUnitaryOn C om) (h' : IsUnitaryOn C om') {μ : @Measure (κ → R) (borel _)}
    (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) {φ : (κ → R) → ℂ} (hφ : φ ∈ C.sp κ)
    (h0 : ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ ≠ 0) (h1 : ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ ≠ ⊤) {g : G} {a : ℂ} (ha : om' g φ = a • om g φ) :
    ‖a‖ = 1 := by
  have e := h μ hμ g φ hφ
  refine @norm_eq_one_of_lintegral_eq _ (borel _) μ (om g φ) a ?_ (e ▸ h0) (e ▸ h1)
  rw [← ha, e, h' μ hμ g φ hφ]
end IsUnitaryOn
end GlobalTheory.WeilM
