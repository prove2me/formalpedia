-- Prove2me | solution 1 for GlobalTheory.SmGL.UnitInd.lintegral_average
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:50:27.456662+00:00
-- url     : https://prove2.me/submissions/9c0836f2-d64e-484d-b70d-4c3c36f8bfde

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_inv
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Matrix
open scoped TensorProduct ENNReal
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.UnitInd
variable {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] [MeasurableSpace X]
namespace GlobalTheory.SmGL.UnitInd
theorem _root_.solution (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] (ρ : Measure X) [SFinite ρ]
    {K L : Set G} (hK : MeasurableSet K) (hL : MeasurableSet L) {j : X → G} (hj : Measurable j)
    {δ : X → ℝ≥0∞} (hδ : Measurable δ) {φ : G → ℝ≥0∞} (hφ : Measurable φ)
    (hlaw : ∀ y x, φ ((j y)⁻¹ * x) = δ y * φ x) {c : ℝ≥0∞}
    (ha : ∀ x, ∫⁻ y, L.indicator 1 (j y * x) ∂ρ = c)
    (hb : ∀ x, ∫⁻ y, K.indicator 1 ((j y)⁻¹ * x) * δ y ∂ρ = c) :
    c * ∫⁻ x in K, φ x ∂μ = c * ∫⁻ x in L, φ x ∂μ := by
  have mK : Measurable (K.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hK
  have mL : Measurable (L.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hL
  have e : ∀ {S : Set G}, MeasurableSet S →
      c * ∫⁻ x in S, φ x ∂μ = ∫⁻ x, (S.indicator 1 x * φ x) * c ∂μ := fun {S} hS => by
    rw [lintegral_mul_const (f := fun x => S.indicator 1 x * φ x) _ ((measurable_one.indicator hS).mul hφ), mul_comm,
      ← lintegral_indicator hS]
    congr 2
    funext x
    by_cases h : x ∈ S <;> simp [h]
  rw [e hK, e hL]
  calc ∫⁻ x, (K.indicator 1 x * φ x) * c ∂μ
      = ∫⁻ x, ∫⁻ y, (K.indicator 1 x * φ x) * L.indicator 1 (j y * x) ∂ρ ∂μ := by
        refine lintegral_congr fun x => ?_
        rw [lintegral_const_mul (f := fun y => L.indicator 1 (j y * x)) _ (mL.comp (hj.mul_const x)), ha]
    _ = ∫⁻ y, ∫⁻ x, (K.indicator 1 x * φ x) * L.indicator 1 (j y * x) ∂μ ∂ρ :=
        lintegral_lintegral_swap (((mK.mul hφ).comp measurable_fst).mul
          (mL.comp ((hj.comp measurable_snd).mul measurable_fst))).aemeasurable
    _ = ∫⁻ y, ∫⁻ x, (L.indicator 1 x * φ x) * (K.indicator 1 ((j y)⁻¹ * x) * δ y) ∂μ ∂ρ := by
        refine lintegral_congr fun y => ?_
        rw [← lintegral_mul_left_eq_self _ (j y)⁻¹]
        refine lintegral_congr fun x => ?_
        rw [hlaw, mul_inv_cancel_left]
        ring
    _ = ∫⁻ x, ∫⁻ y, (L.indicator 1 x * φ x) * (K.indicator 1 ((j y)⁻¹ * x) * δ y) ∂ρ ∂μ :=
        (lintegral_lintegral_swap (((mL.mul hφ).comp measurable_fst).mul
          ((mK.comp ((hj.comp measurable_snd).inv.mul measurable_fst)).mul
            (hδ.comp measurable_snd))).aemeasurable).symm
    _ = _ := by
        refine lintegral_congr fun x => ?_
        rw [lintegral_const_mul (f := fun y => K.indicator 1 ((j y)⁻¹ * x) * δ y) _
          ((mK.comp (hj.inv.mul_const x)).mul hδ), hb]
end GlobalTheory.SmGL.UnitInd
