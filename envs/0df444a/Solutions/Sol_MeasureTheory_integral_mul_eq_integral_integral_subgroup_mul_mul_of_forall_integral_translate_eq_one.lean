-- Prove2me | solution 1 for MeasureTheory.integral_mul_eq_integral_integral_subgroup_mul_mul_of_forall_integral_translate_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/47f78f97-b0b2-504c-afa2-ed80576e8f94

import Mathlib
import Theorems.Thm_MeasureTheory_integral_mul_eq_integral_mul_of_integral_subgroup_translate_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_integral_mul_eq_integral_integral_subgroup_mul_mul_of_forall_integral_translate_eq_one

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory TopologicalSpace Filter Set
open scoped ENNReal NNReal Topology

namespace P2mUnfoldE

section Setup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  (T : Subgroup G) [MeasurableSpace T] [BorelSpace T]

theorem measurable_subgroup_mul [SecondCountableTopology G] :
    Measurable fun p : G × T => ((p.2 : G) * p.1) := by
  have hc : Continuous fun p : G × T => ((p.2 : G) * p.1) :=
    (continuous_subtype_val.comp continuous_snd).mul continuous_fst
  exact hc.measurable

theorem measurable_comp_subgroup_mul [SecondCountableTopology G] {w : G → ℝ} (hw : Measurable w) :
    Measurable fun p : G × T => w ((p.2 : G) * p.1) :=
  hw.comp (measurable_subgroup_mul T)

theorem measurable_fibre {w : G → ℝ} (hw : Measurable w) (x : G) :
    Measurable fun t : T => w ((t : G) * x) :=
  hw.comp ((continuous_subtype_val.mul continuous_const).measurable)

end Setup

section Main

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (T : Subgroup G) [MeasurableSpace T] [BorelSpace T]
  (μ : Measure G) (τ : Measure T)

theorem lintegral_fibre_eq_one {w : G → ℝ} (hw0 : ∀ x, 0 ≤ w x) (hw : Measurable w) {x : G}
    (h : ∫ t : T, w ((t : G) * x) ∂τ = 1) :
    ∫⁻ t : T, ENNReal.ofReal (w ((t : G) * x)) ∂τ = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun t => hw0 _)
    (measurable_fibre T hw x).aestronglyMeasurable] at h
  exact (ENNReal.toReal_eq_one_iff _).1 h

variable [μ.IsHaarMeasure] [τ.IsHaarMeasure] [τ.IsInvInvariant] (hT : IsClosed (T : Set G))
include hT

theorem sigmaCompactSpace_subgroup : SigmaCompactSpace T :=
  hT.isClosedEmbedding_subtypeVal.sigmaCompactSpace

theorem sFinite_tau : SFinite τ := by
  haveI := sigmaCompactSpace_subgroup T hT
  infer_instance

theorem lintegral_enorm_mul_lt_top (F : G → ℂ) (hFm : Measurable F) {C : ℝ} (hFb : ∀ x, ‖F x‖ ≤ C)
    (hFT : ∀ (t : T) (x : G), F ((t : G) * x) = F x)
    (w : G → ℝ) (hw0 : ∀ x, 0 ≤ w x) (hwm : Measurable w) (hwc : HasCompactSupport w)
    (hw1 : ∀ x, F x ≠ 0 → ∫ t : T, w ((t : G) * x) ∂τ = 1) :
    ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w x) ∂μ < ∞ := by
  haveI := sFinite_tau T τ hT

  obtain ⟨U, hUo, hCU, hUc⟩ := exists_isOpen_superset_and_isCompact_closure hwc.isCompact
  obtain ⟨V₀, hV₀, hV₀U⟩ := compact_open_separated_mul_left hwc.isCompact hUo hCU
  obtain ⟨V, hVV₀, hVo, h1V⟩ := mem_nhds_iff.1 hV₀

  set m : ℝ≥0∞ := min (τ ((Subtype.val : T → G) ⁻¹' V)) 1 with hm
  have hm_pos : m ≠ 0 := by
    have h1 : (τ ((Subtype.val : T → G) ⁻¹' V)) ≠ 0 :=
      ((hVo.preimage continuous_subtype_val).measure_pos τ ⟨⟨1, T.one_mem⟩, h1V⟩).ne'
    simp [hm, h1]
  have hm_top : m ≠ ∞ := by simp [hm]
  have hm_le_one : m ≤ 1 := min_le_right _ _

  let Φ₀ : G → ℝ≥0∞ := fun x => ∫⁻ t : T, U.indicator 1 ((t : G) * x) ∂τ
  have hΦ₀ : ∀ x ∈ tsupport w, m ≤ Φ₀ x := by
    intro x hx
    have hsub : (Subtype.val : T → G) ⁻¹' V ⊆ (fun t : T => (t : G) * x) ⁻¹' U := by
      intro t ht
      exact hV₀U (Set.mul_mem_mul (hVV₀ ht) hx)
    calc m ≤ τ ((Subtype.val : T → G) ⁻¹' V) := min_le_left _ _
      _ ≤ τ ((fun t : T => (t : G) * x) ⁻¹' U) := measure_mono hsub
      _ = Φ₀ x := by
        have hUx : MeasurableSet ((fun t : T => (t : G) * x) ⁻¹' U) :=
          measurableSet_preimage ((continuous_subtype_val.mul continuous_const).measurable)
            hUo.measurableSet
        simp only [Φ₀]
        rw [← lintegral_indicator_one hUx]
        rfl

  have hUind : Measurable (U.indicator (1 : G → ℝ≥0∞)) :=
    (measurable_one.indicator hUo.measurableSet)
  have hint2 : Measurable fun p : G × T =>
      ‖F p.1‖ₑ * ENNReal.ofReal (w p.1) * U.indicator 1 ((p.2 : G) * p.1) :=
    ((hFm.comp measurable_fst).enorm.mul
      (ENNReal.measurable_ofReal.comp (hwm.comp measurable_fst))).mul
      (hUind.comp (measurable_subgroup_mul T))

  have step1 : ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w x) ∂μ ≤
      m⁻¹ * ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w x) * Φ₀ x ∂μ := by
    rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hm_pos)]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ tsupport w
    · have h1 : (1 : ℝ≥0∞) ≤ m⁻¹ * Φ₀ x := by
        calc (1 : ℝ≥0∞) = m⁻¹ * m := (ENNReal.inv_mul_cancel hm_pos hm_top).symm
          _ ≤ m⁻¹ * Φ₀ x := mul_le_mul_right (hΦ₀ x hx) _
      calc ‖F x‖ₑ * ENNReal.ofReal (w x) = ‖F x‖ₑ * ENNReal.ofReal (w x) * 1 := (mul_one _).symm
        _ ≤ ‖F x‖ₑ * ENNReal.ofReal (w x) * (m⁻¹ * Φ₀ x) := mul_le_mul_right h1 _
        _ = m⁻¹ * (‖F x‖ₑ * ENNReal.ofReal (w x) * Φ₀ x) := by ring
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp

  have step2 : ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w x) * Φ₀ x ∂μ =
      ∫⁻ x, ‖F x‖ₑ * U.indicator 1 x * ∫⁻ t : T, ENNReal.ofReal (w ((t : G) * x)) ∂τ ∂μ := by
    calc ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w x) * Φ₀ x ∂μ
        = ∫⁻ x, ∫⁻ t : T, ‖F x‖ₑ * ENNReal.ofReal (w x) * U.indicator 1 ((t : G) * x) ∂τ ∂μ := by
          refine lintegral_congr fun x => ?_
          rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top enorm_ne_top ENNReal.ofReal_ne_top)]
      _ = ∫⁻ t : T, ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w x) * U.indicator 1 ((t : G) * x) ∂μ ∂τ :=
          lintegral_lintegral_swap hint2.aemeasurable
      _ = ∫⁻ t : T, ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w ((t : G)⁻¹ * x)) * U.indicator 1 x ∂μ ∂τ := by
          refine lintegral_congr fun t => ?_
          have := lintegral_mul_left_eq_self (μ := μ)
            (fun x => ‖F ((t : G)⁻¹ * x)‖ₑ * ENNReal.ofReal (w ((t : G)⁻¹ * x)) * U.indicator 1 x) (t : G)
          simp only [inv_mul_cancel_left] at this
          rw [this]
          refine lintegral_congr fun x => ?_
          have hF : F ((t : G)⁻¹ * x) = F x := by
            have := hFT t⁻¹ x
            simpa using this
          rw [hF]
      _ = ∫⁻ t : T, ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w ((t : G) * x)) * U.indicator 1 x ∂μ ∂τ := by
          rw [← lintegral_inv_eq_self]
          simp
      _ = ∫⁻ x, ∫⁻ t : T, ‖F x‖ₑ * ENNReal.ofReal (w ((t : G) * x)) * U.indicator 1 x ∂τ ∂μ := by
          refine (lintegral_lintegral_swap ?_).symm
          exact (((hFm.comp measurable_fst).enorm.mul
            (ENNReal.measurable_ofReal.comp (hwm.comp (measurable_subgroup_mul T)))).mul
            (hUind.comp measurable_fst)).aemeasurable
      _ = ∫⁻ x, ‖F x‖ₑ * U.indicator 1 x * ∫⁻ t : T, ENNReal.ofReal (w ((t : G) * x)) ∂τ ∂μ := by
          refine lintegral_congr fun x => ?_
          rw [← lintegral_const_mul' _ _
            (ENNReal.mul_ne_top enorm_ne_top (by by_cases hxU : x ∈ U <;> simp [hxU]))]
          refine lintegral_congr fun t => ?_
          ring

  have step3 : ∫⁻ x, ‖F x‖ₑ * U.indicator 1 x * ∫⁻ t : T, ENNReal.ofReal (w ((t : G) * x)) ∂τ ∂μ ≤
      ∫⁻ x, U.indicator (fun _ => (‖C‖₊ : ℝ≥0∞)) x ∂μ := by
    refine lintegral_mono fun x => ?_
    by_cases hF : F x = 0
    · simp [hF]
    · rw [lintegral_fibre_eq_one T τ hw0 hwm (hw1 x hF), mul_one]
      by_cases hxU : x ∈ U
      · rw [Set.indicator_of_mem hxU, Set.indicator_of_mem hxU, Pi.one_apply, mul_one]
        have h : ‖F x‖₊ ≤ ‖C‖₊ := by
          rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
          exact (hFb x).trans (Real.le_norm_self C)
        exact enorm_le_coe.2 h
      · simp [hxU]
  have step4 : ∫⁻ x, U.indicator (fun _ => (‖C‖₊ : ℝ≥0∞)) x ∂μ < ∞ := by
    rw [lintegral_indicator_const hUo.measurableSet]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top
      ((measure_mono subset_closure).trans_lt hUc.measure_lt_top)
  calc ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w x) ∂μ
      ≤ m⁻¹ * ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w x) * Φ₀ x ∂μ := step1
    _ ≤ m⁻¹ * ∫⁻ x, U.indicator (fun _ => (‖C‖₊ : ℝ≥0∞)) x ∂μ := by
        rw [step2]; exact mul_le_mul_right step3 _
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hm_pos)) step4

omit [μ.IsHaarMeasure] [τ.IsHaarMeasure] [τ.IsInvInvariant] hT in

theorem enorm_integrand (F : G → ℂ) (w₁ w₂ : G → ℝ) (hw₁ : ∀ x, 0 ≤ w₁ x) (hw₂ : ∀ x, 0 ≤ w₂ x)
    (x y : G) :
    ‖F x * (w₁ x : ℂ) * (w₂ y : ℂ)‖ₑ = ‖F x‖ₑ * ENNReal.ofReal (w₁ x) * ENNReal.ofReal (w₂ y) := by
  have h1 : ‖(w₁ x : ℂ)‖ₑ = ENNReal.ofReal (w₁ x) := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (hw₁ x)]
  have h2 : ‖(w₂ y : ℂ)‖ₑ = ENNReal.ofReal (w₂ y) := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (hw₂ y)]
  rw [enorm_mul, enorm_mul, h1, h2]

omit [μ.IsHaarMeasure] [τ.IsHaarMeasure] [τ.IsInvInvariant] hT in
theorem measurable_integrand (F : G → ℂ) (hFm : Measurable F) (w₁ w₂ : G → ℝ)
    (hw₁ : Measurable w₁) (hw₂ : Measurable w₂) :
    Measurable (Function.uncurry fun (x : G) (t : T) =>
      F x * (w₁ x : ℂ) * (w₂ ((t : G) * x) : ℂ)) :=
  ((hFm.comp measurable_fst).mul
    (Complex.measurable_ofReal.comp (hw₁.comp measurable_fst))).mul
    (Complex.measurable_ofReal.comp (measurable_comp_subgroup_mul T hw₂))

theorem integrable_integrand (F : G → ℂ) (hFm : Measurable F)
    (w₁ w₂ : G → ℝ) (hw₁0 : ∀ x, 0 ≤ w₁ x) (hw₁m : Measurable w₁)
    (hfin : ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w₁ x) ∂μ < ∞)
    (hw₂0 : ∀ x, 0 ≤ w₂ x) (hw₂m : Measurable w₂)
    (hw₂1 : ∀ x, F x ≠ 0 → ∫ t : T, w₂ ((t : G) * x) ∂τ = 1) :
    Integrable (Function.uncurry fun (x : G) (t : T) =>
      F x * (w₁ x : ℂ) * (w₂ ((t : G) * x) : ℂ)) (μ.prod τ) := by
  haveI := sFinite_tau T τ hT
  have hmeas := measurable_integrand T F hFm w₁ w₂ hw₁m hw₂m
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hmeas.enorm.aemeasurable]
  calc ∫⁻ x, ∫⁻ t : T, ‖Function.uncurry (fun (x : G) (t : T) =>
          F x * (w₁ x : ℂ) * (w₂ ((t : G) * x) : ℂ)) (x, t)‖ₑ ∂τ ∂μ
      = ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w₁ x) *
          ∫⁻ t : T, ENNReal.ofReal (w₂ ((t : G) * x)) ∂τ ∂μ := by
        refine lintegral_congr fun x => ?_
        rw [← lintegral_const_mul' _ _ (ENNReal.mul_ne_top enorm_ne_top ENNReal.ofReal_ne_top)]
        refine lintegral_congr fun t => ?_
        exact enorm_integrand F w₁ w₂ hw₁0 hw₂0 x _
    _ = ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w₁ x) ∂μ := by
        refine lintegral_congr fun x => ?_
        by_cases hF : F x = 0
        · simp [hF]
        · rw [lintegral_fibre_eq_one T τ hw₂0 hw₂m (hw₂1 x hF), mul_one]
    _ < ∞ := hfin

theorem integral_eq_integral_integral (F : G → ℂ) (hFm : Measurable F)
    (w₁ w₂ : G → ℝ) (hw₁0 : ∀ x, 0 ≤ w₁ x) (hw₁m : Measurable w₁)
    (hfin : ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w₁ x) ∂μ < ∞)
    (hw₂0 : ∀ x, 0 ≤ w₂ x) (hw₂m : Measurable w₂)
    (hw₂1 : ∀ x, F x ≠ 0 → ∫ t : T, w₂ ((t : G) * x) ∂τ = 1) :
    ∫ x, F x * (w₁ x : ℂ) ∂μ =
      ∫ t : T, ∫ x, F x * (w₁ x : ℂ) * (w₂ ((t : G) * x) : ℂ) ∂μ ∂τ := by
  haveI := sFinite_tau T τ hT
  calc ∫ x, F x * (w₁ x : ℂ) ∂μ
      = ∫ x, F x * (w₁ x : ℂ) * ((∫ t : T, w₂ ((t : G) * x) ∂τ : ℝ) : ℂ) ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        by_cases hF : F x = 0
        · simp [hF]
        · simp [hw₂1 x hF]
    _ = ∫ x, ∫ t : T, F x * (w₁ x : ℂ) * (w₂ ((t : G) * x) : ℂ) ∂τ ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only
        rw [integral_const_mul, integral_complex_ofReal]
    _ = ∫ t : T, ∫ x, F x * (w₁ x : ℂ) * (w₂ ((t : G) * x) : ℂ) ∂μ ∂τ :=
        integral_integral_swap
          (integrable_integrand T μ τ hT F hFm w₁ w₂ hw₁0 hw₁m hfin hw₂0 hw₂m hw₂1)

end Main

end P2mUnfoldE

namespace P2mUnfoldE

section Unfold

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (T : Subgroup G) [MeasurableSpace T] [BorelSpace T]
  (μ : Measure G) (τ : Measure T)
  [μ.IsHaarMeasure] [τ.IsHaarMeasure] [τ.IsInvInvariant] (hT : IsClosed (T : Set G))
include hT

theorem integrable_integrand₂ (F : G → ℂ) (hFm : Measurable F)
    (w₁ w₂ : G → ℝ) (hw₁0 : ∀ x, 0 ≤ w₁ x) (hw₁m : Measurable w₁)
    (hfin : ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w₁ x) ∂μ < ∞)
    (hw₂0 : ∀ x, 0 ≤ w₂ x) (hw₂m : Measurable w₂)
    (hw₂1 : ∀ x, F x ≠ 0 → ∫ t : T, w₂ ((t : G) * x) ∂τ = 1) :
    Integrable (Function.uncurry fun (t : T) (x : G) =>
      F ((t : G) * x) * (w₁ ((t : G) * x) : ℂ) * (w₂ x : ℂ)) (τ.prod μ) := by
  haveI := sFinite_tau T τ hT
  have hmul : Measurable fun p : T × G => ((p.1 : G) * p.2) :=
    ((continuous_subtype_val.comp continuous_fst).mul continuous_snd).measurable
  have hmeas : Measurable (Function.uncurry fun (t : T) (x : G) =>
      F ((t : G) * x) * (w₁ ((t : G) * x) : ℂ) * (w₂ x : ℂ)) :=
    ((hFm.comp hmul).mul (Complex.measurable_ofReal.comp (hw₁m.comp hmul))).mul
      (Complex.measurable_ofReal.comp (hw₂m.comp measurable_snd))
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hmeas.enorm.aemeasurable]
  have hsw : Measurable fun p : G × T => ‖F p.1‖ₑ * ENNReal.ofReal (w₁ p.1) * ENNReal.ofReal (w₂ ((p.2 : G) * p.1)) :=
    (((hFm.comp measurable_fst).enorm.mul (ENNReal.measurable_ofReal.comp (hw₁m.comp measurable_fst))).mul
      (ENNReal.measurable_ofReal.comp (measurable_comp_subgroup_mul T hw₂m)))
  calc ∫⁻ t : T, ∫⁻ x, ‖Function.uncurry (fun (t : T) (x : G) =>
          F ((t : G) * x) * (w₁ ((t : G) * x) : ℂ) * (w₂ x : ℂ)) (t, x)‖ₑ ∂μ ∂τ
      = ∫⁻ t : T, ∫⁻ x, ‖F ((t : G) * x)‖ₑ * ENNReal.ofReal (w₁ ((t : G) * x)) * ENNReal.ofReal (w₂ x) ∂μ ∂τ := by
        refine lintegral_congr fun t => lintegral_congr fun x => ?_
        exact enorm_integrand F w₁ w₂ hw₁0 hw₂0 _ _
    _ = ∫⁻ t : T, ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w₁ x) * ENNReal.ofReal (w₂ ((t : G)⁻¹ * x)) ∂μ ∂τ := by
        refine lintegral_congr fun t => ?_
        have := lintegral_mul_left_eq_self (μ := μ)
          (fun x => ‖F x‖ₑ * ENNReal.ofReal (w₁ x) * ENNReal.ofReal (w₂ ((t : G)⁻¹ * x))) (t : G)
        simp only [inv_mul_cancel_left] at this
        rw [← this]
    _ = ∫⁻ t : T, ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w₁ x) * ENNReal.ofReal (w₂ ((t : G) * x)) ∂μ ∂τ := by
        rw [← lintegral_inv_eq_self]
        simp
    _ = ∫⁻ x, ∫⁻ t : T, ‖F x‖ₑ * ENNReal.ofReal (w₁ x) * ENNReal.ofReal (w₂ ((t : G) * x)) ∂τ ∂μ :=
        (lintegral_lintegral_swap hsw.aemeasurable).symm
    _ = ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w₁ x) * ∫⁻ t : T, ENNReal.ofReal (w₂ ((t : G) * x)) ∂τ ∂μ := by
        refine lintegral_congr fun x => ?_
        rw [← lintegral_const_mul' _ _ (ENNReal.mul_ne_top enorm_ne_top ENNReal.ofReal_ne_top)]
    _ = ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w₁ x) ∂μ := by
        refine lintegral_congr fun x => ?_
        by_cases hF : F x = 0
        · simp [hF]
        · rw [lintegral_fibre_eq_one T τ hw₂0 hw₂m (hw₂1 x hF), mul_one]
    _ < ∞ := hfin

theorem unfold_steps (F : G → ℂ) (hFm : Measurable F)
    (wS W : G → ℝ) (hwS0 : ∀ x, 0 ≤ wS x) (hwSm : Measurable wS)
    (hfin : ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (wS x) ∂μ < ∞)
    (hW0 : ∀ x, 0 ≤ W x) (hWm : Measurable W)
    (hW1 : ∀ x, F x ≠ 0 → ∫ t : T, W ((t : G) * x) ∂τ = 1) :
    ∫ x, F x * (wS x : ℂ) ∂μ = ∫ x, (∫ t : T, F ((t : G) * x) * (wS ((t : G) * x) : ℂ) ∂τ) * (W x : ℂ) ∂μ := by
  haveI := sFinite_tau T τ hT
  rw [integral_eq_integral_integral T μ τ hT F hFm wS W hwS0 hwSm hfin hW0 hWm hW1]
  calc ∫ t : T, ∫ x, F x * (wS x : ℂ) * (W ((t : G) * x) : ℂ) ∂μ ∂τ
      = ∫ t : T, ∫ x, F ((t : G)⁻¹ * x) * (wS ((t : G)⁻¹ * x) : ℂ) * (W x : ℂ) ∂μ ∂τ := by
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        have h := integral_mul_left_eq_self (μ := μ)
          (fun x => F ((t : G)⁻¹ * x) * (wS ((t : G)⁻¹ * x) : ℂ) * (W x : ℂ)) (t : G)
        simp only [inv_mul_cancel_left] at h
        exact h
    _ = ∫ t : T, ∫ x, F ((t : G) * x) * (wS ((t : G) * x) : ℂ) * (W x : ℂ) ∂μ ∂τ := by
        have h := integral_inv_eq_self
          (fun t : T => ∫ x, F ((t : G) * x) * (wS ((t : G) * x) : ℂ) * (W x : ℂ) ∂μ) τ
        simp only [Subgroup.coe_inv] at h
        exact h
    _ = ∫ x, ∫ t : T, F ((t : G) * x) * (wS ((t : G) * x) : ℂ) * (W x : ℂ) ∂τ ∂μ :=
        integral_integral_swap (integrable_integrand₂ T μ τ hT F hFm wS W hwS0 hwSm hfin hW0 hWm hW1)
    _ = ∫ x, (∫ t : T, F ((t : G) * x) * (wS ((t : G) * x) : ℂ) ∂τ) * (W x : ℂ) ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        exact integral_mul_const _ _

end Unfold

end P2mUnfoldE

namespace P2mUnfoldE

section Fibre

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem fibre_eq
    (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (S : Subgroup G) (hS : IsClosed (S : Set G)) (hST : S ≤ T) [MeasurableSpace S] [BorelSpace S]
    (τ : Measure T) [τ.IsHaarMeasure] [τ.IsInvInvariant]
    (τS : Measure S) [τS.IsHaarMeasure] [τS.IsInvInvariant]
    (F : G → ℂ) (hFm : Measurable F) (hFb : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C)
    (hFS : ∀ (s : S) (x : G), F ((s : G) * x) = F x)
    (wS : G → ℝ) (hwS0 : ∀ x, 0 ≤ wS x) (hwSm : Measurable wS) (hwSc : HasCompactSupport wS)
    (hwS1 : ∀ x : G, F x ≠ 0 → ∫ s : S, wS ((s : G) * x) ∂τS = 1)
    (β : T → ℝ) (hβ0 : ∀ t, 0 ≤ β t) (hβm : Measurable β) (hβc : HasCompactSupport β)
    (hβ1 : ∀ t : T, ∫ s : S, β (⟨(s : G), hST s.2⟩ * t) ∂τS = 1) (x : G) :
    ∫ t : T, F ((t : G) * x) * (wS ((t : G) * x) : ℂ) ∂τ = ∫ t : T, F ((t : G) * x) * (β t : ℂ) ∂τ := by
  haveI : LocallyCompactSpace T := hT.locallyCompactSpace
  haveI : SecondCountableTopology T := TopologicalSpace.Subtype.secondCountableTopology _

  set S' : Subgroup T := S.subgroupOf T with hS'def
  have hS' : IsClosed (S' : Set T) := by
    have : (S' : Set T) = ((↑) : T → G) ⁻¹' (S : Set G) := by
      ext t; simp [hS'def, Subgroup.mem_subgroupOf]
    rw [this]; exact hS.preimage continuous_subtype_val
  set e : S ≃* S' := (Subgroup.subgroupOfEquivOfLe hST).symm with he
  have hec : Continuous e := by
    refine Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _
  have hesc : Continuous e.symm := by
    refine Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  set τ' : Measure S' := Measure.map e τS with hτ'
  haveI : τ'.IsHaarMeasure := MulEquiv.isHaarMeasure_map τS e hec hesc
  haveI : τ'.IsInvInvariant := by
    refine ⟨?_⟩
    show Measure.map Inv.inv (Measure.map e τS) = Measure.map e τS
    rw [Measure.map_map measurable_inv hec.measurable]
    have : (Inv.inv ∘ (e : S → S')) = (e : S → S') ∘ Inv.inv := by
      funext s; simp
    rw [this, ← Measure.map_map hec.measurable measurable_inv]
    congr 1
    exact Measure.IsInvInvariant.inv_eq_self

  obtain ⟨C, hC⟩ := hFb
  have hF'm : Measurable fun t : T => F ((t : G) * x) := hFm.comp (continuous_subtype_val.mul continuous_const).measurable
  have hF'T : ∀ (s' : S') (t : T), F ((((s' : T) * t : T) : G) * x) = F ((t : G) * x) := by
    intro s' t
    rw [Subgroup.coe_mul, mul_assoc]
    exact hFS ⟨((s' : T) : G), (Subgroup.mem_subgroupOf).mp s'.2⟩ _
  have hemb : Topology.IsClosedEmbedding (fun t : T => (t : G) * x) :=
    (Homeomorph.mulRight x).isClosedEmbedding.comp hT.isClosedEmbedding_subtypeVal
  have hw₁c : HasCompactSupport fun t : T => wS ((t : G) * x) := by
    refine HasCompactSupport.intro' (hemb.isCompact_preimage hwSc) ((isClosed_tsupport wS).preimage hemb.continuous) ?_
    intro t ht
    exact image_eq_zero_of_notMem_tsupport ht
  have hint : ∀ (f : S' → ℝ), Measurable f → ∫ s', f s' ∂τ' = ∫ s, f (e s) ∂τS := by
    intro f hf
    exact integral_map hec.measurable.aemeasurable hf.aestronglyMeasurable
  have hw₁1 : ∀ t : T, F ((t : G) * x) ≠ 0 → ∫ s' : S', wS ((((s' : T) * t : T) : G) * x) ∂τ' = 1 := by
    intro t ht
    have hm : Measurable fun s' : S' => wS ((((s' : T) * t : T) : G) * x) :=
      hwSm.comp ((continuous_subtype_val.comp ((continuous_subtype_val).mul continuous_const)).mul
        continuous_const).measurable
    rw [hint _ hm]
    have : ∀ s : S, wS (((((e s : S') : T) * t : T) : G) * x) = wS ((s : G) * ((t : G) * x)) := by
      intro s; rw [Subgroup.coe_mul, mul_assoc]; rfl
    simp_rw [this]
    exact hwS1 _ ht
  have hw₂1 : ∀ t : T, F ((t : G) * x) ≠ 0 → ∫ s' : S', β ((s' : T) * t) ∂τ' = 1 := by
    intro t _
    have hm : Measurable fun s' : S' => β ((s' : T) * t) :=
      hβm.comp ((continuous_subtype_val).mul continuous_const).measurable
    rw [hint _ hm]
    exact hβ1 t
  exact MeasureTheory.integral_mul_eq_integral_mul_of_integral_subgroup_translate_eq_one (G := T) S' hS' τ τ'
    (fun t : T => F ((t : G) * x)) hF'm ⟨C, fun t => hC _⟩ hF'T
    (fun t : T => wS ((t : G) * x)) β
    ⟨fun t => hwS0 _, hwSm.comp (continuous_subtype_val.mul continuous_const).measurable, hw₁c, hw₁1⟩
    ⟨hβ0, hβm, hβc, hw₂1⟩

end Fibre

end P2mUnfoldE

namespace P2mUnfoldE
theorem main
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (S : Subgroup G) (hS : IsClosed (S : Set G)) (hST : S ≤ T) [MeasurableSpace S] [BorelSpace S]
    (μ : Measure G) [μ.IsHaarMeasure]
    (τ : Measure T) [τ.IsHaarMeasure] [τ.IsInvInvariant]
    (τS : Measure S) [τS.IsHaarMeasure] [τS.IsInvInvariant]
    (F : G → ℂ) (hFm : Measurable F) (hFb : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C)
    (hFS : ∀ (s : S) (x : G), F ((s : G) * x) = F x)
    (wS : G → ℝ) (hwS0 : ∀ x, 0 ≤ wS x) (hwSm : Measurable wS) (hwSc : HasCompactSupport wS)
    (hwS1 : ∀ x : G, F x ≠ 0 → ∫ s : S, wS ((s : G) * x) ∂τS = 1)
    (β : T → ℝ) (hβ0 : ∀ t, 0 ≤ β t) (hβm : Measurable β) (hβc : HasCompactSupport β)
    (hβ1 : ∀ t : T, ∫ s : S, β (⟨(s : G), hST s.2⟩ * t) ∂τS = 1)
    (W : G → ℝ) (hW0 : ∀ x, 0 ≤ W x) (hWm : Measurable W) (hWc : HasCompactSupport W)
    (hW1 : ∀ x : G, F x ≠ 0 → ∫ t : T, W ((t : G) * x) ∂τ = 1) :
    ∫ x, F x * (wS x : ℂ) ∂μ = ∫ x, (∫ t : T, F ((t : G) * x) * (β t : ℂ) ∂τ) * (W x : ℂ) ∂μ := by
  obtain ⟨C, hC⟩ := hFb
  have hfin := lintegral_enorm_mul_lt_top S μ τS hS F hFm hC hFS wS hwS0 hwSm hwSc hwS1
  rw [unfold_steps T μ τ hT F hFm wS W hwS0 hwSm hfin hW0 hWm hW1]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show (∫ t : T, F ((t : G) * x) * (wS ((t : G) * x) : ℂ) ∂τ) * (W x : ℂ) = (∫ t : T, F ((t : G) * x) * (β t : ℂ) ∂τ) * (W x : ℂ)
  rw [fibre_eq T hT S hS hST τ τS F hFm ⟨C, hC⟩ hFS wS hwS0 hwSm hwSc hwS1 β hβ0 hβm hβc hβ1 x]

end P2mUnfoldE

theorem solution
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (S : Subgroup G) (hS : IsClosed (S : Set G)) (hST : S ≤ T) [MeasurableSpace S] [BorelSpace S]
    (μ : Measure G) [μ.IsHaarMeasure]
    (τ : Measure T) [τ.IsHaarMeasure] [τ.IsInvInvariant]
    (τS : Measure S) [τS.IsHaarMeasure] [τS.IsInvInvariant]
    (F : G → ℂ) (hFm : Measurable F) (hFb : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C)
    (hFS : ∀ (s : S) (x : G), F ((s : G) * x) = F x)
    (wS : G → ℝ) (hwS0 : ∀ x, 0 ≤ wS x) (hwSm : Measurable wS) (hwSc : HasCompactSupport wS)
    (hwS1 : ∀ x : G, F x ≠ 0 → ∫ s : S, wS ((s : G) * x) ∂τS = 1)
    (β : T → ℝ) (hβ0 : ∀ t, 0 ≤ β t) (hβm : Measurable β) (hβc : HasCompactSupport β)
    (hβ1 : ∀ t : T, ∫ s : S, β (⟨(s : G), hST s.2⟩ * t) ∂τS = 1)
    (W : G → ℝ) (hW0 : ∀ x, 0 ≤ W x) (hWm : Measurable W) (hWc : HasCompactSupport W)
    (hW1 : ∀ x : G, F x ≠ 0 → ∫ t : T, W ((t : G) * x) ∂τ = 1) :
    ∫ x, F x * (wS x : ℂ) ∂μ = ∫ x, (∫ t : T, F ((t : G) * x) * (β t : ℂ) ∂τ) * (W x : ℂ) ∂μ :=
  P2mUnfoldE.main T hT S hS hST μ τ τS F hFm hFb hFS wS hwS0 hwSm hwSc hwS1 β hβ0 hβm hβc hβ1 W hW0 hWm hWc hW1

end S_MeasureTheory_integral_mul_eq_integral_integral_subgroup_mul_mul_of_forall_integral_translate_eq_one
end P2MW
export P2MW.S_MeasureTheory_integral_mul_eq_integral_integral_subgroup_mul_mul_of_forall_integral_translate_eq_one (solution)
