-- Prove2me | solution 1 for LanglandsTunnell.integrable_dualFibres_of_integrable_oneSided
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/00286922-8604-5983-aed4-36c81255a71b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_integrable_dualFibres_of_integrable_oneSided

set_option autoImplicit false

open MeasureTheory Set

noncomputable section

namespace K9F2

theorem integrable_prod_iff_of_fiber {Z E : Type*} [MeasurableSpace Z] {ν : Measure Z} [SFinite ν]
    [NormedAddCommGroup E] (ρ₁ ρ₂ : Measure ℝ) [SFinite ρ₁] [SFinite ρ₂] (F G : Z × ℝ → E)
    (hF : AEStronglyMeasurable F (ν.prod ρ₁)) (hG : AEStronglyMeasurable G (ν.prod ρ₂))
    (hiff : ∀ᵐ z ∂ν, (Integrable (fun x => F (z, x)) ρ₁ ↔ Integrable (fun y => G (z, y)) ρ₂))
    (hint : ∀ᵐ z ∂ν, (∫ x, ‖F (z, x)‖ ∂ρ₁) = ∫ y, ‖G (z, y)‖ ∂ρ₂) :
    Integrable F (ν.prod ρ₁) ↔ Integrable G (ν.prod ρ₂) := by
  rw [integrable_prod_iff hF, integrable_prod_iff hG]
  exact and_congr (Filter.eventually_congr hiff) (integrable_congr hint)

section OneDim
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem subst_negInv (c : ℝ) (hc : 0 < c) (g : ℝ → E) :
    (IntegrableOn g (Iio 0) ↔ IntegrableOn (fun y : ℝ => (c * y ^ 2)⁻¹ • g (-(c * y)⁻¹)) (Ioi 0)) ∧
    ((∫ x in Iio 0, g x) = ∫ y in Ioi 0, (c * y ^ 2)⁻¹ • g (-(c * y)⁻¹)) := by
  have hderiv : ∀ y ∈ Ioi (0:ℝ), HasDerivWithinAt (fun y : ℝ => -(c * y)⁻¹) ((c * y ^ 2)⁻¹) (Ioi 0) y := by
    intro y hy
    have hy0 : y ≠ 0 := ne_of_gt hy
    have hy' : c * y ≠ 0 := mul_ne_zero hc.ne' hy0
    have h1 : HasDerivAt (fun y : ℝ => c * y) c y := by simpa using (hasDerivAt_id y).const_mul c
    have h3 := (h1.inv hy').neg
    have e : -(-c / (c * y) ^ 2) = (c * y ^ 2)⁻¹ := by field_simp
    rw [e] at h3
    exact h3.hasDerivWithinAt
  have hinj : InjOn (fun y : ℝ => -(c * y)⁻¹) (Ioi 0) := by
    intro y₁ h₁ y₂ h₂ h
    have : (c * y₁)⁻¹ = (c * y₂)⁻¹ := neg_inj.1 h
    have := inv_inj.1 this
    exact mul_left_cancel₀ hc.ne' this
  have himg : (fun y : ℝ => -(c * y)⁻¹) '' Ioi 0 = Iio 0 := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact neg_neg_of_pos (inv_pos.2 (mul_pos hc hy))
    · intro hx
      refine ⟨-(c * x)⁻¹, ?_, ?_⟩
      · have : c * x < 0 := mul_neg_of_pos_of_neg hc hx
        exact neg_pos.2 (inv_neg''.2 this)
      · have hx0 : x ≠ 0 := ne_of_lt hx
        field_simp
  have habs : ∀ y ∈ Ioi (0:ℝ), |(c * y ^ 2)⁻¹| = (c * y ^ 2)⁻¹ := fun y hy => abs_of_pos (by
    have : (0:ℝ) < y := hy; positivity)
  constructor
  · have h := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hinj g
    rw [himg] at h
    rw [h]
    exact integrableOn_congr_fun (fun y hy => by rw [habs y hy]) measurableSet_Ioi
  · have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj g
    rw [himg] at h
    rw [h]
    exact setIntegral_congr_fun measurableSet_Ioi (fun y hy => by rw [habs y hy])

end OneDim

theorem integrable_iff_pullback_negInv {Z : Type*} [MeasurableSpace Z] (ν : Measure Z) [SFinite ν]
    (c : Z → ℝ) (hcm : Measurable c) (hc : ∀ᵐ z ∂ν, 0 < c z)
    (F : Z × ℝ → ℂ) (hF : Measurable F) :
    Integrable F (ν.prod (volume.restrict (Iio 0))) ↔
      Integrable (fun p : Z × ℝ => (c p.1 * p.2 ^ 2)⁻¹ • F (p.1, -(c p.1 * p.2)⁻¹))
        (ν.prod (volume.restrict (Ioi 0))) := by
  have hGm : Measurable (fun p : Z × ℝ => (c p.1 * p.2 ^ 2)⁻¹ • F (p.1, -(c p.1 * p.2)⁻¹)) := by
    refine Measurable.smul (((hcm.comp measurable_fst).mul (measurable_snd.pow_const 2)).inv) ?_
    exact hF.comp (measurable_fst.prodMk ((hcm.comp measurable_fst).mul measurable_snd).inv.neg)
  refine integrable_prod_iff_of_fiber _ _ _ _ hF.aestronglyMeasurable hGm.aestronglyMeasurable ?_ ?_
  · filter_upwards [hc] with z hz
    exact (subst_negInv (c z) hz (fun x => F (z, x))).1
  · filter_upwards [hc] with z hz
    have h := (subst_negInv (c z) hz (fun x => ‖F (z, x)‖)).2
    rw [h]
    refine setIntegral_congr_fun measurableSet_Ioi (fun y (hy : (0:ℝ) < y) => ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), smul_eq_mul]

end K9F2

end

noncomputable section

namespace K9F2

section OneDim'
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem subst_negInv' (c : ℝ) (hc : 0 < c) (g : ℝ → E) :
    (IntegrableOn g (Ioi 0) ↔ IntegrableOn (fun y : ℝ => (c * y ^ 2)⁻¹ • g (-(c * y)⁻¹)) (Iio 0)) ∧
    ((∫ x in Ioi 0, g x) = ∫ y in Iio 0, (c * y ^ 2)⁻¹ • g (-(c * y)⁻¹)) := by
  have hderiv : ∀ y ∈ Iio (0:ℝ), HasDerivWithinAt (fun y : ℝ => -(c * y)⁻¹) ((c * y ^ 2)⁻¹) (Iio 0) y := by
    intro y hy
    have hy0 : y ≠ 0 := ne_of_lt hy
    have hy' : c * y ≠ 0 := mul_ne_zero hc.ne' hy0
    have h1 : HasDerivAt (fun y : ℝ => c * y) c y := by simpa using (hasDerivAt_id y).const_mul c
    have h3 := (h1.inv hy').neg
    have e : -(-c / (c * y) ^ 2) = (c * y ^ 2)⁻¹ := by field_simp
    rw [e] at h3
    exact h3.hasDerivWithinAt
  have hinj : InjOn (fun y : ℝ => -(c * y)⁻¹) (Iio 0) := by
    intro y₁ h₁ y₂ h₂ h
    have : (c * y₁)⁻¹ = (c * y₂)⁻¹ := neg_inj.1 h
    have := inv_inj.1 this
    exact mul_left_cancel₀ hc.ne' this
  have himg : (fun y : ℝ => -(c * y)⁻¹) '' Iio 0 = Ioi 0 := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have : c * y < 0 := mul_neg_of_pos_of_neg hc hy
      exact neg_pos.2 (inv_neg''.2 this)
    · intro hx
      refine ⟨-(c * x)⁻¹, ?_, ?_⟩
      · have : 0 < c * x := mul_pos hc hx
        exact neg_neg_of_pos (inv_pos.2 this)
      · have hx0 : x ≠ 0 := ne_of_gt hx
        field_simp
  have habs : ∀ y ∈ Iio (0:ℝ), |(c * y ^ 2)⁻¹| = (c * y ^ 2)⁻¹ := fun y hy => abs_of_pos (by
    have : y ≠ 0 := ne_of_lt hy; positivity)
  constructor
  · have h := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Iio hderiv hinj g
    rw [himg] at h
    rw [h]
    exact integrableOn_congr_fun (fun y hy => by rw [habs y hy]) measurableSet_Iio
  · have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Iio hderiv hinj g
    rw [himg] at h
    rw [h]
    exact setIntegral_congr_fun measurableSet_Iio (fun y hy => by rw [habs y hy])

end OneDim'

theorem integrable_iff_pullback_negInv' {Z : Type*} [MeasurableSpace Z] (ν : Measure Z) [SFinite ν]
    (c : Z → ℝ) (hcm : Measurable c) (hc : ∀ᵐ z ∂ν, 0 < c z)
    (F : Z × ℝ → ℂ) (hF : Measurable F) :
    Integrable F (ν.prod (volume.restrict (Ioi 0))) ↔
      Integrable (fun p : Z × ℝ => (c p.1 * p.2 ^ 2)⁻¹ • F (p.1, -(c p.1 * p.2)⁻¹))
        (ν.prod (volume.restrict (Iio 0))) := by
  have hGm : Measurable (fun p : Z × ℝ => (c p.1 * p.2 ^ 2)⁻¹ • F (p.1, -(c p.1 * p.2)⁻¹)) := by
    refine Measurable.smul (((hcm.comp measurable_fst).mul (measurable_snd.pow_const 2)).inv) ?_
    exact hF.comp (measurable_fst.prodMk ((hcm.comp measurable_fst).mul measurable_snd).inv.neg)
  refine integrable_prod_iff_of_fiber _ _ _ _ hF.aestronglyMeasurable hGm.aestronglyMeasurable ?_ ?_
  · filter_upwards [hc] with z hz
    exact (subst_negInv' (c z) hz (fun x => F (z, x))).1
  · filter_upwards [hc] with z hz
    have h := (subst_negInv' (c z) hz (fun x => ‖F (z, x)‖)).2
    rw [h]
    refine setIntegral_congr_fun measurableSet_Iio (fun y (hy : y < (0:ℝ)) => ?_)
    have : y ≠ 0 := ne_of_lt hy
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), smul_eq_mul]

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

def sig : (α × β) × γ ≃ᵐ (α × γ) × β :=
  (MeasurableEquiv.prodAssoc.trans ((MeasurableEquiv.refl α).prodCongr MeasurableEquiv.prodComm)).trans
    MeasurableEquiv.prodAssoc.symm

theorem sig_apply (p : (α × β) × γ) : (sig p : (α × γ) × β) = ((p.1.1, p.2), p.1.2) := rfl

theorem measurePreserving_sig (μ : Measure α) (ν : Measure β) (ρ : Measure γ)
    [SFinite μ] [SFinite ν] [SFinite ρ] :
    MeasurePreserving (sig : (α × β) × γ ≃ᵐ (α × γ) × β) ((μ.prod ν).prod ρ) ((μ.prod ρ).prod ν) := by
  have h1 : MeasurePreserving (MeasurableEquiv.prodAssoc : (α × β) × γ ≃ᵐ α × β × γ)
      ((μ.prod ν).prod ρ) (μ.prod (ν.prod ρ)) := measurePreserving_prodAssoc μ ν ρ
  have h2 : MeasurePreserving ((MeasurableEquiv.refl α).prodCongr (MeasurableEquiv.prodComm : β × γ ≃ᵐ γ × β))
      (μ.prod (ν.prod ρ)) (μ.prod (ρ.prod ν)) :=
    (MeasurePreserving.id μ).prod Measure.measurePreserving_swap
  have h3 : MeasurePreserving (MeasurableEquiv.prodAssoc.symm : α × γ × β ≃ᵐ (α × γ) × β)
      (μ.prod (ρ.prod ν)) ((μ.prod ρ).prod ν) := (measurePreserving_prodAssoc μ ρ ν).symm _
  exact h3.comp (h2.comp h1)

def tau : α × β × γ ≃ᵐ (α × γ) × β :=
  ((MeasurableEquiv.refl α).prodCongr (MeasurableEquiv.prodComm : β × γ ≃ᵐ γ × β)).trans
    MeasurableEquiv.prodAssoc.symm

theorem tau_apply (p : α × β × γ) : (tau p : (α × γ) × β) = ((p.1, p.2.2), p.2.1) := rfl

theorem measurePreserving_tau (μ : Measure α) (ν : Measure β) (ρ : Measure γ)
    [SFinite μ] [SFinite ν] [SFinite ρ] :
    MeasurePreserving (tau : α × β × γ ≃ᵐ (α × γ) × β) (μ.prod (ν.prod ρ)) ((μ.prod ρ).prod ν) := by
  have h2 : MeasurePreserving ((MeasurableEquiv.refl α).prodCongr (MeasurableEquiv.prodComm : β × γ ≃ᵐ γ × β))
      (μ.prod (ν.prod ρ)) (μ.prod (ρ.prod ν)) :=
    (MeasurePreserving.id μ).prod Measure.measurePreserving_swap
  have h3 : MeasurePreserving (MeasurableEquiv.prodAssoc.symm : α × γ × β ≃ᵐ (α × γ) × β)
      (μ.prod (ρ.prod ν)) ((μ.prod ρ).prod ν) := (measurePreserving_prodAssoc μ ρ ν).symm _
  exact h3.comp h2

theorem measurePreserving_neg_Iio_Ioi :
    MeasurePreserving (fun t : ℝ => -t) (volume.restrict (Iio (0:ℝ))) (volume.restrict (Ioi (0:ℝ))) := by
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
    (measurableSet_Ioi : MeasurableSet (Ioi (0:ℝ)))
  have e : (Neg.neg : ℝ → ℝ) ⁻¹' Ioi (0:ℝ) = Iio 0 := by
    ext t; simp
  rw [e] at h
  exact h

theorem measurePreserving_neg_Ioi_Iio :
    MeasurePreserving (fun t : ℝ => -t) (volume.restrict (Ioi (0:ℝ))) (volume.restrict (Iio (0:ℝ))) := by
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
    (measurableSet_Iio : MeasurableSet (Iio (0:ℝ)))
  have e : (Neg.neg : ℝ → ℝ) ⁻¹' Iio (0:ℝ) = Ioi 0 := by
    ext t; simp
  rw [e] at h
  exact h

local notation "μ₊" => Measure.restrict (volume : Measure ℝ) (Ioi (0:ℝ))
local notation "μ₋" => Measure.restrict (volume : Measure ℝ) (Iio (0:ℝ))

theorem transport (H : ℝ × ℝ × ℝ → ℂ) (hH : Measurable H) (hI : Integrable H ((μ₊).prod ((μ₋).prod (μ₊)))) :
    Integrable (fun q : ℝ × ℝ × ℝ =>
        ((-q.1) * q.2.1 ^ 2)⁻¹ • ((1 * q.2.2 ^ 2)⁻¹ • H (-q.1, -((-q.1) * q.2.1)⁻¹, -(1 * q.2.2)⁻¹)))
      ((μ₋).prod ((μ₊).prod (μ₋))) := by

  set F₁ : (ℝ × ℝ) × ℝ → ℂ := fun p => H (p.1.1, p.1.2, p.2) with hF₁
  have mF₁ : Measurable F₁ :=
    hH.comp ((measurable_fst.comp measurable_fst).prodMk ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have I₁ : Integrable F₁ (((μ₊).prod (μ₋)).prod (μ₊)) :=
    ((measurePreserving_prodAssoc (μ₊) (μ₋) (μ₊)).integrable_comp_emb
      (MeasurableEquiv.prodAssoc).measurableEmbedding).mpr hI

  have I₂ := (integrable_iff_pullback_negInv' ((μ₊).prod (μ₋)) (fun _ => (1:ℝ)) measurable_const
    (ae_of_all _ fun _ => one_pos) F₁ mF₁).mp I₁
  set G₁ : (ℝ × ℝ) × ℝ → ℂ := fun p => ((1:ℝ) * p.2 ^ 2)⁻¹ • F₁ (p.1, -((1:ℝ) * p.2)⁻¹) with hG₁
  have mG₁ : Measurable G₁ := by
    refine Measurable.smul ((measurable_const.mul (measurable_snd.pow_const 2)).inv) ?_
    exact mF₁.comp (measurable_fst.prodMk ((measurable_const.mul measurable_snd).inv.neg))
  have I₂' : Integrable G₁ (((μ₊).prod (μ₋)).prod (μ₋)) := I₂

  set F₂ : (ℝ × ℝ) × ℝ → ℂ := fun p => G₁ ((p.1.1, p.2), p.1.2) with hF₂
  have mF₂ : Measurable F₂ :=
    mG₁.comp (((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk (measurable_snd.comp measurable_fst))
  have I₃ : Integrable F₂ (((μ₊).prod (μ₋)).prod (μ₋)) :=
    ((measurePreserving_sig (μ₊) (μ₋) (μ₋)).integrable_comp_emb (sig).measurableEmbedding).mpr I₂'

  have hc : ∀ᵐ z : ℝ × ℝ ∂((μ₊).prod (μ₋)), 0 < z.1 :=
    (Measure.quasiMeasurePreserving_fst).ae (ae_restrict_mem measurableSet_Ioi)
  have I₄ := (integrable_iff_pullback_negInv ((μ₊).prod (μ₋)) (fun z => z.1) measurable_fst hc F₂ mF₂).mp I₃
  set G₂ : (ℝ × ℝ) × ℝ → ℂ := fun p => (p.1.1 * p.2 ^ 2)⁻¹ • F₂ (p.1, -(p.1.1 * p.2)⁻¹) with hG₂
  have I₄' : Integrable G₂ (((μ₊).prod (μ₋)).prod (μ₊)) := I₄

  have hθ : MeasurePreserving (fun q : ℝ × ℝ × ℝ => ((-q.1, q.2.2), q.2.1))
      ((μ₋).prod ((μ₊).prod (μ₋))) (((μ₊).prod (μ₋)).prod (μ₊)) := by
    have h1 : MeasurePreserving (fun q : ℝ × ℝ × ℝ => (-q.1, q.2))
        ((μ₋).prod ((μ₊).prod (μ₋))) ((μ₊).prod ((μ₊).prod (μ₋))) :=
      measurePreserving_neg_Iio_Ioi.prod (MeasurePreserving.id _)
    have h2 := measurePreserving_tau (μ₊) (μ₊) (μ₋)
    have := h2.comp h1
    exact this
  have I₅ := (hθ.integrable_comp I₄'.aestronglyMeasurable).mpr I₄'
  refine I₅.congr (ae_of_all _ fun q => ?_)
  simp only [Function.comp, hG₂, hF₂, hG₁, hF₁]

end K9F2

end

namespace K9F2i
variable {X Y Z T E : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace T]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def assoc4 : X × Y × Z × T ≃ᵐ (X × Y × Z) × T :=
  ((MeasurableEquiv.refl X).prodCongr (MeasurableEquiv.prodAssoc.symm : Y × Z × T ≃ᵐ (Y × Z) × T)).trans
    (MeasurableEquiv.prodAssoc.symm : X × (Y × Z) × T ≃ᵐ (X × Y × Z) × T)

theorem assoc4_symm_apply (p : (X × Y × Z) × T) : ((assoc4).symm p : X × Y × Z × T) = (p.1.1, p.1.2.1, p.1.2.2, p.2) := rfl

theorem measurePreserving_assoc4 (μ : Measure X) (ν : Measure Y) (ρ : Measure Z) (τ : Measure T)
    [SFinite μ] [SFinite ν] [SFinite ρ] [SFinite τ] :
    MeasurePreserving (assoc4 : X × Y × Z × T ≃ᵐ (X × Y × Z) × T)
      (μ.prod (ν.prod (ρ.prod τ))) ((μ.prod (ν.prod ρ)).prod τ) := by
  have h1 : MeasurePreserving ((MeasurableEquiv.refl X).prodCongr
      (MeasurableEquiv.prodAssoc.symm : Y × Z × T ≃ᵐ (Y × Z) × T))
      (μ.prod (ν.prod (ρ.prod τ))) (μ.prod ((ν.prod ρ).prod τ)) :=
    (MeasurePreserving.id μ).prod ((MeasureTheory.measurePreserving_prodAssoc ν ρ τ).symm _)
  have h2 : MeasurePreserving (MeasurableEquiv.prodAssoc.symm : X × (Y × Z) × T ≃ᵐ (X × Y × Z) × T)
      (μ.prod ((ν.prod ρ).prod τ)) ((μ.prod (ν.prod ρ)).prod τ) :=
    (MeasureTheory.measurePreserving_prodAssoc μ (ν.prod ρ) τ).symm _
  exact h2.comp h1

theorem integrable_integral_inner4 (μ : Measure X) (ν : Measure Y) (ρ : Measure Z) (τ : Measure T)
    [SFinite μ] [SFinite ν] [SFinite ρ] [SFinite τ]
    (F : X × Y × Z × T → E) (hF : Integrable F (μ.prod (ν.prod (ρ.prod τ)))) :
    Integrable (fun p : X × Y × Z => ∫ t, F (p.1, p.2.1, p.2.2, t) ∂τ) (μ.prod (ν.prod ρ)) := by
  have hc := measurePreserving_assoc4 μ ν ρ τ
  have hF' : Integrable (fun q : (X × Y × Z) × T => F ((assoc4).symm q)) ((μ.prod (ν.prod ρ)).prod τ) :=
    ((hc.symm _).integrable_comp_emb (assoc4).symm.measurableEmbedding).mpr hF
  exact hF'.integral_prod_left

end K9F2i

noncomputable section
namespace K9F2
open Real

local notation "μ₊" => Measure.restrict (volume : Measure ℝ) (Ioi (0:ℝ))
local notation "μ₋" => Measure.restrict (volume : Measure ℝ) (Iio (0:ℝ))

def Zi (m : ℕ) (c : ℝ) : ℂ := ∫ z : ℝ, (((c : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m * (Real.exp (-(Real.pi * z ^ 2)) : ℂ)

theorem Zi_neg (m : ℕ) (c : ℝ) : Zi m (-c) = (-1 : ℂ) ^ m * Zi m c := by
  unfold Zi
  rw [← integral_const_mul, ← integral_neg_eq_self]
  congr 1; funext z
  push_cast
  rw [neg_sq, show (-(c : ℂ) + Complex.I * -(z : ℂ)) = -(((c : ℂ)) + Complex.I * (z : ℂ)) by ring, neg_pow]
  ring

theorem measurable_Zi (m : ℕ) : Measurable (Zi m) := by
  have hc : Continuous (fun p : ℝ × ℝ => (((p.1 : ℝ) : ℂ) + Complex.I * (p.2 : ℂ)) ^ m * (Real.exp (-(Real.pi * p.2 ^ 2)) : ℂ)) := by
    fun_prop
  exact (hc.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))).measurable

def Phi (A₁ β γ w : ℂ) (m n : ℕ) (S g : ℝ → ℂ) (q : ℝ × ℝ × ℝ) : ℂ :=
  ((|q.2.2| : ℝ) : ℂ) ^ (w + 1) *
    (((|q.1| : ℝ) : ℂ) ^ A₁ * (Real.exp (-(2 * Real.pi * |q.1|)) : ℂ) *
      (((q.2.2⁻¹ : ℝ) : ℂ) ^ n * S q.2.2 * ((|q.2.2| : ℝ) : ℂ) ^ β * ((q.2.1 : ℝ) : ℂ) ^ γ) *
      (Real.exp (-(Real.pi * ((q.2.1 ^ 2)⁻¹ + q.1 ^ 2 * q.2.1 ^ 2 + q.2.2 ^ 2))) : ℂ) *
      g (q.2.2 / q.2.1) *
      Zi m (q.1 * q.2.1 - q.2.1⁻¹ + q.2.2))

def H3 (α' β' γ' : ℂ) (m : ℕ) (G : ℝ → ℂ) (br : ℝ × ℝ × ℝ → ℝ) (p : ℝ × ℝ × ℝ) : ℂ :=
  ((p.1 : ℝ) : ℂ) ^ α' * (Real.exp (-(2 * Real.pi * p.1)) : ℂ) *
    ((|p.2.1| : ℝ) : ℂ) ^ β' * ((p.2.2 : ℝ) : ℂ) ^ γ' *
    (Real.exp (-(Real.pi * ((p.2.1 ^ 2)⁻¹ + p.1 ^ 2 * p.2.1 ^ 2 + (p.2.2 ^ 2)⁻¹))) : ℂ) *
    G (p.1 * |p.2.1| / p.2.2) * Zi m (br p)

def brM (p : ℝ × ℝ × ℝ) : ℝ := p.2.1⁻¹ - p.2.2⁻¹ + p.1 * p.2.1
def brP (p : ℝ × ℝ × ℝ) : ℝ := -p.2.1⁻¹ - p.2.2⁻¹ - p.1 * p.2.1

theorem measurable_brM : Measurable brM := by unfold brM; fun_prop
theorem measurable_brP : Measurable brP := by unfold brP; fun_prop

theorem measurable_H3 (α' β' γ' : ℂ) (m : ℕ) (G : ℝ → ℂ) (hG : Measurable G) (br : ℝ × ℝ × ℝ → ℝ)
    (hbr : Measurable br) : Measurable (H3 α' β' γ' m G br) := by
  unfold H3
  have cR : Measurable (fun x : ℝ => (x : ℂ)) := Complex.measurable_ofReal
  have m1 : Measurable fun p : ℝ × ℝ × ℝ => (((p.1 : ℝ) : ℂ)) ^ α' := (cR.comp measurable_fst).pow_const _
  have m2 : Measurable fun p : ℝ × ℝ × ℝ => ((Real.exp (-(2 * Real.pi * p.1)) : ℝ) : ℂ) := cR.comp (by fun_prop)
  have m3 : Measurable fun p : ℝ × ℝ × ℝ => (((|p.2.1| : ℝ) : ℂ)) ^ β' :=
    (cR.comp (measurable_fst.comp measurable_snd).abs).pow_const _
  have m4 : Measurable fun p : ℝ × ℝ × ℝ => (((p.2.2 : ℝ) : ℂ)) ^ γ' := (cR.comp (measurable_snd.comp measurable_snd)).pow_const _
  have m5 : Measurable fun p : ℝ × ℝ × ℝ =>
      ((Real.exp (-(Real.pi * ((p.2.1 ^ 2)⁻¹ + p.1 ^ 2 * p.2.1 ^ 2 + (p.2.2 ^ 2)⁻¹))) : ℝ) : ℂ) := cR.comp (by fun_prop)
  have m6 : Measurable fun p : ℝ × ℝ × ℝ => G (p.1 * |p.2.1| / p.2.2) :=
    hG.comp ((measurable_fst.mul (measurable_fst.comp measurable_snd).abs).div (measurable_snd.comp measurable_snd))
  have m7 : Measurable fun p : ℝ × ℝ × ℝ => Zi m (br p) := (measurable_Zi m).comp hbr
  exact (((((m1.mul m2).mul m3).mul m4).mul m5).mul m6).mul m7

theorem measurable_Phi (A₁ β γ w : ℂ) (m n : ℕ) (S g : ℝ → ℂ) (hS : Measurable S) (hg : Measurable g) :
    Measurable (Phi A₁ β γ w m n S g) := by
  unfold Phi
  have cR : Measurable (fun x : ℝ => (x : ℂ)) := Complex.measurable_ofReal
  have mt : Measurable fun q : ℝ × ℝ × ℝ => q.1 := measurable_fst
  have mY : Measurable fun q : ℝ × ℝ × ℝ => q.2.1 := measurable_fst.comp measurable_snd
  have mu : Measurable fun q : ℝ × ℝ × ℝ => q.2.2 := measurable_snd.comp measurable_snd
  have m0 : Measurable fun q : ℝ × ℝ × ℝ => (((|q.2.2| : ℝ) : ℂ)) ^ (w + 1) := (cR.comp mu.abs).pow_const _
  have m1 : Measurable fun q : ℝ × ℝ × ℝ => (((|q.1| : ℝ) : ℂ)) ^ A₁ := (cR.comp mt.abs).pow_const _
  have m2 : Measurable fun q : ℝ × ℝ × ℝ => ((Real.exp (-(2 * Real.pi * |q.1|)) : ℝ) : ℂ) := cR.comp (by fun_prop)
  have m3 : Measurable fun q : ℝ × ℝ × ℝ => (((q.2.2⁻¹ : ℝ) : ℂ)) ^ n := (cR.comp mu.inv).pow_const _
  have m4 : Measurable fun q : ℝ × ℝ × ℝ => S q.2.2 := hS.comp mu
  have m5 : Measurable fun q : ℝ × ℝ × ℝ => (((|q.2.2| : ℝ) : ℂ)) ^ β := (cR.comp mu.abs).pow_const _
  have m6 : Measurable fun q : ℝ × ℝ × ℝ => (((q.2.1 : ℝ) : ℂ)) ^ γ := (cR.comp mY).pow_const _
  have m7 : Measurable fun q : ℝ × ℝ × ℝ =>
      ((Real.exp (-(Real.pi * ((q.2.1 ^ 2)⁻¹ + q.1 ^ 2 * q.2.1 ^ 2 + q.2.2 ^ 2))) : ℝ) : ℂ) := cR.comp (by fun_prop)
  have m8 : Measurable fun q : ℝ × ℝ × ℝ => g (q.2.2 / q.2.1) := hg.comp (mu.div mY)
  have m9 : Measurable fun q : ℝ × ℝ × ℝ => Zi m (q.1 * q.2.1 - q.2.1⁻¹ + q.2.2) :=
    (measurable_Zi m).comp (((mt.mul mY).sub mY.inv).add mu)
  exact m0.mul ((((((m1.mul m2).mul (((m3.mul m4).mul m5).mul m6)).mul m7).mul m8).mul m9))

end K9F2
end

noncomputable section
namespace K9F2
open Real

theorem cpow_pos' (x : ℝ) (hx : 0 < x) (s : ℂ) : ((x : ℝ) : ℂ) ^ s = Complex.exp ((Real.log x : ℂ) * s) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hx.ne'), Complex.ofReal_log hx.le]

theorem ofReal_pos' (x : ℝ) (hx : 0 < x) : ((x : ℝ) : ℂ) = Complex.exp (Real.log x : ℂ) := by
  rw [← Complex.ofReal_exp, Real.exp_log hx]

theorem powid_minus (τ Y v : ℝ) (hτ : 0 < τ) (hY : 0 < Y) (hv : 0 < v) (A₁ β γ w : ℂ) (n : ℕ) :
    ((v : ℝ) : ℂ) ^ (w + 1) * ((τ : ℝ) : ℂ) ^ A₁ * ((((-v)⁻¹ : ℝ)) : ℂ) ^ n * ((v : ℝ) : ℂ) ^ β * ((Y : ℝ) : ℂ) ^ γ =
      (-1 : ℂ) ^ n * (((τ * Y ^ 2)⁻¹ : ℝ) : ℂ) * ((((1 * (-v) ^ 2)⁻¹ : ℝ)) : ℂ) *
        ((τ : ℝ) : ℂ) ^ (A₁ - γ - 1) * ((((τ * Y)⁻¹ : ℝ)) : ℂ) ^ (-γ - 2) *
        (((v⁻¹ : ℝ)) : ℂ) ^ ((n : ℂ) - w - β - 3) := by
  have hτY : 0 < τ * Y := mul_pos hτ hY
  have hτY2 : 0 < (τ * Y ^ 2)⁻¹ := by positivity
  have hv2 : 0 < (1 * (-v) ^ 2)⁻¹ := by rw [neg_sq, one_mul]; positivity
  have hvi : 0 < v⁻¹ := inv_pos.2 hv
  have hτYi : 0 < (τ * Y)⁻¹ := inv_pos.2 hτY

  have l1 : Real.log ((τ * Y ^ 2)⁻¹) = -(Real.log τ + 2 * Real.log Y) := by
    rw [Real.log_inv, Real.log_mul hτ.ne' (by positivity), Real.log_pow]; push_cast; ring
  have l2 : Real.log ((1 * (-v) ^ 2)⁻¹) = -(2 * Real.log v) := by
    rw [neg_sq, one_mul, Real.log_inv, Real.log_pow]; push_cast; ring
  have l3 : Real.log ((τ * Y)⁻¹) = -(Real.log τ + Real.log Y) := by
    rw [Real.log_inv, Real.log_mul hτ.ne' hY.ne']
  have l4 : Real.log (v⁻¹) = -Real.log v := Real.log_inv v

  have e_neg : ((((-v)⁻¹ : ℝ)) : ℂ) ^ n = (-1 : ℂ) ^ n * (((v⁻¹ : ℝ)) : ℂ) ^ n := by
    rw [inv_neg, Complex.ofReal_neg, neg_pow]
  rw [e_neg]
  simp only [cpow_pos' τ hτ, cpow_pos' v hv, cpow_pos' Y hY, cpow_pos' _ hτYi, cpow_pos' _ hvi]
  rw [ofReal_pos' _ hvi, ← Complex.exp_nat_mul, ofReal_pos' _ hτY2, ofReal_pos' _ hv2, l1, l2, l3, l4]

  have L : ∀ p₁ p₂ p₃ p₄ p₅ : ℂ, Complex.exp p₁ * Complex.exp p₂ * ((-1 : ℂ) ^ n * Complex.exp p₃) * Complex.exp p₄ *
      Complex.exp p₅ = (-1 : ℂ) ^ n * Complex.exp (p₁ + p₂ + p₃ + p₄ + p₅) := by
    intro p₁ p₂ p₃ p₄ p₅; rw [Complex.exp_add, Complex.exp_add, Complex.exp_add, Complex.exp_add]; ring
  have R : ∀ q₁ q₂ q₃ q₄ q₅ : ℂ, (-1 : ℂ) ^ n * Complex.exp q₁ * Complex.exp q₂ * Complex.exp q₃ * Complex.exp q₄ *
      Complex.exp q₅ = (-1 : ℂ) ^ n * Complex.exp (q₁ + q₂ + q₃ + q₄ + q₅) := by
    intro q₁ q₂ q₃ q₄ q₅; rw [Complex.exp_add, Complex.exp_add, Complex.exp_add, Complex.exp_add]; ring
  rw [L, R]
  congr 2
  push_cast
  ring

end K9F2
end

noncomputable section
namespace K9F2
open Real

theorem powid_plus (τ Y u : ℝ) (hτ : 0 < τ) (hY : 0 < Y) (hu : 0 < u) (A₁ β γ w : ℂ) (n : ℕ) :
    ((u : ℝ) : ℂ) ^ (w + 1) * ((τ : ℝ) : ℂ) ^ A₁ * (((u⁻¹ : ℝ)) : ℂ) ^ n * ((u : ℝ) : ℂ) ^ β * ((Y : ℝ) : ℂ) ^ γ =
      (((τ * Y ^ 2)⁻¹ : ℝ) : ℂ) * ((((1 * (-u) ^ 2)⁻¹ : ℝ)) : ℂ) *
        ((τ : ℝ) : ℂ) ^ (A₁ - γ - 1) * ((((τ * Y)⁻¹ : ℝ)) : ℂ) ^ (-γ - 2) *
        (((u⁻¹ : ℝ)) : ℂ) ^ ((n : ℂ) - w - β - 3) := by
  have hτY : 0 < τ * Y := mul_pos hτ hY
  have hτY2 : 0 < (τ * Y ^ 2)⁻¹ := by positivity
  have hu2 : 0 < (1 * (-u) ^ 2)⁻¹ := by rw [neg_sq, one_mul]; positivity
  have hui : 0 < u⁻¹ := inv_pos.2 hu
  have hτYi : 0 < (τ * Y)⁻¹ := inv_pos.2 hτY
  have l1 : Real.log ((τ * Y ^ 2)⁻¹) = -(Real.log τ + 2 * Real.log Y) := by
    rw [Real.log_inv, Real.log_mul hτ.ne' (by positivity), Real.log_pow]; push_cast; ring
  have l2 : Real.log ((1 * (-u) ^ 2)⁻¹) = -(2 * Real.log u) := by
    rw [neg_sq, one_mul, Real.log_inv, Real.log_pow]; push_cast; ring
  have l3 : Real.log ((τ * Y)⁻¹) = -(Real.log τ + Real.log Y) := by
    rw [Real.log_inv, Real.log_mul hτ.ne' hY.ne']
  have l4 : Real.log (u⁻¹) = -Real.log u := Real.log_inv u
  simp only [cpow_pos' τ hτ, cpow_pos' u hu, cpow_pos' Y hY, cpow_pos' _ hτYi, cpow_pos' _ hui]
  rw [ofReal_pos' _ hui, ← Complex.exp_nat_mul, ofReal_pos' _ hτY2, ofReal_pos' _ hu2, l1, l2, l3, l4]
  have L : ∀ p₁ p₂ p₃ p₄ p₅ : ℂ, Complex.exp p₁ * Complex.exp p₂ * Complex.exp p₃ * Complex.exp p₄ *
      Complex.exp p₅ = Complex.exp (p₁ + p₂ + p₃ + p₄ + p₅) := by
    intro p₁ p₂ p₃ p₄ p₅; rw [Complex.exp_add, Complex.exp_add, Complex.exp_add, Complex.exp_add]
  rw [L, L]
  congr 1
  push_cast
  ring

theorem powid_minus' (t Y u : ℝ) (ht : t < 0) (hY : 0 < Y) (hu : u < 0) (A₁ β γ w : ℂ) (n : ℕ) :
    ((|u| : ℝ) : ℂ) ^ (w + 1) * ((|t| : ℝ) : ℂ) ^ A₁ * (((u⁻¹ : ℝ)) : ℂ) ^ n * ((|u| : ℝ) : ℂ) ^ β * ((Y : ℝ) : ℂ) ^ γ =
      (-1 : ℂ) ^ n * ((((-t) * Y ^ 2)⁻¹ : ℝ) : ℂ) * ((((1 * u ^ 2)⁻¹ : ℝ)) : ℂ) *
        (((-t : ℝ)) : ℂ) ^ (A₁ - γ - 1) * (((|-((-t) * Y)⁻¹| : ℝ)) : ℂ) ^ (-γ - 2) *
        (((-(1 * u)⁻¹ : ℝ)) : ℂ) ^ ((n : ℂ) - w - β - 3) := by
  have hτ : 0 < -t := by linarith
  have hv : 0 < -u := by linarith
  have e1 : |u| = -u := abs_of_neg hu
  have e2 : |t| = -t := abs_of_neg ht
  have e3 : u⁻¹ = (-(-u))⁻¹ := by rw [neg_neg]
  have e4 : |-((-t) * Y)⁻¹| = ((-t) * Y)⁻¹ := by rw [abs_neg, abs_of_pos (by positivity)]
  have e5 : -(1 * u)⁻¹ = (-u)⁻¹ := by rw [one_mul, inv_neg]
  have e6 : (1 * u ^ 2)⁻¹ = (1 * (-(-u)) ^ 2)⁻¹ := by rw [neg_neg]
  rw [e1, e2, e3, e4, e5, e6]
  exact powid_minus (-t) Y (-u) hτ hY hv A₁ β γ w n

theorem powid_plus' (t Y v : ℝ) (ht : t < 0) (hY : 0 < Y) (hv : v < 0) (A₁ β γ w : ℂ) (n : ℕ) :
    ((|-v| : ℝ) : ℂ) ^ (w + 1) * ((|t| : ℝ) : ℂ) ^ A₁ * ((((-v)⁻¹ : ℝ)) : ℂ) ^ n * ((|-v| : ℝ) : ℂ) ^ β * ((Y : ℝ) : ℂ) ^ γ =
      ((((-t) * Y ^ 2)⁻¹ : ℝ) : ℂ) * ((((1 * v ^ 2)⁻¹ : ℝ)) : ℂ) *
        (((-t : ℝ)) : ℂ) ^ (A₁ - γ - 1) * (((|-((-t) * Y)⁻¹| : ℝ)) : ℂ) ^ (-γ - 2) *
        (((-(1 * v)⁻¹ : ℝ)) : ℂ) ^ ((n : ℂ) - w - β - 3) := by
  have hτ : 0 < -t := by linarith
  have hu : 0 < -v := by linarith
  have e1 : |-v| = -v := by rw [abs_neg, abs_of_neg hv]
  have e2 : |t| = -t := abs_of_neg ht
  have e4 : |-((-t) * Y)⁻¹| = ((-t) * Y)⁻¹ := by rw [abs_neg, abs_of_pos (by positivity)]
  have e5 : -(1 * v)⁻¹ = (-v)⁻¹ := by rw [one_mul, inv_neg]
  have e6 : (1 * v ^ 2)⁻¹ = (1 * (-(-v)) ^ 2)⁻¹ := by rw [neg_neg]
  rw [e1, e2, e4, e5, e6]
  exact powid_plus (-t) Y (-v) hτ hY hu A₁ β γ w n

end K9F2
end

noncomputable section
namespace K9F2
open Real

theorem S_of_neg (S : ℝ → ℂ) (hS : ∀ c : ℝ, 0 < c → ∀ y : ℝ, S (y / c) = S y) {u : ℝ} (hu : u < 0) :
    S u = S (-1) := by
  have h := hS (-u) (by linarith) u
  rw [div_neg, div_self hu.ne] at h
  exact h.symm

theorem S_of_pos (S : ℝ → ℂ) (hS : ∀ c : ℝ, 0 < c → ∀ y : ℝ, S (y / c) = S y) {u : ℝ} (hu : 0 < u) :
    S u = S 1 := by
  have h := hS u hu u
  rw [div_self hu.ne'] at h
  exact h.symm

theorem pointwise_minus (A₁ β γ w : ℂ) (m n : ℕ) (S g : ℝ → ℂ)
    (hS : ∀ c : ℝ, 0 < c → ∀ y : ℝ, S (y / c) = S y)
    (t Y u : ℝ) (ht : t < 0) (hY : 0 < Y) (hu : u < 0) :
    Phi A₁ β γ w m n S g (t, Y, u) =
      ((-1 : ℂ) ^ n * S (-1)) *
        (((-t) * Y ^ 2)⁻¹ • ((1 * u ^ 2)⁻¹ •
          H3 (A₁ - γ - 1) (-γ - 2) ((n : ℂ) - w - β - 3) m (fun v : ℝ => g (-v)) brM
            (-t, -((-t) * Y)⁻¹, -(1 * u)⁻¹))) := by
  have hτ : 0 < -t := by linarith
  have hv : 0 < -u := by linarith
  have ht0 : t ≠ 0 := ht.ne
  have hu0 : u ≠ 0 := hu.ne
  have hY0 : Y ≠ 0 := hY.ne'
  have hb := powid_minus' t Y u ht hY hu A₁ β γ w n
  have r_abs1 : |-((-t) * Y)⁻¹| = ((-t) * Y)⁻¹ := by rw [abs_neg, abs_of_pos (by positivity)]
  have r_E : ((-((-t) * Y)⁻¹) ^ 2)⁻¹ + (-t) ^ 2 * (-((-t) * Y)⁻¹) ^ 2 + ((-(1 * u)⁻¹) ^ 2)⁻¹ =
      (Y ^ 2)⁻¹ + t ^ 2 * Y ^ 2 + u ^ 2 := by
    field_simp
    ring
  have r_g : -((-t) * ((-t) * Y)⁻¹ / (-(1 * u)⁻¹)) = u / Y := by
    field_simp
  have r_br : (-((-t) * Y)⁻¹)⁻¹ - (-(1 * u)⁻¹)⁻¹ + (-t) * (-((-t) * Y)⁻¹) = t * Y - Y⁻¹ + u := by
    field_simp
    ring
  have r_S : S u = S (-1) := S_of_neg S hS hu
  simp only [Phi, H3, brM]
  rw [r_abs1] at hb ⊢
  rw [r_E, r_g, r_br, r_S, abs_of_neg ht, Complex.real_smul, Complex.real_smul]
  rw [abs_of_neg ht] at hb
  linear_combination ((Real.exp (-(2 * Real.pi * -t)) : ℂ) * S (-1) *
    (Real.exp (-(Real.pi * ((Y ^ 2)⁻¹ + t ^ 2 * Y ^ 2 + u ^ 2))) : ℂ) * g (u / Y) * Zi m (t * Y - Y⁻¹ + u)) * hb

theorem pointwise_plus (A₁ β γ w : ℂ) (m n : ℕ) (S g : ℝ → ℂ)
    (hS : ∀ c : ℝ, 0 < c → ∀ y : ℝ, S (y / c) = S y)
    (t Y v : ℝ) (ht : t < 0) (hY : 0 < Y) (hv : v < 0) :
    Phi A₁ β γ w m n S g (t, Y, -v) =
      ((-1 : ℂ) ^ m * S 1) *
        (((-t) * Y ^ 2)⁻¹ • ((1 * v ^ 2)⁻¹ •
          H3 (A₁ - γ - 1) (-γ - 2) ((n : ℂ) - w - β - 3) m g brP
            (-t, -((-t) * Y)⁻¹, -(1 * v)⁻¹))) := by
  have hτ : 0 < -t := by linarith
  have hu : 0 < -v := by linarith
  have ht0 : t ≠ 0 := ht.ne
  have hv0 : v ≠ 0 := hv.ne
  have hY0 : Y ≠ 0 := hY.ne'
  have hb := powid_plus' t Y v ht hY hv A₁ β γ w n
  have r_abs1 : |-((-t) * Y)⁻¹| = ((-t) * Y)⁻¹ := by rw [abs_neg, abs_of_pos (by positivity)]
  have r_E : ((-((-t) * Y)⁻¹) ^ 2)⁻¹ + (-t) ^ 2 * (-((-t) * Y)⁻¹) ^ 2 + ((-(1 * v)⁻¹) ^ 2)⁻¹ =
      (Y ^ 2)⁻¹ + t ^ 2 * Y ^ 2 + (-v) ^ 2 := by
    field_simp
    ring
  have r_g : (-t) * ((-t) * Y)⁻¹ / (-(1 * v)⁻¹) = -v / Y := by
    field_simp
  have r_br : -(-((-t) * Y)⁻¹)⁻¹ - (-(1 * v)⁻¹)⁻¹ - (-t) * (-((-t) * Y)⁻¹) = -(t * Y - Y⁻¹ + -v) := by
    field_simp
    ring
  have r_S : S (-v) = S 1 := S_of_pos S hS hu
  have hm1 : (-1 : ℂ) ^ m * (-1 : ℂ) ^ m = 1 := by
    rw [← mul_pow]; simp
  simp only [Phi, H3, brP]
  rw [r_abs1] at hb ⊢
  rw [r_E, r_g, r_br, Zi_neg, r_S, abs_of_neg ht, Complex.real_smul, Complex.real_smul]
  rw [abs_of_neg ht] at hb
  linear_combination ((Real.exp (-(2 * Real.pi * -t)) : ℂ) * S 1 *
      (Real.exp (-(Real.pi * ((Y ^ 2)⁻¹ + t ^ 2 * Y ^ 2 + (-v) ^ 2))) : ℂ) * g (-v / Y) * Zi m (t * Y - Y⁻¹ + -v)) * hb
    - ((((-t * Y ^ 2)⁻¹ : ℝ) : ℂ) * ((((1 * v ^ 2)⁻¹ : ℝ)) : ℂ) * (((-t : ℝ)) : ℂ) ^ (A₁ - γ - 1) *
        (((((-t) * Y)⁻¹ : ℝ)) : ℂ) ^ (-γ - 2) * (((-(1 * v)⁻¹ : ℝ)) : ℂ) ^ ((n : ℂ) - w - β - 3) *
        (Real.exp (-(2 * Real.pi * -t)) : ℂ) * S 1 *
        (Real.exp (-(Real.pi * ((Y ^ 2)⁻¹ + t ^ 2 * Y ^ 2 + (-v) ^ 2))) : ℂ) * g (-v / Y) * Zi m (t * Y - Y⁻¹ + -v)) * hm1

end K9F2
end

noncomputable section
namespace K9F2
open Real

local notation "μ₊" => Measure.restrict (volume : Measure ℝ) (Ioi (0:ℝ))
local notation "μ₋" => Measure.restrict (volume : Measure ℝ) (Iio (0:ℝ))

theorem ae3_neg : ∀ᵐ q : ℝ × ℝ × ℝ ∂((μ₋).prod ((μ₊).prod (μ₋))), q.1 < 0 ∧ 0 < q.2.1 ∧ q.2.2 < 0 := by
  have h1 : ∀ᵐ t : ℝ ∂(μ₋), t < 0 := ae_restrict_mem measurableSet_Iio
  have h2 : ∀ᵐ y : ℝ ∂(μ₊), 0 < y := ae_restrict_mem measurableSet_Ioi
  have hB : ∀ᵐ p : ℝ × ℝ ∂((μ₊).prod (μ₋)), 0 < p.1 ∧ p.2 < 0 :=
    ((Measure.quasiMeasurePreserving_fst).ae h2).and ((Measure.quasiMeasurePreserving_snd).ae h1)
  exact ((Measure.quasiMeasurePreserving_fst).ae h1).and ((Measure.quasiMeasurePreserving_snd).ae hB)

theorem vol_eq_add : (volume : Measure ℝ) = (μ₋) + (μ₊) := by
  have hd : Disjoint (Iio (0:ℝ)) (Ioi 0) := Set.disjoint_left.2 fun x (h1 : x < 0) (h2 : 0 < x) => lt_irrefl x (h1.trans h2)
  rw [← Measure.restrict_union hd measurableSet_Ioi]
  refine (Measure.restrict_eq_self_of_ae_mem ?_).symm
  have : ({0}ᶜ : Set ℝ) ∈ ae (volume : Measure ℝ) := compl_mem_ae_iff.2 (measure_singleton 0)
  filter_upwards [this] with x hx
  rcases lt_or_gt_of_ne (show x ≠ 0 by simpa using hx) with h | h
  · exact Or.inl h
  · exact Or.inr h

end K9F2
end

open K9F2 in
theorem solution
    (A₁ β γ w : ℂ) (m n : ℕ) (S : ℝ → ℂ) (hS : ∀ c : ℝ, 0 < c → ∀ y : ℝ, S (y / c) = S y)
    (hSm : Measurable S) (g : ℝ → ℂ) (hg : Measurable g)
    (hminus : Integrable (fun x : ℝ × ℝ × ℝ × ℝ =>
        ((x.1 : ℝ) : ℂ) ^ (A₁ - γ - 1) * (Real.exp (-(2 * Real.pi * x.1)) : ℂ) *
          ((|x.2.1| : ℝ) : ℂ) ^ (-γ - 2) * ((x.2.2.1 : ℝ) : ℂ) ^ ((n : ℂ) - w - β - 3) *
          (Real.exp (-(Real.pi * ((x.2.1 ^ 2)⁻¹ + x.1 ^ 2 * x.2.1 ^ 2 + (x.2.2.1 ^ 2)⁻¹))) : ℂ) *
          (fun v : ℝ => g (-v)) (x.1 * |x.2.1| / x.2.2.1) *
          ((((x.2.1⁻¹ - x.2.2.1⁻¹ + x.1 * x.2.1 : ℝ) : ℂ) + Complex.I * (x.2.2.2 : ℂ)) ^ m *
            (Real.exp (-(Real.pi * x.2.2.2 ^ 2)) : ℂ)))
        ((volume.restrict (Ioi (0 : ℝ))).prod ((volume.restrict (Iio (0 : ℝ))).prod
          ((volume.restrict (Ioi (0 : ℝ))).prod volume))))
    (hplus : Integrable (fun x : ℝ × ℝ × ℝ × ℝ =>
        ((x.1 : ℝ) : ℂ) ^ (A₁ - γ - 1) * (Real.exp (-(2 * Real.pi * x.1)) : ℂ) *
          ((|x.2.1| : ℝ) : ℂ) ^ (-γ - 2) * ((x.2.2.1 : ℝ) : ℂ) ^ ((n : ℂ) - w - β - 3) *
          (Real.exp (-(Real.pi * ((x.2.1 ^ 2)⁻¹ + x.1 ^ 2 * x.2.1 ^ 2 + (x.2.2.1 ^ 2)⁻¹))) : ℂ) *
          g (x.1 * |x.2.1| / x.2.2.1) *
          ((((-x.2.1⁻¹ - x.2.2.1⁻¹ - x.1 * x.2.1 : ℝ) : ℂ) + Complex.I * (x.2.2.2 : ℂ)) ^ m *
            (Real.exp (-(Real.pi * x.2.2.2 ^ 2)) : ℂ)))
        ((volume.restrict (Ioi (0 : ℝ))).prod ((volume.restrict (Iio (0 : ℝ))).prod
          ((volume.restrict (Ioi (0 : ℝ))).prod volume)))) :
    Integrable (fun q : ℝ × ℝ × ℝ =>
        ((|q.2.2| : ℝ) : ℂ) ^ (w + 1) *
          (((|q.1| : ℝ) : ℂ) ^ A₁ * (Real.exp (-(2 * Real.pi * |q.1|)) : ℂ) *
            (((q.2.2⁻¹ : ℝ) : ℂ) ^ n * S q.2.2 * ((|q.2.2| : ℝ) : ℂ) ^ β * ((q.2.1 : ℝ) : ℂ) ^ γ) *
            (Real.exp (-(Real.pi * ((q.2.1 ^ 2)⁻¹ + q.1 ^ 2 * q.2.1 ^ 2 + q.2.2 ^ 2))) : ℂ) *
            g (q.2.2 / q.2.1) *
            (∫ z : ℝ, (((q.1 * q.2.1 - q.2.1⁻¹ + q.2.2 : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
              (Real.exp (-(Real.pi * z ^ 2)) : ℂ))))
        ((volume.restrict (Iio (0 : ℝ))).prod ((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure ℝ))) ∧
    Integrable (fun q : ℝ × ℝ × ℝ =>
        ((|q.2.1| : ℝ) : ℂ) ^ (w + 1) *
          (((|q.1| : ℝ) : ℂ) ^ A₁ * (Real.exp (-(2 * Real.pi * |q.1|)) : ℂ) *
            (((q.2.1⁻¹ : ℝ) : ℂ) ^ n * S q.2.1 * ((|q.2.1| : ℝ) : ℂ) ^ β * ((q.2.2 : ℝ) : ℂ) ^ γ) *
            (Real.exp (-(Real.pi * ((q.2.2 ^ 2)⁻¹ + q.1 ^ 2 * q.2.2 ^ 2 + q.2.1 ^ 2))) : ℂ) *
            g (q.2.1 / q.2.2) *
            (∫ z : ℝ, (((q.1 * q.2.2 - q.2.2⁻¹ + q.2.1 : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
              (Real.exp (-(Real.pi * z ^ 2)) : ℂ))))
        ((volume.restrict (Iio (0 : ℝ))).prod ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ))))) := by

  have Im : Integrable (K9F2.H3 (A₁ - γ - 1) (-γ - 2) ((n : ℂ) - w - β - 3) m (fun v : ℝ => g (-v)) K9F2.brM)
      ((volume.restrict (Ioi (0:ℝ))).prod ((volume.restrict (Iio (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))))) := by
    have h := K9F2i.integrable_integral_inner4 (volume.restrict (Ioi (0:ℝ))) (volume.restrict (Iio (0:ℝ)))
      (volume.restrict (Ioi (0:ℝ))) (volume : Measure ℝ) _ hminus
    refine h.congr (ae_of_all _ fun p => ?_)
    simp only [K9F2.H3, K9F2.Zi, K9F2.brM]
    rw [← integral_const_mul]
  have Ip : Integrable (K9F2.H3 (A₁ - γ - 1) (-γ - 2) ((n : ℂ) - w - β - 3) m g K9F2.brP)
      ((volume.restrict (Ioi (0:ℝ))).prod ((volume.restrict (Iio (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))))) := by
    have h := K9F2i.integrable_integral_inner4 (volume.restrict (Ioi (0:ℝ))) (volume.restrict (Iio (0:ℝ)))
      (volume.restrict (Ioi (0:ℝ))) (volume : Measure ℝ) _ hplus
    refine h.congr (ae_of_all _ fun p => ?_)
    simp only [K9F2.H3, K9F2.Zi, K9F2.brP]
    rw [← integral_const_mul]

  have Tm := K9F2.transport _ (K9F2.measurable_H3 _ _ _ m _ (hg.comp measurable_neg) _ K9F2.measurable_brM) Im
  have Tp := K9F2.transport _ (K9F2.measurable_H3 _ _ _ m _ hg _ K9F2.measurable_brP) Ip

  have Pm : Integrable (K9F2.Phi A₁ β γ w m n S g)
      ((volume.restrict (Iio (0:ℝ))).prod ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Iio (0:ℝ))))) := by
    refine (Tm.const_mul ((-1 : ℂ) ^ n * S (-1))).congr ?_
    filter_upwards [K9F2.ae3_neg] with q hq
    obtain ⟨t, Y, u⟩ := q
    exact (K9F2.pointwise_minus A₁ β γ w m n S g hS t Y u hq.1 hq.2.1 hq.2.2).symm
  have Pp' : Integrable (fun q : ℝ × ℝ × ℝ => K9F2.Phi A₁ β γ w m n S g (q.1, q.2.1, -q.2.2))
      ((volume.restrict (Iio (0:ℝ))).prod ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Iio (0:ℝ))))) := by
    refine (Tp.const_mul ((-1 : ℂ) ^ m * S 1)).congr ?_
    filter_upwards [K9F2.ae3_neg] with q hq
    obtain ⟨t, Y, v⟩ := q
    exact (K9F2.pointwise_plus A₁ β γ w m n S g hS t Y v hq.1 hq.2.1 hq.2.2).symm
  have Pp : Integrable (K9F2.Phi A₁ β γ w m n S g)
      ((volume.restrict (Iio (0:ℝ))).prod ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))))) := by
    have hρ : MeasurePreserving (fun q : ℝ × ℝ × ℝ => (q.1, q.2.1, -q.2.2))
        ((volume.restrict (Iio (0:ℝ))).prod ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))))
        ((volume.restrict (Iio (0:ℝ))).prod ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Iio (0:ℝ))))) :=
      (MeasurePreserving.id _).prod ((MeasurePreserving.id _).prod K9F2.measurePreserving_neg_Ioi_Iio)
    have h := (hρ.integrable_comp Pp'.aestronglyMeasurable).mpr Pp'
    refine h.congr (ae_of_all _ fun q => ?_)
    simp only [Function.comp, neg_neg]

  have T1 : Integrable (K9F2.Phi A₁ β γ w m n S g)
      ((volume.restrict (Iio (0:ℝ))).prod ((volume.restrict (Ioi (0:ℝ))).prod (volume : Measure ℝ))) := by
    have e : ((volume.restrict (Iio (0:ℝ))).prod ((volume.restrict (Ioi (0:ℝ))).prod (volume : Measure ℝ))) =
        (volume.restrict (Iio (0:ℝ))).prod ((volume.restrict (Ioi (0:ℝ))).prod
          (volume.restrict (Iio (0:ℝ)) + volume.restrict (Ioi (0:ℝ)))) := by
      rw [← K9F2.vol_eq_add]
    rw [e, Measure.prod_add, Measure.prod_add, integrable_add_measure]
    exact ⟨Pm, Pp⟩

  have T2 : Integrable (fun q : ℝ × ℝ × ℝ => K9F2.Phi A₁ β γ w m n S g (q.1, q.2.2, q.2.1))
      ((volume.restrict (Iio (0:ℝ))).prod ((volume : Measure ℝ).prod (volume.restrict (Ioi (0:ℝ))))) := by
    have hσ : MeasurePreserving (fun q : ℝ × ℝ × ℝ => (q.1, q.2.2, q.2.1))
        ((volume.restrict (Iio (0:ℝ))).prod ((volume : Measure ℝ).prod (volume.restrict (Ioi (0:ℝ)))))
        ((volume.restrict (Iio (0:ℝ))).prod ((volume.restrict (Ioi (0:ℝ))).prod (volume : Measure ℝ))) :=
      (MeasurePreserving.id _).prod (Measure.measurePreserving_swap)
    exact (hσ.integrable_comp T1.aestronglyMeasurable).mpr T1
  exact ⟨by exact T1, by simpa only [K9F2.Phi, K9F2.Zi] using T2⟩

#print axioms solution

end S_LanglandsTunnell_integrable_dualFibres_of_integrable_oneSided
end P2MW
export P2MW.S_LanglandsTunnell_integrable_dualFibres_of_integrable_oneSided (solution)
