-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_localZeta31_fe_of_forall_localZeta31_fe
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/4c639542-699c-5ce4-97bb-bf8181a06817

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_localZeta31_fe_of_forall_localZeta31_fe

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal MeasureTheory
open scoped NNReal ENNReal Matrix

noncomputable section

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

namespace LTPkg31Cyclic

open LanglandsTunnell.CubicInduction

section Algebra

variable {A : Type*} [CommRing A]

theorem transposeInv3_coe (g : GL (Fin 3) A) :
    ((transposeInv3 g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      (((g⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ := rfl

theorem transposeInv3_mul (g h : GL (Fin 3) A) :
    transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  refine Units.ext ?_
  rw [Units.val_mul, transposeInv3_coe, transposeInv3_coe, transposeInv3_coe, _root_.mul_inv_rev, Units.val_mul,
    Matrix.transpose_mul]

theorem transposeInv3_transposeInv3 (g : GL (Fin 3) A) : transposeInv3 (transposeInv3 g) = g := by
  refine Units.ext ?_
  show ((((g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ)ᵀ = _
  exact Matrix.transpose_transpose _

theorem dualWhittakerFn3_translate {R : Type*} (W : GL (Fin 3) A → R) (h : GL (Fin 3) A) :
    dualWhittakerFn3 (fun x => W (x * h)) = fun X => dualWhittakerFn3 W (X * transposeInv3 h) := by
  funext X
  rw [dualWhittakerFn3_apply, dualWhittakerFn3_apply, transposeInv3_mul, transposeInv3_transposeInv3, mul_assoc]

theorem dualWhittakerFn3_add {R : Type*} [Add R] (W₁ W₂ : GL (Fin 3) A → R) :
    dualWhittakerFn3 (W₁ + W₂) = dualWhittakerFn3 W₁ + dualWhittakerFn3 W₂ := by
  funext X; rfl

theorem dualWhittakerFn3_smul {R : Type*} [Mul R] (c : R) (W : GL (Fin 3) A → R) :
    dualWhittakerFn3 (c • W) = c • dualWhittakerFn3 W := by
  funext X; rfl

theorem dualWhittakerFn3_zero {R : Type*} [Zero R] :
    dualWhittakerFn3 (0 : GL (Fin 3) A → R) = 0 := by
  funext X; rfl

end Algebra

variable (v : HeightOneSpectrum (𝓞 ℚ))

section Measures

theorem measurableEmbedding_val : MeasurableEmbedding (Units.val : (v.adicCompletion ℚ)ˣ → v.adicCompletion ℚ) where
  injective := Units.val_injective
  measurable := comap_measurable Units.val
  measurableSet_image' := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
    have : Units.val '' (Units.val ⁻¹' t) = t ∩ {x : v.adicCompletion ℚ | x ≠ 0} := by
      ext x
      constructor
      · rintro ⟨u, hu, rfl⟩; exact ⟨hu, u.ne_zero⟩
      · rintro ⟨hx, hx0⟩; exact ⟨Units.mk0 x hx0, hx, rfl⟩
    rw [this]
    exact ht.inter (measurableSet_singleton (0 : v.adicCompletion ℚ)).compl

theorem sFinite_comap_val (ρ : Measure (v.adicCompletion ℚ)) [SFinite ρ] :
    SFinite (Measure.comap Units.val ρ : Measure (v.adicCompletion ℚ)ˣ) := by
  have hme := measurableEmbedding_val v
  refine ⟨⟨fun n => Measure.comap Units.val (sfiniteSeq ρ n), fun n => ⟨?_⟩, ?_⟩⟩
  · rw [hme.comap_apply]
    exact measure_lt_top _ _
  · ext s hs
    rw [Measure.sum_apply _ hs, hme.comap_apply]
    simp_rw [hme.comap_apply]
    rw [← Measure.sum_apply _ (hme.measurableSet_image' hs), sum_sfiniteSeq]

theorem isAddHaarMeasure_selfDualHaarAt : (selfDualHaarAt ℚ v).IsAddHaarMeasure := by
  set c : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0) ^
    (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ v) : ℝ) / 2) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.rpow_pos (pos_iff_ne_zero.mpr (HeightOneSpectrum.absNorm_ne_zero v))).ne'
  have hdef : selfDualHaarAt ℚ v = c • Measure.addHaarMeasure (integersPositiveCompacts ℚ v) := rfl
  have h : selfDualHaarAt ℚ v = (c : ℝ≥0∞) • Measure.addHaarMeasure (integersPositiveCompacts ℚ v) := by
    rw [hdef]
    ext s _
    rw [Measure.coe_nnreal_smul_apply, Measure.smul_apply, smul_eq_mul]
  rw [h]
  exact Measure.IsAddHaarMeasure.smul _ (ENNReal.coe_ne_zero.mpr hc0) ENNReal.coe_ne_top

theorem sFinite_selfDual : SFinite (selfDualHaarAt ℚ v) := by
  haveI := isAddHaarMeasure_selfDualHaarAt v
  infer_instance

theorem sFinite_mulSelfDual :
    SFinite (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)) : Measure (v.adicCompletion ℚ)ˣ) := by
  haveI := isAddHaarMeasure_selfDualHaarAt v
  haveI : SFinite (mulMeasure (selfDualHaarAt ℚ v)) := by unfold mulMeasure; infer_instance
  exact sFinite_comap_val v _

end Measures

theorem modulusC_cpow_ne_zero (a : (v.adicCompletion ℚ)ˣ) (z : ℂ) : ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ z ≠ 0 := by
  intro h
  rw [Complex.cpow_eq_zero_iff] at h
  have hpos : (0 : ℝ) < (modulus (a : v.adicCompletion ℚ) : ℝ) := by exact_mod_cast modulus_pos a.ne_zero
  exact hpos.ne' (by exact_mod_cast h.1)

theorem charC_ne_zero (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (a : (v.adicCompletion ℚ)ˣ) : ((χ a : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _

section Linearity

variable {v}

theorem localZeta30_add (μ : Measure (v.adicCompletion ℚ)ˣ) (W₁ W₂ : LocalGL3 v → ℂ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (g : LocalGL3 v)
    (h₁ : Integrable (fun a : (v.adicCompletion ℚ)ˣ => W₁ (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) *
        ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) μ)
    (h₂ : Integrable (fun a : (v.adicCompletion ℚ)ˣ => W₂ (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) *
        ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) μ) :
    localZeta30 v μ (W₁ + W₂) χ s g = localZeta30 v μ W₁ χ s g + localZeta30 v μ W₂ χ s g := by
  unfold localZeta30
  rw [← integral_add h₁ h₂]
  refine integral_congr_ae (ae_of_all _ fun a => ?_)
  simp only [Pi.add_apply]
  ring

theorem localZeta30_smul (μ : Measure (v.adicCompletion ℚ)ˣ) (c : ℂ) (W : LocalGL3 v → ℂ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (g : LocalGL3 v) :
    localZeta30 v μ (c • W) χ s g = c * localZeta30 v μ W χ s g := by
  unfold localZeta30
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun a => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem localZeta30_zero (μ : Measure (v.adicCompletion ℚ)ˣ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (g : LocalGL3 v) :
    localZeta30 v μ (0 : LocalGL3 v → ℂ) χ s g = 0 := by
  unfold localZeta30
  simp

theorem localZeta30_translate (μ : Measure (v.adicCompletion ℚ)ˣ) (W : LocalGL3 v → ℂ) (h : LocalGL3 v) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (g : LocalGL3 v) :
    localZeta30 v μ (fun x => W (x * h)) χ s g = localZeta30 v μ W χ s (g * h) := by
  unfold localZeta30
  simp only [mul_assoc]

theorem conv30_add (μ : Measure (v.adicCompletion ℚ)ˣ) {W₁ W₂ : LocalGL3 v → ℂ} {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ} {g : LocalGL3 v} {σ₁ σ₂ : ℝ}
    (h₁ : IsLocalZeta30ConvergentAbove v μ W₁ χ g σ₁) (h₂ : IsLocalZeta30ConvergentAbove v μ W₂ χ g σ₂) :
    IsLocalZeta30ConvergentAbove v μ (W₁ + W₂) χ g (max σ₁ σ₂) := by
  intro s hs
  have e : (fun a : (v.adicCompletion ℚ)ˣ => (W₁ + W₂) (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) *
        ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) =
      (fun a : (v.adicCompletion ℚ)ˣ => W₁ (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) +
      (fun a : (v.adicCompletion ℚ)ˣ => W₂ (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) := by
    funext a
    simp only [Pi.add_apply]
    ring
  rw [e]
  exact (h₁ s (lt_of_le_of_lt (le_max_left _ _) hs)).add (h₂ s (lt_of_le_of_lt (le_max_right _ _) hs))

theorem conv30_smul (μ : Measure (v.adicCompletion ℚ)ˣ) (c : ℂ) {W : LocalGL3 v → ℂ} {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ} {g : LocalGL3 v} {σ : ℝ}
    (h : IsLocalZeta30ConvergentAbove v μ W χ g σ) :
    IsLocalZeta30ConvergentAbove v μ (c • W) χ g σ := by
  intro s hs
  have e : (fun a : (v.adicCompletion ℚ)ˣ => (c • W) (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) *
        ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) =
      fun a : (v.adicCompletion ℚ)ˣ => c * (W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) := by
    funext a
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [e]
  exact (h s hs).const_mul c

theorem conv30_zero (μ : Measure (v.adicCompletion ℚ)ˣ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (g : LocalGL3 v) :
    IsLocalZeta30ConvergentAbove v μ (0 : LocalGL3 v → ℂ) χ g 0 := by
  intro s _
  simp only [Pi.zero_apply, zero_mul]
  exact integrable_zero _ _ _

theorem conv30_translate (μ : Measure (v.adicCompletion ℚ)ˣ) {W : LocalGL3 v → ℂ} (h : LocalGL3 v) {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ} {g : LocalGL3 v} {σ : ℝ}
    (hW : IsLocalZeta30ConvergentAbove v μ W χ (g * h) σ) :
    IsLocalZeta30ConvergentAbove v μ (fun x => W (x * h)) χ g σ := by
  intro s hs
  simpa only [mul_assoc] using hW s hs

theorem localZeta31_add (μ : Measure (v.adicCompletion ℚ)ˣ) (ν : Measure (v.adicCompletion ℚ)) [SFinite μ] [SFinite ν] (W₁ W₂ : LocalGL3 v → ℂ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (g : LocalGL3 v)
    (h₁ : Integrable (fun q : (v.adicCompletion ℚ)ˣ × (v.adicCompletion ℚ) => W₁ (iotaGL (diagUnitGL2 q.1) * lowerUnipotent21 q.2 * g) *
        ((χ q.1 : ℂˣ) : ℂ) * ((modulus (q.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) (μ.prod ν))
    (h₂ : Integrable (fun q : (v.adicCompletion ℚ)ˣ × (v.adicCompletion ℚ) => W₂ (iotaGL (diagUnitGL2 q.1) * lowerUnipotent21 q.2 * g) *
        ((χ q.1 : ℂˣ) : ℂ) * ((modulus (q.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) (μ.prod ν)) :
    localZeta31 v μ ν (W₁ + W₂) χ s g = localZeta31 v μ ν W₁ χ s g + localZeta31 v μ ν W₂ χ s g := by

  set c : (v.adicCompletion ℚ)ˣ → ℂ := fun a => ((χ a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) with hc
  have hc0 : ∀ a, c a ≠ 0 := fun a => mul_ne_zero (charC_ne_zero v χ a) (modulusC_cpow_ne_zero v a _)

  set F₁ : (v.adicCompletion ℚ)ˣ → (v.adicCompletion ℚ) → ℂ := fun a x => W₁ (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * g) with hF₁
  set F₂ : (v.adicCompletion ℚ)ˣ → (v.adicCompletion ℚ) → ℂ := fun a x => W₂ (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * g) with hF₂
  have h₁' : Integrable (fun q : (v.adicCompletion ℚ)ˣ × (v.adicCompletion ℚ) => F₁ q.1 q.2 * c q.1) (μ.prod ν) := by
    refine h₁.congr (ae_of_all _ fun q => ?_)
    simp only [hF₁, hc]; ring
  have h₂' : Integrable (fun q : (v.adicCompletion ℚ)ˣ × (v.adicCompletion ℚ) => F₂ q.1 q.2 * c q.1) (μ.prod ν) := by
    refine h₂.congr (ae_of_all _ fun q => ?_)
    simp only [hF₂, hc]; ring

  have hs₁ : ∀ᵐ a ∂μ, Integrable (fun x => F₁ a x) ν := by
    filter_upwards [h₁'.prod_right_ae] with a ha
    have := ha.mul_const (c a)⁻¹
    refine this.congr (ae_of_all _ fun x => ?_)
    show F₁ a x * c a * (c a)⁻¹ = F₁ a x
    rw [mul_assoc, mul_inv_cancel₀ (hc0 a), mul_one]
  have hs₂ : ∀ᵐ a ∂μ, Integrable (fun x => F₂ a x) ν := by
    filter_upwards [h₂'.prod_right_ae] with a ha
    have := ha.mul_const (c a)⁻¹
    refine this.congr (ae_of_all _ fun x => ?_)
    show F₂ a x * c a * (c a)⁻¹ = F₂ a x
    rw [mul_assoc, mul_inv_cancel₀ (hc0 a), mul_one]

  have hI₁ : Integrable (fun a => (∫ x, F₁ a x ∂ν) * c a) μ := by
    have := h₁'.integral_prod_left
    refine this.congr (ae_of_all _ fun a => ?_)
    show (∫ x, F₁ a x * c a ∂ν) = (∫ x, F₁ a x ∂ν) * c a
    exact integral_mul_const (c a) _
  have hI₂ : Integrable (fun a => (∫ x, F₂ a x ∂ν) * c a) μ := by
    have := h₂'.integral_prod_left
    refine this.congr (ae_of_all _ fun a => ?_)
    show (∫ x, F₂ a x * c a ∂ν) = (∫ x, F₂ a x ∂ν) * c a
    exact integral_mul_const (c a) _

  have e : localZeta31 v μ ν (W₁ + W₂) χ s g = ∫ a, (∫ x, F₁ a x + F₂ a x ∂ν) * c a ∂μ := by
    unfold localZeta31
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    show (∫ x, (W₁ + W₂) (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * g) ∂ν) * ((χ a : ℂˣ) : ℂ) *
        ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) = (∫ x, F₁ a x + F₂ a x ∂ν) * c a
    rw [hc, ← mul_assoc]
    rfl
  have e₁ : localZeta31 v μ ν W₁ χ s g = ∫ a, (∫ x, F₁ a x ∂ν) * c a ∂μ := by
    unfold localZeta31
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    show (∫ x, W₁ (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * g) ∂ν) * ((χ a : ℂˣ) : ℂ) *
        ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) = (∫ x, F₁ a x ∂ν) * c a
    rw [hc, ← mul_assoc]
  have e₂ : localZeta31 v μ ν W₂ χ s g = ∫ a, (∫ x, F₂ a x ∂ν) * c a ∂μ := by
    unfold localZeta31
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    show (∫ x, W₂ (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * g) ∂ν) * ((χ a : ℂˣ) : ℂ) *
        ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) = (∫ x, F₂ a x ∂ν) * c a
    rw [hc, ← mul_assoc]
  rw [e, e₁, e₂, ← integral_add hI₁ hI₂]
  refine integral_congr_ae ?_
  filter_upwards [hs₁, hs₂] with a ha₁ ha₂
  rw [integral_add ha₁ ha₂]
  ring

theorem localZeta31_smul (μ : Measure (v.adicCompletion ℚ)ˣ) (ν : Measure (v.adicCompletion ℚ)) (c : ℂ) (W : LocalGL3 v → ℂ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (g : LocalGL3 v) :
    localZeta31 v μ ν (c • W) χ s g = c * localZeta31 v μ ν W χ s g := by
  unfold localZeta31
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun a => ?_)
  have hin : (∫ x, (c • W) (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * g) ∂ν) =
      c * ∫ x, W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * g) ∂ν := by
    rw [← integral_const_mul]
    rfl
  show (∫ x, (c • W) (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * g) ∂ν) * ((χ a : ℂˣ) : ℂ) *
      ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) =
    c * ((∫ x, W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * g) ∂ν) * ((χ a : ℂˣ) : ℂ) *
      ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1))
  rw [hin]
  ring

theorem localZeta31_zero (μ : Measure (v.adicCompletion ℚ)ˣ) (ν : Measure (v.adicCompletion ℚ)) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (g : LocalGL3 v) :
    localZeta31 v μ ν (0 : LocalGL3 v → ℂ) χ s g = 0 := by
  unfold localZeta31
  simp

theorem localZeta31_translate (μ : Measure (v.adicCompletion ℚ)ˣ) (ν : Measure (v.adicCompletion ℚ)) (W : LocalGL3 v → ℂ) (h : LocalGL3 v) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (g : LocalGL3 v) :
    localZeta31 v μ ν (fun x => W (x * h)) χ s g = localZeta31 v μ ν W χ s (g * h) := by
  unfold localZeta31
  simp only [mul_assoc]

theorem conv31_add (μ : Measure (v.adicCompletion ℚ)ˣ) (ν : Measure (v.adicCompletion ℚ)) {W₁ W₂ : LocalGL3 v → ℂ} {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ} {g : LocalGL3 v} {σ₁ σ₂ : ℝ}
    (h₁ : IsLocalZeta31ConvergentAbove v μ ν W₁ χ g σ₁) (h₂ : IsLocalZeta31ConvergentAbove v μ ν W₂ χ g σ₂) :
    IsLocalZeta31ConvergentAbove v μ ν (W₁ + W₂) χ g (max σ₁ σ₂) := by
  intro s hs
  have e : (fun q : (v.adicCompletion ℚ)ˣ × (v.adicCompletion ℚ) => (W₁ + W₂) (iotaGL (diagUnitGL2 q.1) * lowerUnipotent21 q.2 * g) *
        ((χ q.1 : ℂˣ) : ℂ) * ((modulus (q.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) =
      (fun q : (v.adicCompletion ℚ)ˣ × (v.adicCompletion ℚ) => W₁ (iotaGL (diagUnitGL2 q.1) * lowerUnipotent21 q.2 * g) *
        ((χ q.1 : ℂˣ) : ℂ) * ((modulus (q.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) +
      (fun q : (v.adicCompletion ℚ)ˣ × (v.adicCompletion ℚ) => W₂ (iotaGL (diagUnitGL2 q.1) * lowerUnipotent21 q.2 * g) *
        ((χ q.1 : ℂˣ) : ℂ) * ((modulus (q.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) := by
    funext q
    simp only [Pi.add_apply]
    ring
  rw [e]
  exact (h₁ s (lt_of_le_of_lt (le_max_left _ _) hs)).add (h₂ s (lt_of_le_of_lt (le_max_right _ _) hs))

theorem conv31_smul (μ : Measure (v.adicCompletion ℚ)ˣ) (ν : Measure (v.adicCompletion ℚ)) (c : ℂ) {W : LocalGL3 v → ℂ} {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ} {g : LocalGL3 v} {σ : ℝ}
    (h : IsLocalZeta31ConvergentAbove v μ ν W χ g σ) :
    IsLocalZeta31ConvergentAbove v μ ν (c • W) χ g σ := by
  intro s hs
  have e : (fun q : (v.adicCompletion ℚ)ˣ × (v.adicCompletion ℚ) => (c • W) (iotaGL (diagUnitGL2 q.1) * lowerUnipotent21 q.2 * g) *
        ((χ q.1 : ℂˣ) : ℂ) * ((modulus (q.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) =
      fun q : (v.adicCompletion ℚ)ˣ × (v.adicCompletion ℚ) => c * (W (iotaGL (diagUnitGL2 q.1) * lowerUnipotent21 q.2 * g) *
        ((χ q.1 : ℂˣ) : ℂ) * ((modulus (q.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) := by
    funext q
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [e]
  exact (h s hs).const_mul c

theorem conv31_zero (μ : Measure (v.adicCompletion ℚ)ˣ) (ν : Measure (v.adicCompletion ℚ)) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (g : LocalGL3 v) :
    IsLocalZeta31ConvergentAbove v μ ν (0 : LocalGL3 v → ℂ) χ g 0 := by
  intro s _
  simp only [Pi.zero_apply, zero_mul]
  exact integrable_zero _ _ _

theorem conv31_translate (μ : Measure (v.adicCompletion ℚ)ˣ) (ν : Measure (v.adicCompletion ℚ)) {W : LocalGL3 v → ℂ} (h : LocalGL3 v) {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ} {g : LocalGL3 v} {σ : ℝ}
    (hW : IsLocalZeta31ConvergentAbove v μ ν W χ (g * h) σ) :
    IsLocalZeta31ConvergentAbove v μ ν (fun x => W (x * h)) χ g σ := by
  intro s hs
  simpa only [mul_assoc] using hW s hs

theorem localZetaDual31_translate (μ : Measure (v.adicCompletion ℚ)ˣ) (ν : Measure (v.adicCompletion ℚ)) (W : LocalGL3 v → ℂ) (h : LocalGL3 v) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (g : LocalGL3 v) :
    localZetaDual31 v μ ν (fun x => W (x * h)) χ s g = localZetaDual31 v μ ν W χ s (g * h) := by
  unfold localZetaDual31
  rw [dualWhittakerFn3_translate, localZeta31_translate, transposeInv3_mul, mul_assoc]

theorem localZetaDual31_smul (μ : Measure (v.adicCompletion ℚ)ˣ) (ν : Measure (v.adicCompletion ℚ)) (c : ℂ) (W : LocalGL3 v → ℂ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (g : LocalGL3 v) :
    localZetaDual31 v μ ν (c • W) χ s g = c * localZetaDual31 v μ ν W χ s g := by
  unfold localZetaDual31
  rw [dualWhittakerFn3_smul, localZeta31_smul]

theorem localZetaDual31_zero (μ : Measure (v.adicCompletion ℚ)ˣ) (ν : Measure (v.adicCompletion ℚ)) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (g : LocalGL3 v) :
    localZetaDual31 v μ ν (0 : LocalGL3 v → ℂ) χ s g = 0 := by
  unfold localZetaDual31
  rw [dualWhittakerFn3_zero, localZeta31_zero]

theorem localZetaDual31_add (μ : Measure (v.adicCompletion ℚ)ˣ) (ν : Measure (v.adicCompletion ℚ)) [SFinite μ] [SFinite ν] (W₁ W₂ : LocalGL3 v → ℂ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (g : LocalGL3 v)
    (h₁ : Integrable (fun q : (v.adicCompletion ℚ)ˣ × (v.adicCompletion ℚ) => dualWhittakerFn3 W₁ (iotaGL (diagUnitGL2 q.1) * lowerUnipotent21 q.2 *
        (weylPrime3 * transposeInv3 g)) * ((χ⁻¹ q.1 : ℂˣ) : ℂ) * ((modulus (q.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) (μ.prod ν))
    (h₂ : Integrable (fun q : (v.adicCompletion ℚ)ˣ × (v.adicCompletion ℚ) => dualWhittakerFn3 W₂ (iotaGL (diagUnitGL2 q.1) * lowerUnipotent21 q.2 *
        (weylPrime3 * transposeInv3 g)) * ((χ⁻¹ q.1 : ℂˣ) : ℂ) * ((modulus (q.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) (μ.prod ν)) :
    localZetaDual31 v μ ν (W₁ + W₂) χ s g = localZetaDual31 v μ ν W₁ χ s g + localZetaDual31 v μ ν W₂ χ s g := by
  unfold localZetaDual31
  rw [dualWhittakerFn3_add]
  exact localZeta31_add μ ν _ _ _ _ _ h₁ h₂

end Linearity

theorem qpow_shift {q : ℂ} (hq : q ≠ 0) {n N : ℤ} (h : n ≤ N) (s : ℂ) :
    q ^ ((n : ℂ) * s) = q ^ ((N : ℂ) * s) * (q ^ (-s)) ^ (N - n).toNat := by
  rw [← Complex.cpow_nat_mul, ← Complex.cpow_add _ _ hq]
  congr 1
  have h1 : (((N - n).toNat : ℕ) : ℂ) = (N : ℂ) - (n : ℂ) := by
    have : (((N - n).toNat : ℕ) : ℤ) = N - n := Int.toNat_of_nonneg (sub_nonneg.mpr h)
    exact_mod_cast this
  rw [h1]
  ring

section Package

variable {v}

def Pkg (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (C : ℂ) (k : ℤ) (W : LocalGL3 v → ℂ) (g : LocalGL3 v) : Prop :=
  ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
    IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
      W η g σ₀ ∧
    (∀ s : ℂ, σ₀ < s.re →
      localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W η s g *
        Q₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
      Q₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
    IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
      (dualWhittakerFn3 W) η⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
    (∀ s : ℂ, σ₁ < (1 - s).re →
      localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
        W η (1 - s) g * Q₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
      Q₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((n : ℂ) * s) *
        (C * (Ideal.absNorm v.asIdeal : ℂ) ^ ((k : ℂ) * s)))

variable (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (C : ℂ) (k : ℤ)

local notation "μv" => (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)) : Measure (v.adicCompletion ℚ)ˣ)
local notation "νv" => (selfDualHaarAt ℚ v)

theorem pkg_translate {W : LocalGL3 v → ℂ} (h g : LocalGL3 v) (hW : Pkg η C k W (g * h)) :
    Pkg η C k (fun x => W (x * h)) g := by
  obtain ⟨Q₁, Q₂, n, σ₀, σ₁, hQ₂, hc0, he0, hc1, he1⟩ := hW
  refine ⟨Q₁, Q₂, n, σ₀, σ₁, hQ₂, conv30_translate _ h hc0, ?_, ?_, ?_⟩
  · intro s hs
    rw [localZeta30_translate]
    exact he0 s hs
  · rw [dualWhittakerFn3_translate]
    refine conv31_translate μv νv (transposeInv3 h) ?_
    rwa [mul_assoc, ← transposeInv3_mul]
  · intro s hs
    rw [localZetaDual31_translate]
    exact he1 s hs

theorem pkg_zero (g : LocalGL3 v) : Pkg η C k (0 : LocalGL3 v → ℂ) g := by
  refine ⟨0, 1, 0, 0, 0, one_ne_zero, conv30_zero μv η g, ?_, ?_, ?_⟩
  · intro s _
    rw [localZeta30_zero]
    simp
  · rw [dualWhittakerFn3_zero]
    exact conv31_zero μv νv η⁻¹ _
  · intro s _
    rw [localZetaDual31_zero]
    simp

theorem pkg_smul (c : ℂ) {W : LocalGL3 v → ℂ} (g : LocalGL3 v) (hW : Pkg η C k W g) : Pkg η C k (c • W) g := by
  obtain ⟨Q₁, Q₂, n, σ₀, σ₁, hQ₂, hc0, he0, hc1, he1⟩ := hW
  refine ⟨Polynomial.C c * Q₁, Q₂, n, σ₀, σ₁, hQ₂, conv30_smul μv c hc0, ?_, ?_, ?_⟩
  · intro s hs
    rw [localZeta30_smul, mul_assoc, he0 s hs, Polynomial.eval_mul, Polynomial.eval_C]
    ring
  · rw [dualWhittakerFn3_smul]
    exact conv31_smul μv νv c hc1
  · intro s hs
    rw [localZetaDual31_smul, mul_assoc, he1 s hs, Polynomial.eval_mul, Polynomial.eval_C]
    ring

theorem pkg_add {W₁ W₂ : LocalGL3 v → ℂ} (g : LocalGL3 v) (h₁ : Pkg η C k W₁ g) (h₂ : Pkg η C k W₂ g) :
    Pkg η C k (W₁ + W₂) g := by
  haveI : SFinite μv := sFinite_mulSelfDual v
  haveI : SFinite νv := sFinite_selfDual v
  obtain ⟨Q₁, Q₂, n, σ₀, σ₁, hQ₂, hc0, he0, hc1, he1⟩ := h₁
  obtain ⟨Q₁', Q₂', n', σ₀', σ₁', hQ₂', hc0', he0', hc1', he1'⟩ := h₂
  set q : ℂ := (Ideal.absNorm v.asIdeal : ℂ) with hqdef
  have hq : q ≠ 0 := by
    rw [hqdef]
    exact_mod_cast HeightOneSpectrum.absNorm_ne_zero v
  set N : ℤ := max n n' with hN
  set m : ℕ := (N - n).toNat with hm
  set m' : ℕ := (N - n').toNat with hm'
  refine ⟨Q₁ * Q₂' * Polynomial.X ^ m + Q₁' * Q₂ * Polynomial.X ^ m', Q₂ * Q₂', N, max σ₀ σ₀', max σ₁ σ₁',
    mul_ne_zero hQ₂ hQ₂', conv30_add μv hc0 hc0', ?_, ?_, ?_⟩
  · intro s hs
    have hs₁ : σ₀ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have hs₂ : σ₀' < s.re := lt_of_le_of_lt (le_max_right _ _) hs
    have E₁ := he0 s hs₁
    have E₂ := he0' s hs₂
    rw [qpow_shift hq (le_max_left n n' : n ≤ N) s] at E₁
    rw [qpow_shift hq (le_max_right n n' : n' ≤ N) s] at E₂
    rw [localZeta30_add μv W₁ W₂ η s g (hc0 s hs₁) (hc0' s hs₂)]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    linear_combination (Polynomial.eval (q ^ (-s)) Q₂') * E₁ + (Polynomial.eval (q ^ (-s)) Q₂) * E₂
  · rw [dualWhittakerFn3_add]
    exact conv31_add μv νv hc1 hc1'
  · intro s hs
    have hs₁ : σ₁ < (1 - s).re := lt_of_le_of_lt (le_max_left _ _) hs
    have hs₂ : σ₁' < (1 - s).re := lt_of_le_of_lt (le_max_right _ _) hs
    have E₁ := he1 s hs₁
    have E₂ := he1' s hs₂
    rw [qpow_shift hq (le_max_left n n' : n ≤ N) s] at E₁
    rw [qpow_shift hq (le_max_right n n' : n' ≤ N) s] at E₂
    rw [localZetaDual31_add μv νv W₁ W₂ η (1 - s) g (hc1 (1 - s) hs₁) (hc1' (1 - s) hs₂)]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    linear_combination (Polynomial.eval (q ^ (-s)) Q₂') * E₁ + (Polynomial.eval (q ^ (-s)) Q₂) * E₂

theorem pkg_of_mem_gl3CyclicSubspace {W₀ : LocalGL3 v → ℂ} (h₀ : ∀ g, Pkg η C k W₀ g)
    {W : LocalGL3 v → ℂ} (hW : W ∈ gl3CyclicSubspace W₀) : ∀ g, Pkg η C k W g := by
  refine Submodule.span_induction (p := fun f _ => ∀ g, Pkg η C k f g) ?_ ?_ ?_ ?_ hW
  · rintro _ ⟨h, rfl⟩ g
    exact pkg_translate η C k h g (h₀ (g * h))
  · exact pkg_zero η C k
  · intro f₁ f₂ _ _ h₁ h₂ g
    exact pkg_add η C k g (h₁ g) (h₂ g)
  · intro c f _ h g
    exact pkg_smul η C k c g (h g)

end Package

end LTPkg31Cyclic

open LanglandsTunnell.CubicInduction LTPkg31Cyclic

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (W₃base : LocalGL3 p → ℂ)
    (η : (p.adicCompletion ℚ)ˣ →* ℂˣ) (C : ℂ) (k : ℤ)
    (h31 : ∀ g : LocalGL3 p,
        letI := localBorel ℚ p
        ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
          IsLocalZeta30ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
            W₃base η g σ₀ ∧
          (∀ s : ℂ, σ₀ < s.re →
            localZeta30 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) W₃base η s g *
              Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
          IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p) (dualWhittakerFn3 W₃base) η⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
          (∀ s : ℂ, σ₁ < (1 - s).re →
            localZetaDual31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
              W₃base η (1 - s) g * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s) *
              (C * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k : ℂ) * s)))) :
    ∀ W₃ ∈ gl3CyclicSubspace W₃base, ∀ g : LocalGL3 p,
        letI := localBorel ℚ p
        ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
          IsLocalZeta30ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
            W₃ η g σ₀ ∧
          (∀ s : ℂ, σ₀ < s.re →
            localZeta30 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) W₃ η s g *
              Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
          IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p) (dualWhittakerFn3 W₃) η⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
          (∀ s : ℂ, σ₁ < (1 - s).re →
            localZetaDual31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
              W₃ η (1 - s) g * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s) *
              (C * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k : ℂ) * s))) := by
  intro W₃ hW₃ g
  exact pkg_of_mem_gl3CyclicSubspace η C k h31 hW₃ g

end
end S_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_localZeta31_fe_of_forall_localZeta31_fe
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_localZeta31_fe_of_forall_localZeta31_fe (solution)
