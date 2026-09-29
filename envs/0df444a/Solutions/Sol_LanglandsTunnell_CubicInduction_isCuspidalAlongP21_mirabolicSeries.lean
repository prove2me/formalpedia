-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.isCuspidalAlongP21_mirabolicSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/613d6b6f-7a5d-5ff0-8e15-adbff89df2f9

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_NumberField_IdeleProductMeasure
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_isCuspidalAlongP21_mirabolicSeries

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicHaar AutomorphicForm Matrix MeasureTheory
open scoped NNReal ENNReal Pointwise ProbabilityTheory

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel

local notation "μbox" =>
  ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ)

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "IsGL3PsiWhittakerFn IsCuspidalAlongP21 mirabolicTranslate AdelicGL upperUnipotent3 radicalP21 embedMat2 iotaGL coe_iotaGL MirabolicIndex mirabolicRep"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section Transport

variable {A : Type*} [CommRing A]

private theorem iotaGL_mul_upperUnipotent3_zero (h : GL (Fin 2) A) (y z : A) :
    iotaGL h * upperUnipotent3 0 y z =
      upperUnipotent3 0 ((h : Matrix (Fin 2) (Fin 2) A) 1 0 * z + (h : Matrix (Fin 2) (Fin 2) A) 1 1 * y)
        ((h : Matrix (Fin 2) (Fin 2) A) 0 0 * z + (h : Matrix (Fin 2) (Fin 2) A) 0 1 * y) * iotaGL h := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Units.val_mul, coe_iotaGL, embedMat2, Matrix.mul_apply, Fin.sum_univ_three]

end Transport

section YStep

private theorem setIntegral_adelicBox_comp_add_right {f : AdeleRing (𝓞 ℚ) ℚ → ℂ}
    (hf : ∀ (α : ℚ) (y : AdeleRing (𝓞 ℚ) ℚ), f (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α + y) = f y)
    (s : AdeleRing (𝓞 ℚ) ℚ) :
    ∫ y in AdelicBox.adelicBox ℚ, f (y + s) ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) =
      ∫ y in AdelicBox.adelicBox ℚ, f y ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) := by
  haveI := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ
  set μ : Measure (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ with hμ

  have hf' : ∀ (γ : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (y : AdeleRing (𝓞 ℚ) ℚ), f (γ +ᵥ y) = f y := by
    intro γ y
    obtain ⟨α, hα⟩ := RingHom.mem_range.mp γ.2
    show f ((γ : AdeleRing (𝓞 ℚ) ℚ) + y) = f y
    rw [← hα]
    exact hf α y
  have hbox := AdelicBox.isAddFundamentalDomain_adelicBox ℚ μ

  haveI : Countable (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) := by
    refine Function.Surjective.countable (f := fun α : ℚ =>
      (⟨algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α, ⟨α, rfl⟩⟩ : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ)) ?_
    rintro ⟨x, hx⟩
    obtain ⟨α, rfl⟩ := RingHom.mem_range.mp hx
    exact ⟨α, rfl⟩

  have hbox' : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (s +ᵥ AdelicBox.adelicBox ℚ) μ :=
    hbox.vadd_of_comm s

  have hpre : (fun y : AdeleRing (𝓞 ℚ) ℚ => y + s) ⁻¹' (s +ᵥ AdelicBox.adelicBox ℚ) = AdelicBox.adelicBox ℚ := by
    ext y
    simp only [Set.mem_preimage, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    rw [show -s + (y + s) = y by abel]
  have hshift := (measurePreserving_add_right μ s).setIntegral_preimage_emb
    (MeasurableEquiv.addRight s).measurableEmbedding f (s +ᵥ AdelicBox.adelicBox ℚ)
  rw [hpre] at hshift
  rw [hshift]
  exact hbox'.setIntegral_eq hbox hf'

private theorem addChar_mul_algebraMap_add {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ}
    (hψ : IsPrincipalInvariantAddChar ℚ ψ) (β α : ℚ) (y : AdeleRing (𝓞 ℚ) ℚ) :
    ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α + y)) =
      ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * y) := by
  rw [mul_add, AddChar.map_add_eq_mul, ← map_mul (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)), hψ (β * α), one_mul]

private theorem setIntegral_adelicBox_addChar_mul_eq_zero {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ}
    (hψ : IsGlobalAddChar ℚ ψ)
    {β : ℚ} (hβ : β ≠ 0) :
    ∫ y in AdelicBox.adelicBox ℚ, ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * y)
      ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) = 0 := by
  obtain ⟨t, ht⟩ : ∃ t : AdeleRing (𝓞 ℚ) ℚ, ψ t ≠ 1 := by
    by_contra h
    refine hψ.nontrivial (AddChar.ext ψ 1 fun t => ?_)
    rw [AddChar.one_apply]
    by_contra ht
    exact h ⟨t, ht⟩
  set I : ℂ := ∫ y in AdelicBox.adelicBox ℚ, ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * y)
    ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) with hI
  have hβt : algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β⁻¹ * t) = t := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hβ, map_one, one_mul]
  have hshift := setIntegral_adelicBox_comp_add_right
    (f := fun y => ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * y))
    (addChar_mul_algebraMap_add hψ.principalInvariant β) (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β⁻¹ * t)
  have hmul : (∫ y in AdelicBox.adelicBox ℚ,
      ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * (y + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β⁻¹ * t))
        ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) = ψ t * I := by
    rw [hI, ← integral_const_mul]
    congr 1
    funext y
    rw [mul_add, AddChar.map_add_eq_mul, hβt, mul_comm]
  have h : ψ t * I = I := by
    rw [← hmul]
    exact hshift
  have h' : (ψ t - 1) * I = 0 := by rw [sub_mul, one_mul, h, sub_self]
  exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr ht)

private theorem integral_box_phase_eq_zero {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ)
    {β : ℚ} (hβ : β ≠ 0) :
    ∫ y, ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * y) ∂μbox = 0 := by
  rw [ProbabilityTheory.cond, integral_smul_measure, setIntegral_adelicBox_addChar_mul_eq_zero hψ hβ, smul_zero]

private theorem globalPoints_apply_one_one (h : GL (Fin 2) ℚ) :
    ((globalPoints (𝓞 ℚ) ℚ h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 1 =
      algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ((h : Matrix (Fin 2) (Fin 2) ℚ) 1 1) :=
  Matrix.GeneralLinearGroup.map_apply _ _ _ _

private theorem integral_box_phase_mul {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ) (δ : ℚ) :
    ∫ y, ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) δ * y) * ψ (-y) ∂μbox = if δ = 1 then 1 else 0 := by
  haveI := AdelicBox.isProbabilityMeasure_cond_adelicBox ℚ
  have hcomb : ∀ y : AdeleRing (𝓞 ℚ) ℚ,
      ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) δ * y) * ψ (-y) = ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (δ - 1) * y) := by
    intro y
    rw [← AddChar.map_add_eq_mul, map_sub, map_one]
    ring_nf
  simp_rw [hcomb]
  split_ifs with hδ
  · subst hδ
    simp
  · exact integral_box_phase_eq_zero hψ (sub_ne_zero.mpr hδ)

private theorem integral_box_tsum_phase {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ)
    (d : MirabolicIndex ℚ → AdeleRing (𝓞 ℚ) ℚ) (T : MirabolicIndex ℚ → ℂ) (hT : Summable T) :
    ∫ y, (∑' i, ψ (d i * y) * T i) * ψ (-y) ∂μbox = ∑' i, (∫ y, ψ (d i * y) * ψ (-y) ∂μbox) * T i := by
  haveI := AdelicBox.isProbabilityMeasure_cond_adelicBox ℚ
  haveI := borelSpace_adeleBorel (𝓞 ℚ) ℚ
  have hψc : Continuous ψ := hψ.continuous
  have hcont : ∀ i, Continuous fun y : AdeleRing (𝓞 ℚ) ℚ => ψ (d i * y) * T i * ψ (-y) := fun i =>
    ((hψc.comp (continuous_const.mul continuous_id)).mul continuous_const).mul (hψc.comp continuous_neg)
  have hnn : ∀ (i : MirabolicIndex ℚ) (y : AdeleRing (𝓞 ℚ) ℚ), ‖ψ (d i * y) * T i * ψ (-y)‖ₑ = ‖T i‖ₑ := by
    intro i y
    have h1 : ∀ x, ‖ψ x‖ₑ = 1 := fun x => by
      have hx : ‖ψ x‖ = 1 := by
        simpa using NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar ℚ hψ x
      rw [← ofReal_norm, hx, ENNReal.ofReal_one]
    rw [enorm_mul, enorm_mul, h1, h1, one_mul, mul_one]
  have hsumn : Summable fun i => ‖T i‖₊ :=
    NNReal.summable_coe.mp (by simpa only [coe_nnnorm] using (summable_norm_iff (f := T)).mpr hT)
  have hfun : (fun y : AdeleRing (𝓞 ℚ) ℚ => (∑' i, ψ (d i * y) * T i) * ψ (-y)) =
      fun y => ∑' i, ψ (d i * y) * T i * ψ (-y) := by
    funext y
    exact tsum_mul_right.symm
  rw [hfun, integral_tsum (fun i => (hcont i).aestronglyMeasurable)]
  · refine tsum_congr fun i => ?_
    simp_rw [mul_right_comm _ (T i)]
    exact integral_mul_const _ _
  · simp_rw [hnn, lintegral_const, measure_univ, mul_one, enorm_eq_nnnorm]
    exact ENNReal.tsum_coe_ne_top_iff_summable.mpr hsumn

end YStep

section ConstantTermRat

private theorem integral_box_phase_eq_ite {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ) (δ : ℚ) :
    ∫ y, ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) δ * y) ∂μbox = if δ = 0 then 1 else 0 := by
  haveI := AdelicBox.isProbabilityMeasure_cond_adelicBox ℚ
  split_ifs with h
  · subst h
    simp
  · exact integral_box_phase_eq_zero hψ h

private theorem integral_box_tsum_phase_rat {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ)
    (δ : MirabolicIndex ℚ → ℚ) (T : MirabolicIndex ℚ → ℂ) (hT : Summable T) :
    ∫ y, (∑' i, ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (δ i) * y) * T i) ∂μbox = ∑' i, if δ i = 0 then T i else 0 := by
  have hshift : ∀ y : AdeleRing (𝓞 ℚ) ℚ,
      (∑' i, ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (δ i) * y) * T i) =
        (∑' i, ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (δ i + 1) * y) * T i) * ψ (-y) := by
    intro y
    rw [← tsum_mul_right]
    refine tsum_congr fun i => ?_
    have h1 : ψ y * ψ (-y) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    rw [map_add, map_one, add_mul, one_mul, AddChar.map_add_eq_mul]
    linear_combination (-(ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (δ i) * y) * T i)) * h1
  simp_rw [hshift]
  rw [integral_box_tsum_phase hψ (fun i => algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (δ i + 1)) T hT]
  refine tsum_congr fun i => ?_
  rw [integral_box_phase_mul hψ]
  by_cases h : δ i = 0
  · simp [h]
  · simp [h]

end ConstantTermRat

section PrimalTerms

private noncomputable abbrev repMat (i : MirabolicIndex ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  ((mirabolicRep ℚ i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)

private theorem globalPoints_apply (h : GL (Fin 2) ℚ) (k l : Fin 2) :
    ((globalPoints (𝓞 ℚ) ℚ h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) k l =
      algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ((h : Matrix (Fin 2) (Fin 2) ℚ) k l) :=
  Matrix.GeneralLinearGroup.map_apply _ _ _ _

private theorem primal_term_radical_eq {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hW : IsGL3PsiWhittakerFn ψ W) (i : MirabolicIndex ℚ) (z y : AdeleRing (𝓞 ℚ) ℚ) (X : AdelicGL 3 (𝓞 ℚ) ℚ) :
    W (mirabolicTranslate i * (radicalP21 ![z, y] * X)) =
      ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (repMat i 1 0) * z + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (repMat i 1 1) * y) *
        W (mirabolicTranslate i * X) := by
  have hrad : (radicalP21 ![z, y] : GL (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = upperUnipotent3 0 y z := rfl
  show W (iotaGL (globalPoints (𝓞 ℚ) ℚ (mirabolicRep ℚ i)) * (radicalP21 ![z, y] * X)) =
    _ * W (iotaGL (globalPoints (𝓞 ℚ) ℚ (mirabolicRep ℚ i)) * X)
  rw [hrad, ← mul_assoc, iotaGL_mul_upperUnipotent3_zero, mul_assoc, hW, zero_add, globalPoints_apply,
    globalPoints_apply]

end PrimalTerms

section BottomRow

private theorem repMat_apply_one_one_ne_zero (i : MirabolicIndex ℚ) (h10 : repMat i 1 0 = 0) : repMat i 1 1 ≠ 0 := by
  intro h11
  have hdet : (repMat i).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (mirabolicRep ℚ i : GL (Fin 2) ℚ).isUnit).ne_zero
  apply hdet
  rw [Matrix.det_fin_two, h10, h11]
  ring

end BottomRow

section Radial

private theorem summable_addChar_mul_iff {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ)
    (c : MirabolicIndex ℚ → AdeleRing (𝓞 ℚ) ℚ) (T : MirabolicIndex ℚ → ℂ) :
    (Summable fun i => ψ (c i) * T i) ↔ Summable T := by
  have hone : ∀ x, ‖ψ x‖ = 1 := fun x => by
    simpa using NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar ℚ hψ x
  rw [← summable_norm_iff (f := fun i => ψ (c i) * T i), ← summable_norm_iff (f := T)]
  simp [hone]

private theorem term_radical_eq_mul {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hW : IsGL3PsiWhittakerFn ψ W) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (x y : AdeleRing (𝓞 ℚ) ℚ) (i : MirabolicIndex ℚ) :
    W (mirabolicTranslate i * (radicalP21 ![x, y] * g)) =
      ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (repMat i 1 1) * y) *
        (ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (repMat i 1 0) * x) * W (mirabolicTranslate i * g)) := by
  rw [primal_term_radical_eq hW, AddChar.map_add_eq_mul, mul_assoc, mul_left_comm]

private theorem integral_integral_mirabolicSeries_radical_eq_zero_of_summable {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ}
    (hψ : IsGlobalAddChar ℚ ψ) {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hW : IsGL3PsiWhittakerFn ψ W)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hs : Summable fun i : MirabolicIndex ℚ => W (mirabolicTranslate i * g)) :
    ∫ x, ∫ y, (∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * (radicalP21 ![x, y] * g))) ∂μbox ∂μbox = 0 := by
  have hterm : ∀ x y : AdeleRing (𝓞 ℚ) ℚ,
      (∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * (radicalP21 ![x, y] * g))) =
        ∑' i : MirabolicIndex ℚ, ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (repMat i 1 1) * y) *
          (ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (repMat i 1 0) * x) * W (mirabolicTranslate i * g)) :=
    fun x y => tsum_congr fun i => term_radical_eq_mul hW g x y i
  have hinner : ∀ x : AdeleRing (𝓞 ℚ) ℚ,
      (∫ y, (∑' i : MirabolicIndex ℚ, ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (repMat i 1 1) * y) *
          (ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (repMat i 1 0) * x) * W (mirabolicTranslate i * g))) ∂μbox) =
        ∑' i : MirabolicIndex ℚ, ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (repMat i 1 0) * x) *
          (if repMat i 1 1 = 0 then W (mirabolicTranslate i * g) else 0) := by
    intro x
    rw [integral_box_tsum_phase_rat hψ (fun i => repMat i 1 1)
      (fun i => ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (repMat i 1 0) * x) * W (mirabolicTranslate i * g))
      ((summable_addChar_mul_iff hψ _ _).mpr hs)]
    refine tsum_congr fun i => ?_
    split_ifs <;> simp
  have hsum' : Summable fun i : MirabolicIndex ℚ => if repMat i 1 1 = 0 then W (mirabolicTranslate i * g) else 0 :=
    hs.summable_of_eq_zero_or_self fun i => by
      by_cases h : repMat i 1 1 = 0 <;> simp [h]
  simp_rw [hterm, hinner]
  rw [integral_box_tsum_phase_rat hψ (fun i => repMat i 1 0) _ hsum']
  refine (tsum_congr fun i => ?_).trans tsum_zero
  by_cases h10 : repMat i 1 0 = 0
  · rw [if_pos h10, if_neg (repMat_apply_one_one_ne_zero i h10)]
  · rw [if_neg h10]

private theorem tsum_mirabolicSeries_radical_eq_zero_of_not_summable {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ}
    (hψ : IsGlobalAddChar ℚ ψ) {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hW : IsGL3PsiWhittakerFn ψ W)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hs : ¬ Summable fun i : MirabolicIndex ℚ => W (mirabolicTranslate i * g))
    (x y : AdeleRing (𝓞 ℚ) ℚ) :
    (∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * (radicalP21 ![x, y] * g))) = 0 := by
  refine tsum_eq_zero_of_not_summable fun hsum => hs ?_
  have h : Summable fun i : MirabolicIndex ℚ =>
      ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (repMat i 1 0) * x + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (repMat i 1 1) * y) *
        W (mirabolicTranslate i * g) :=
    hsum.congr fun i => primal_term_radical_eq hW i x y g
  exact (summable_addChar_mul_iff hψ _ _).mp h

end Radial

end LanglandsTunnell.CubicInduction

p2m_open "IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_isCuspidalAlongP21_mirabolicSeries.LanglandsTunnell.CubicInduction"

theorem solution
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (_hW : IsGL3PsiWhittakerFn ψ W)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ) :
    IsCuspidalAlongP21 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ))
      (fun x => ∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * x)) := by
  intro g
  show (∫ x, ∫ y, (∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * (radicalP21 ![x, y] * g)))
      ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))
      ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))) = 0
  by_cases hs : Summable fun i : MirabolicIndex ℚ => W (mirabolicTranslate i * g)
  · exact integral_integral_mirabolicSeries_radical_eq_zero_of_summable _hψ _hW g hs
  · simp_rw [tsum_mirabolicSeries_radical_eq_zero_of_not_summable _hψ _hW g hs]
    simp

#print axioms solution

end S_LanglandsTunnell_CubicInduction_isCuspidalAlongP21_mirabolicSeries
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_isCuspidalAlongP21_mirabolicSeries (solution)
