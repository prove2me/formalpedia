-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.radicalCoefficient_eq_radicalCoefficient_psi_neg_iotaGL_globalPoints_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/3520616a-6441-547a-9c42-ee7ebd4cd09e

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_NumberField_AdelicHaar_measurePreserving_mul_algebraMap_adelicAddHaar
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_radicalCoefficient_eq_radicalCoefficient_psi_neg_iotaGL_globalPoints_mul
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

section

set_option autoImplicit false

open MeasureTheory NumberField

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL globalPointsGL upperUnipotent3 radicalP21 radicalP21_add embedMat2 iotaGL"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

private scoped instance countable_principalSubgroup : Countable (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) := by
  refine Function.Surjective.countable (f := fun q : ℚ =>
    (⟨algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q, q, rfl⟩ : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ)) ?_
  rintro ⟨_, q, rfl⟩
  exact ⟨q, rfl⟩

private noncomputable def mulAdeleEquiv (c : ℚ) (hc : c ≠ 0) : AdeleRing (𝓞 ℚ) ℚ ≃ AdeleRing (𝓞 ℚ) ℚ where
  toFun u := algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) c * u
  invFun u := algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) c⁻¹ * u
  left_inv u := by simp only [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
  right_inv u := by simp only [← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul]

private theorem algebraMap_mul_mem_principalSubgroup (c : ℚ) (γ : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) :
    algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) c * (γ : AdeleRing (𝓞 ℚ) ℚ) ∈ AdeleRing.principalSubgroup (𝓞 ℚ) ℚ := by
  obtain ⟨β, hβ⟩ := γ.2
  exact ⟨c * β, by rw [map_mul, hβ]⟩

private noncomputable def mulPrincipalEquiv (c : ℚ) (hc : c ≠ 0) :
    AdeleRing.principalSubgroup (𝓞 ℚ) ℚ ≃ AdeleRing.principalSubgroup (𝓞 ℚ) ℚ where
  toFun γ := ⟨algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) c * γ, algebraMap_mul_mem_principalSubgroup c γ⟩
  invFun γ := ⟨algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) c⁻¹ * γ, algebraMap_mul_mem_principalSubgroup c⁻¹ γ⟩
  left_inv γ := Subtype.ext (by simp only [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul])
  right_inv γ := Subtype.ext (by simp only [← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul])

private theorem measurableEmbedding_mul (c : ℚ) (hc : c ≠ 0) :
    MeasurableEmbedding (fun u : AdeleRing (𝓞 ℚ) ℚ => algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) c * u) :=
  MeasurableEquiv.measurableEmbedding
    { toEquiv := mulAdeleEquiv c hc
      measurable_toFun := (continuous_const.mul continuous_id).measurable
      measurable_invFun := (continuous_const.mul continuous_id).measurable }

private theorem setIntegral_adelicBox_comp_add (h : AdeleRing (𝓞 ℚ) ℚ → ℂ)
    (hper : ∀ (β : ℚ) (u : AdeleRing (𝓞 ℚ) ℚ), h (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β + u) = h u)
    (x : AdeleRing (𝓞 ℚ) ℚ) :
    ∫ u in AdelicBox.adelicBox ℚ, h (x + u) ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) =
      ∫ u in AdelicBox.adelicBox ℚ, h u ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) := by
  set μ := NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ
  have hme : MeasurableEmbedding (fun u : AdeleRing (𝓞 ℚ) ℚ => x + u) :=
    (Homeomorph.addLeft x).measurableEmbedding
  have h1 : ∫ u in AdelicBox.adelicBox ℚ, h (x + u) ∂μ =
      ∫ w in (fun u : AdeleRing (𝓞 ℚ) ℚ => x + u) '' AdelicBox.adelicBox ℚ, h w ∂μ := by
    conv_lhs => rw [← Set.preimage_image_eq (AdelicBox.adelicBox ℚ) (add_right_injective x)]
    rw [← hme.setIntegral_map, map_add_left_eq_self]
  have hFD : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ) μ :=
    AdelicBox.isAddFundamentalDomain_adelicBox ℚ μ
  have hFD' : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ)
      ((fun u : AdeleRing (𝓞 ℚ) ℚ => x + u) '' AdelicBox.adelicBox ℚ) μ := by
    refine hFD.image_of_equiv (ν := μ) (Equiv.addLeft x) ?_ (Equiv.refl _) ?_
    · simpa using (measurePreserving_add_left μ (-x)).quasiMeasurePreserving
    · intro γ u
      show x + (γ +ᵥ u) = γ +ᵥ (x + u)
      simp only [AddSubgroup.vadd_def, vadd_eq_add, add_left_comm]
  have hinv : ∀ (γ : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (u : AdeleRing (𝓞 ℚ) ℚ), h (γ +ᵥ u) = h u := by
    rintro ⟨_, β, rfl⟩ u
    exact hper β u
  rw [h1]
  exact hFD'.setIntegral_eq hFD hinv

private theorem setIntegral_adelicBox_comp_mul (h : AdeleRing (𝓞 ℚ) ℚ → ℂ)
    (hper : ∀ (β : ℚ) (u : AdeleRing (𝓞 ℚ) ℚ), h (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β + u) = h u)
    (c : ℚ) (hc : c ≠ 0) :
    ∫ u in AdelicBox.adelicBox ℚ, h (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) c * u)
        ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) =
      ∫ u in AdelicBox.adelicBox ℚ, h u ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) := by
  set μ := NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ
  have hmp : MeasurePreserving (fun u : AdeleRing (𝓞 ℚ) ℚ => algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) c * u) μ μ :=
    NumberField.AdelicHaar.measurePreserving_mul_algebraMap_adelicAddHaar ℚ c hc
  have hmp' : MeasurePreserving (fun u : AdeleRing (𝓞 ℚ) ℚ => algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) c⁻¹ * u) μ μ :=
    NumberField.AdelicHaar.measurePreserving_mul_algebraMap_adelicAddHaar ℚ c⁻¹ (inv_ne_zero hc)
  have hme := measurableEmbedding_mul c hc
  have h1 : ∫ u in AdelicBox.adelicBox ℚ, h (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) c * u) ∂μ =
      ∫ w in (fun u : AdeleRing (𝓞 ℚ) ℚ => algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) c * u) '' AdelicBox.adelicBox ℚ,
        h w ∂μ := by
    conv_lhs => rw [← Set.preimage_image_eq (AdelicBox.adelicBox ℚ) hme.injective]
    rw [← hme.setIntegral_map, hmp.map_eq]
  have hFD : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ) μ :=
    AdelicBox.isAddFundamentalDomain_adelicBox ℚ μ
  have hFD' : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ)
      ((fun u : AdeleRing (𝓞 ℚ) ℚ => algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) c * u) '' AdelicBox.adelicBox ℚ) μ := by
    refine hFD.image_of_equiv (ν := μ) (mulAdeleEquiv c hc) hmp'.quasiMeasurePreserving
      (mulPrincipalEquiv c⁻¹ (inv_ne_zero hc)) ?_
    intro γ u
    show algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) c * (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) c⁻¹ * (γ : AdeleRing (𝓞 ℚ) ℚ) + u) =
      (γ : AdeleRing (𝓞 ℚ) ℚ) + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) c * u
    rw [mul_add, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul]
  have hinv : ∀ (γ : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (u : AdeleRing (𝓞 ℚ) ℚ), h (γ +ᵥ u) = h u := by
    rintro ⟨_, β, rfl⟩ u
    exact hper β u
  rw [h1]
  exact hFD'.setIntegral_eq hFD hinv

private noncomputable def boxMeasure : Measure (AdeleRing (𝓞 ℚ) ℚ) :=
  ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ)

private theorem integral_boxMeasure_comp_add_left (h : AdeleRing (𝓞 ℚ) ℚ → ℂ)
    (hper : ∀ (β : ℚ) (u : AdeleRing (𝓞 ℚ) ℚ), h (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β + u) = h u)
    (x : AdeleRing (𝓞 ℚ) ℚ) : ∫ u, h (x + u) ∂boxMeasure = ∫ u, h u ∂boxMeasure := by
  simp only [boxMeasure, ProbabilityTheory.cond, integral_smul_measure, setIntegral_adelicBox_comp_add h hper x]

private theorem integral_boxMeasure_comp_add (h : AdeleRing (𝓞 ℚ) ℚ → ℂ)
    (hper : ∀ (β : ℚ) (u : AdeleRing (𝓞 ℚ) ℚ), h (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β + u) = h u)
    (x : AdeleRing (𝓞 ℚ) ℚ) : ∫ u, h (u + x) ∂boxMeasure = ∫ u, h u ∂boxMeasure := by
  simp only [add_comm _ x]
  exact integral_boxMeasure_comp_add_left h hper x

private theorem integral_boxMeasure_comp_mul (h : AdeleRing (𝓞 ℚ) ℚ → ℂ)
    (hper : ∀ (β : ℚ) (u : AdeleRing (𝓞 ℚ) ℚ), h (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β + u) = h u)
    (c : ℚ) (hc : c ≠ 0) :
    ∫ u, h (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) c * u) ∂boxMeasure = ∫ u, h u ∂boxMeasure := by
  simp only [boxMeasure, ProbabilityTheory.cond, integral_smul_measure, setIntegral_adelicBox_comp_mul h hper c hc]

private theorem integral_boxMeasure_comp_mul_add (h : AdeleRing (𝓞 ℚ) ℚ → ℂ)
    (hper : ∀ (β : ℚ) (u : AdeleRing (𝓞 ℚ) ℚ), h (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β + u) = h u)
    (c : ℚ) (hc : c ≠ 0) (u₀ : AdeleRing (𝓞 ℚ) ℚ) :
    ∫ u, h (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) c * u + u₀) ∂boxMeasure = ∫ u, h u ∂boxMeasure := by
  have hper' : ∀ (β : ℚ) (w : AdeleRing (𝓞 ℚ) ℚ),
      h (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β + w + u₀) = h (w + u₀) := by
    intro β w
    rw [add_assoc, hper]
  rw [integral_boxMeasure_comp_mul (fun w => h (w + u₀)) hper' c hc, integral_boxMeasure_comp_add h hper u₀]

private theorem integral_cond_adelicBox_comp_mul_add_eq_of_periodic
    (h : AdeleRing (𝓞 ℚ) ℚ → ℂ) (_hh : Continuous h)
    (_hper : ∀ (β : ℚ) (u : AdeleRing (𝓞 ℚ) ℚ), h (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β + u) = h u)
    (a : ℚˣ) (u₀ : AdeleRing (𝓞 ℚ) ℚ) :
    (∫ u : AdeleRing (𝓞 ℚ) ℚ, h (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (a : ℚ) * u + u₀)
        ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))) =
      ∫ u : AdeleRing (𝓞 ℚ) ℚ, h u
        ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ)) := by
  exact integral_boxMeasure_comp_mul_add h _hper (a : ℚ) a.ne_zero u₀

private def IsPeriodicPair (H : AdeleRing (𝓞 ℚ) ℚ → AdeleRing (𝓞 ℚ) ℚ → ℂ) : Prop :=
  (Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => H p.1 p.2) ∧
    (∀ (β : ℚ) (z y : AdeleRing (𝓞 ℚ) ℚ), H (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β + z) y = H z y) ∧
      ∀ (β : ℚ) (z y : AdeleRing (𝓞 ℚ) ℚ), H z (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β + y) = H z y

private noncomputable def substituteByMatrix (M : Matrix (Fin 2) (Fin 2) ℚ)
    (H : AdeleRing (𝓞 ℚ) ℚ → AdeleRing (𝓞 ℚ) ℚ → ℂ) (z y : AdeleRing (𝓞 ℚ) ℚ) : ℂ :=
  H (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 0 0) * z + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 1 0) * y)
    (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 0 1) * z + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 1 1) * y)

private theorem isPeriodicPair_shift {H : AdeleRing (𝓞 ℚ) ℚ → AdeleRing (𝓞 ℚ) ℚ → ℂ} (hH : IsPeriodicPair H)
    (β₁ β₂ : ℚ) (z y : AdeleRing (𝓞 ℚ) ℚ) :
    H (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β₁ + z) (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β₂ + y) = H z y := by
  rw [hH.2.1, hH.2.2]

private theorem isPeriodicPair_substituteByMatrix (M : Matrix (Fin 2) (Fin 2) ℚ)
    {H : AdeleRing (𝓞 ℚ) ℚ → AdeleRing (𝓞 ℚ) ℚ → ℂ} (hH : IsPeriodicPair H) :
    IsPeriodicPair (substituteByMatrix M H) := by
  refine ⟨?_, ?_, ?_⟩
  · have h₁ : Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
        algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 0 0) * p.1 + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 1 0) * p.2 :=
      (continuous_const.mul continuous_fst).add (continuous_const.mul continuous_snd)
    have h₂ : Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
        algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 0 1) * p.1 + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 1 1) * p.2 :=
      (continuous_const.mul continuous_fst).add (continuous_const.mul continuous_snd)
    exact hH.1.comp (h₁.prodMk h₂)
  · intro β z y
    have e₁ : algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 0 0) * (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β + z) +
          algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 1 0) * y =
        algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 0 0 * β) +
          (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 0 0) * z + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 1 0) * y) := by
      rw [map_mul]; ring
    have e₂ : algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 0 1) * (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β + z) +
          algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 1 1) * y =
        algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 0 1 * β) +
          (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 0 1) * z + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 1 1) * y) := by
      rw [map_mul]; ring
    simp only [substituteByMatrix]
    rw [e₁, e₂, isPeriodicPair_shift hH]
  · intro β z y
    have e₁ : algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 0 0) * z +
          algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 1 0) * (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β + y) =
        algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 1 0 * β) +
          (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 0 0) * z + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 1 0) * y) := by
      rw [map_mul]; ring
    have e₂ : algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 0 1) * z +
          algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 1 1) * (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β + y) =
        algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 1 1 * β) +
          (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 0 1) * z + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 1 1) * y) := by
      rw [map_mul]; ring
    simp only [substituteByMatrix]
    rw [e₁, e₂, isPeriodicPair_shift hH]

private theorem exists_bound_of_isPeriodicPair {H : AdeleRing (𝓞 ℚ) ℚ → AdeleRing (𝓞 ℚ) ℚ → ℂ}
    (hH : IsPeriodicPair H) : ∃ C : ℝ, ∀ z y : AdeleRing (𝓞 ℚ) ℚ, ‖H z y‖ ≤ C := by
  obtain ⟨K, hK, hbox⟩ := AdelicBox.exists_isCompact_adelicBox_subset ℚ
  obtain ⟨C, hC⟩ := (hK.prod hK).exists_bound_of_continuousOn hH.1.continuousOn
  refine ⟨C, fun z y => ?_⟩
  obtain ⟨k₁, hk₁, -⟩ := AdelicBox.existsUnique_algebraMap_add_mem_adelicBox ℚ z
  obtain ⟨k₂, hk₂, -⟩ := AdelicBox.existsUnique_algebraMap_add_mem_adelicBox ℚ y
  have := hC _ (Set.mk_mem_prod (hbox hk₁) (hbox hk₂))
  simpa only [isPeriodicPair_shift hH] using this

private theorem integral_integral_swap_of_isPeriodicPair {H : AdeleRing (𝓞 ℚ) ℚ → AdeleRing (𝓞 ℚ) ℚ → ℂ}
    (hH : IsPeriodicPair H) :
    ∫ z, ∫ y, H z y ∂boxMeasure ∂boxMeasure = ∫ y, ∫ z, H z y ∂boxMeasure ∂boxMeasure := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdeleRing.secondCountableTopology ℚ
  haveI : IsProbabilityMeasure boxMeasure := AdelicBox.isProbabilityMeasure_cond_adelicBox ℚ
  obtain ⟨C, hC⟩ := exists_bound_of_isPeriodicPair hH
  have hint : Integrable (Function.uncurry H) (boxMeasure.prod boxMeasure) :=
    (integrable_const C).mono' hH.1.aestronglyMeasurable (Filter.Eventually.of_forall fun p => hC p.1 p.2)
  exact MeasureTheory.integral_integral_swap hint

private def IsSubstitutionInvariant (M : Matrix (Fin 2) (Fin 2) ℚ) : Prop :=
  ∀ H : AdeleRing (𝓞 ℚ) ℚ → AdeleRing (𝓞 ℚ) ℚ → ℂ, IsPeriodicPair H →
    ∫ z, ∫ y, substituteByMatrix M H z y ∂boxMeasure ∂boxMeasure = ∫ z, ∫ y, H z y ∂boxMeasure ∂boxMeasure

private theorem isSubstitutionInvariant_diagonal (D : Fin 2 → ℚ) (hD : (Matrix.diagonal D).det ≠ 0) :
    IsSubstitutionInvariant (Matrix.diagonal D) := by
  intro H hH
  rw [Matrix.det_diagonal, Fin.prod_univ_two] at hD
  have hD0 : D 0 ≠ 0 := left_ne_zero_of_mul hD
  have hD1 : D 1 ≠ 0 := right_ne_zero_of_mul hD
  have hsub : ∀ z y : AdeleRing (𝓞 ℚ) ℚ, substituteByMatrix (Matrix.diagonal D) H z y =
      H (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (D 0) * z) (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (D 1) * y) := by
    intro z y
    simp [substituteByMatrix]
  have hin : ∀ z : AdeleRing (𝓞 ℚ) ℚ,
      ∫ y, H (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (D 0) * z) (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (D 1) * y) ∂boxMeasure =
        ∫ y, H (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (D 0) * z) y ∂boxMeasure :=
    fun z => integral_boxMeasure_comp_mul (fun y => H (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (D 0) * z) y)
      (fun β y => hH.2.2 β _ y) (D 1) hD1
  have hout : ∀ (β : ℚ) (w : AdeleRing (𝓞 ℚ) ℚ),
      ∫ y, H (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β + w) y ∂boxMeasure = ∫ y, H w y ∂boxMeasure := by
    intro β w
    simp only [hH.2.1]
  simp only [hsub, hin]
  exact integral_boxMeasure_comp_mul (fun w => ∫ y, H w y ∂boxMeasure) hout (D 0) hD0

private theorem isSubstitutionInvariant_transvection (t : Matrix.TransvectionStruct (Fin 2) ℚ) :
    IsSubstitutionInvariant t.toMatrix := by
  intro H hH
  rcases t with ⟨i, j, hij, c⟩
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  ·
    simp [substituteByMatrix, Matrix.transvection, Matrix.single_apply_same,
      Matrix.single_apply_of_ne]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact integral_boxMeasure_comp_add_left (fun y => H z y) (fun β y => hH.2.2 β z y) _
  ·
    rw [integral_integral_swap_of_isPeriodicPair (isPeriodicPair_substituteByMatrix _ hH),
      integral_integral_swap_of_isPeriodicPair hH]
    simp [substituteByMatrix, Matrix.transvection, Matrix.single_apply_same,
      Matrix.single_apply_of_ne]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    exact integral_boxMeasure_comp_add (fun z => H z y) (fun β z => hH.2.1 β z y) _
  · exact absurd rfl hij

private theorem isSubstitutionInvariant_mul (A B : Matrix (Fin 2) (Fin 2) ℚ) (_hA : A.det ≠ 0) (_hB : B.det ≠ 0)
    (hA : IsSubstitutionInvariant A) (hB : IsSubstitutionInvariant B) : IsSubstitutionInvariant (A * B) := by
  intro H hH
  have key : ∀ z y : AdeleRing (𝓞 ℚ) ℚ,
      substituteByMatrix (A * B) H z y = substituteByMatrix A (substituteByMatrix B H) z y := by
    intro z y
    simp only [substituteByMatrix, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul]
    congr 1 <;> ring
  simp only [key]
  rw [hA _ (isPeriodicPair_substituteByMatrix B hH), hB H hH]

private theorem integral_integral_cond_adelicBox_comp_vecMul_eq_of_periodic
    (H : AdeleRing (𝓞 ℚ) ℚ → AdeleRing (𝓞 ℚ) ℚ → ℂ)
    (_hH : Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => H p.1 p.2)
    (_hper₁ : ∀ (β : ℚ) (z y : AdeleRing (𝓞 ℚ) ℚ), H (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β + z) y = H z y)
    (_hper₂ : ∀ (β : ℚ) (z y : AdeleRing (𝓞 ℚ) ℚ), H z (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β + y) = H z y)
    (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ) :
    (∫ z : AdeleRing (𝓞 ℚ) ℚ, ∫ y : AdeleRing (𝓞 ℚ) ℚ,
        H (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) 0 0) * z +
            algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0) * y)
          (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) 0 1) * z +
            algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1) * y)
        ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))
        ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))) =
      ∫ z : AdeleRing (𝓞 ℚ) ℚ, ∫ y : AdeleRing (𝓞 ℚ) ℚ, H z y
        ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))
        ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ)) := by
  have hdet : ((γ : Matrix (Fin 2) (Fin 2) ℚ)).det ≠ 0 := (Matrix.isUnits_det_units γ).ne_zero
  exact Matrix.diagonal_transvection_induction_of_det_ne_zero IsSubstitutionInvariant _ hdet
    isSubstitutionInvariant_diagonal isSubstitutionInvariant_transvection isSubstitutionInvariant_mul H
    ⟨_hH, _hper₁, _hper₂⟩

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_radicalCoefficient_eq_radicalCoefficient_psi_neg_iotaGL_globalPoints_mul.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_radicalCoefficient_eq_radicalCoefficient_psi_neg_iotaGL_globalPoints_mul.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_radicalCoefficient_eq_radicalCoefficient_psi_neg_iotaGL_globalPoints_mul.LanglandsTunnell"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_radicalCoefficient_eq_radicalCoefficient_psi_neg_iotaGL_globalPoints_mul.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_radicalCoefficient_eq_radicalCoefficient_psi_neg_iotaGL_globalPoints_mul.LanglandsTunnell.CubicInduction"

p2m_open "MeasureTheory NumberField AutomorphicForm LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_radicalCoefficient_eq_radicalCoefficient_psi_neg_iotaGL_globalPoints_mul.LanglandsTunnell.CubicInduction"

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL globalPointsGL upperUnipotent3 radicalP21 radicalP21_add embedMat2 iotaGL"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section Conjugation

variable {A : Type*} [CommRing A]

private theorem radicalP21_mulVec_mul_iotaGL (h : Matrix.GeneralLinearGroup (Fin 2) A) (w : Fin 2 → A) :
    radicalP21 ((h : Matrix (Fin 2) (Fin 2) A).mulVec w) * iotaGL h = iotaGL h * radicalP21 w := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, embedMat2]

end Conjugation
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_radicalCoefficient_eq_radicalCoefficient_psi_neg_iotaGL_globalPoints_mul.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_radicalCoefficient_eq_radicalCoefficient_psi_neg_iotaGL_globalPoints_mul.LanglandsTunnell.CubicInduction"

section RationalPoints

private theorem globalPointsGL_iotaGL (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ) :
    globalPointsGL 3 (𝓞 ℚ) ℚ (iotaGL γ) = iotaGL (globalPointsGL 2 (𝓞 ℚ) ℚ γ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [globalPointsGL, Matrix.GeneralLinearGroup.map, embedMat2]

private theorem globalPointsGL_radicalP21 (v : Fin 2 → ℚ) :
    globalPointsGL 3 (𝓞 ℚ) ℚ (radicalP21 v) = radicalP21 fun i => algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (v i) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [globalPointsGL, Matrix.GeneralLinearGroup.map]

private theorem apply_radicalP21_algebraMap_mul (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hinv : ∀ (δ : Matrix.GeneralLinearGroup (Fin 3) ℚ) (h : AdelicGL 3 (𝓞 ℚ) ℚ),
      Φ (globalPointsGL 3 (𝓞 ℚ) ℚ δ * h) = Φ h)
    (v : Fin 2 → ℚ) (h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Φ (radicalP21 (fun i => algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (v i)) * h) = Φ h := by
  rw [← globalPointsGL_radicalP21]
  exact hinv _ _

end RationalPoints
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_radicalCoefficient_eq_radicalCoefficient_psi_neg_iotaGL_globalPoints_mul.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_radicalCoefficient_eq_radicalCoefficient_psi_neg_iotaGL_globalPoints_mul.LanglandsTunnell.CubicInduction"

section Continuity

private theorem continuous_radicalP21_pair :
    Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => radicalP21 ![p.1, p.2] := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [radicalP21, upperUnipotent3] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [radicalP21, upperUnipotent3] <;> fun_prop

end Continuity
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_radicalCoefficient_eq_radicalCoefficient_psi_neg_iotaGL_globalPoints_mul.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_radicalCoefficient_eq_radicalCoefficient_psi_neg_iotaGL_globalPoints_mul.LanglandsTunnell.CubicInduction"

section Substitution

private theorem integral_integral_cond_adelicBox_comp_inv_mulVec_eq_of_periodic
    (H : AdeleRing (𝓞 ℚ) ℚ → AdeleRing (𝓞 ℚ) ℚ → ℂ)
    (hH : Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => H p.1 p.2)
    (hper₁ : ∀ (β : ℚ) (z y : AdeleRing (𝓞 ℚ) ℚ), H (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β + z) y = H z y)
    (hper₂ : ∀ (β : ℚ) (z y : AdeleRing (𝓞 ℚ) ℚ), H z (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β + y) = H z y)
    (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ) :
    (∫ z : AdeleRing (𝓞 ℚ) ℚ, ∫ y : AdeleRing (𝓞 ℚ) ℚ,
        H (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)
                (((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 0 0) * z +
              algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)
                (((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 0 1) * y)
          (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)
                (((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0) * z +
              algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)
                (((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 1) * y)
        ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))
        ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))) =
      ∫ z : AdeleRing (𝓞 ℚ) ℚ, ∫ y : AdeleRing (𝓞 ℚ) ℚ, H z y
        ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))
        ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ)) := by
  have key := integral_integral_cond_adelicBox_comp_vecMul_eq_of_periodic H hH hper₁ hper₂
    ⟨(((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)).transpose,
      (γ : Matrix (Fin 2) (Fin 2) ℚ).transpose,
      by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
      by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩
  simpa only [Units.val_mk, Matrix.transpose_apply] using key

end Substitution
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_radicalCoefficient_eq_radicalCoefficient_psi_neg_iotaGL_globalPoints_mul.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_radicalCoefficient_eq_radicalCoefficient_psi_neg_iotaGL_globalPoints_mul.LanglandsTunnell.CubicInduction"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_radicalCoefficient_eq_radicalCoefficient_psi_neg_iotaGL_globalPoints_mul.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_radicalCoefficient_eq_radicalCoefficient_psi_neg_iotaGL_globalPoints_mul.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_radicalCoefficient_eq_radicalCoefficient_psi_neg_iotaGL_globalPoints_mul.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_radicalCoefficient_eq_radicalCoefficient_psi_neg_iotaGL_globalPoints_mul.LanglandsTunnell.CubicInduction"

theorem solution
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (_hcont : Continuous Φ)
    (_hinv : ∀ (δ : Matrix.GeneralLinearGroup (Fin 3) ℚ) (h : AdelicGL 3 (𝓞 ℚ) ℚ),
      Φ (globalPointsGL 3 (𝓞 ℚ) ℚ δ * h) = Φ h)
    (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ) (v : Fin 2 → ℚ)
    (_hv : Matrix.vecMul ![0, 1] (γ : Matrix (Fin 2) (Fin 2) ℚ) = v)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (∫ z : AdeleRing (𝓞 ℚ) ℚ, ∫ y : AdeleRing (𝓞 ℚ) ℚ,
        Φ (radicalP21 ![z, y] * g) *
          ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (v 0) * z + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (v 1) * y))
      ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))
      ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))) =
    ∫ z : AdeleRing (𝓞 ℚ) ℚ, ∫ y : AdeleRing (𝓞 ℚ) ℚ,
        Φ (radicalP21 ![z, y] * (iotaGL (globalPointsGL 2 (𝓞 ℚ) ℚ γ) * g)) * ψ (-y)
      ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))
      ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ)) := by
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 2) (Fin 2) ℚ,
      M = ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) := ⟨_, rfl⟩
  have hγM : (γ : Matrix (Fin 2) (Fin 2) ℚ) * M = 1 := by
    rw [hM]
    exact Units.mul_inv γ
  have hvM : Matrix.vecMul v M = ![0, 1] := by
    rw [← _hv, Matrix.vecMul_vecMul, hγM, Matrix.vecMul_one]

  have h00 : (γ : Matrix (Fin 2) (Fin 2) ℚ) 0 0 * M 0 0 + (γ : Matrix (Fin 2) (Fin 2) ℚ) 0 1 * M 1 0 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hγM 0) 0
  have h01 : (γ : Matrix (Fin 2) (Fin 2) ℚ) 0 0 * M 0 1 + (γ : Matrix (Fin 2) (Fin 2) ℚ) 0 1 * M 1 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hγM 0) 1
  have h10 : (γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0 * M 0 0 + (γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1 * M 1 0 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hγM 1) 0
  have h11 : (γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0 * M 0 1 + (γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1 * M 1 1 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hγM 1) 1
  have hv0 : v 0 * M 0 0 + v 1 * M 1 0 = 0 := by
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using congrFun hvM 0
  have hv1 : v 0 * M 0 1 + v 1 * M 1 1 = 1 := by
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using congrFun hvM 1
  have e00 := congrArg (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) h00
  have e01 := congrArg (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) h01
  have e10 := congrArg (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) h10
  have e11 := congrArg (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) h11
  have ev0 := congrArg (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) hv0
  have ev1 := congrArg (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) hv1
  simp only [map_add, map_mul, map_one, map_zero] at e00 e01 e10 e11 ev0 ev1

  have hw : ∀ z y : AdeleRing (𝓞 ℚ) ℚ,
      (globalPointsGL 2 (𝓞 ℚ) ℚ γ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)).mulVec
          ![algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 0 0) * z +
              algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 0 1) * y,
            algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 1 0) * z +
              algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 1 1) * y] =
        ![z, y] := by
    intro z y
    funext i
    fin_cases i
    · simp [globalPointsGL, Matrix.GeneralLinearGroup.map, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination z * e00 + y * e01
    · simp [globalPointsGL, Matrix.GeneralLinearGroup.map, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination z * e10 + y * e11
  have hchar : ∀ z y : AdeleRing (𝓞 ℚ) ℚ,
      algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (v 0) *
            (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 0 0) * z +
              algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 0 1) * y) +
          algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (v 1) *
            (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 1 0) * z +
              algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 1 1) * y) =
        y := by
    intro z y
    linear_combination z * ev0 + y * ev1
  have hpt : ∀ z y : AdeleRing (𝓞 ℚ) ℚ,
      Φ (radicalP21 ![z, y] * (iotaGL (globalPointsGL 2 (𝓞 ℚ) ℚ γ) * g)) * ψ (-y) =
        Φ (radicalP21
              ![algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 0 0) * z +
                  algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 0 1) * y,
                algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 1 0) * z +
                  algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 1 1) * y] * g) *
          ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (v 0) *
                (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 0 0) * z +
                  algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 0 1) * y) +
              algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (v 1) *
                (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 1 0) * z +
                  algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (M 1 1) * y))) := by
    intro z y
    rw [hchar z y]
    congr 1
    conv_lhs => rw [← hw z y]
    rw [← mul_assoc, radicalP21_mulVec_mul_iotaGL, mul_assoc, ← globalPointsGL_iotaGL, _hinv]

  have hH : Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
      Φ (radicalP21 ![p.1, p.2] * g) *
        ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (v 0) * p.1 + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (v 1) * p.2)) := by
    refine (_hcont.comp (continuous_radicalP21_pair.mul continuous_const)).mul (_hψ.continuous.comp ?_)
    fun_prop
  have hper₁ : ∀ (β : ℚ) (z y : AdeleRing (𝓞 ℚ) ℚ),
      Φ (radicalP21 ![algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β + z, y] * g) *
          ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (v 0) * (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β + z) +
            algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (v 1) * y)) =
        Φ (radicalP21 ![z, y] * g) *
          ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (v 0) * z + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (v 1) * y)) := by
    intro β z y
    have hvec : (![algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β + z, y] : Fin 2 → AdeleRing (𝓞 ℚ) ℚ) =
        (fun i => algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (![β, 0] i)) + ![z, y] := by
      funext i
      fin_cases i <;> simp
    have hch : -(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (v 0) * (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β + z) +
          algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (v 1) * y) =
        algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (-(v 0 * β)) +
          -(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (v 0) * z + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (v 1) * y) := by
      simp only [map_neg, map_mul]
      ring
    have hpi : ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (-(v 0 * β))) = 1 := _hψ.principalInvariant _
    rw [hvec, radicalP21_add, mul_assoc, apply_radicalP21_algebraMap_mul Φ _hinv, hch, AddChar.map_add_eq_mul, hpi,
      one_mul]
  have hper₂ : ∀ (β : ℚ) (z y : AdeleRing (𝓞 ℚ) ℚ),
      Φ (radicalP21 ![z, algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β + y] * g) *
          ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (v 0) * z +
            algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (v 1) * (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β + y))) =
        Φ (radicalP21 ![z, y] * g) *
          ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (v 0) * z + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (v 1) * y)) := by
    intro β z y
    have hvec : (![z, algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β + y] : Fin 2 → AdeleRing (𝓞 ℚ) ℚ) =
        (fun i => algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (![0, β] i)) + ![z, y] := by
      funext i
      fin_cases i <;> simp
    have hch : -(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (v 0) * z +
          algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (v 1) * (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β + y)) =
        algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (-(v 1 * β)) +
          -(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (v 0) * z + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (v 1) * y) := by
      simp only [map_neg, map_mul]
      ring
    have hpi : ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (-(v 1 * β))) = 1 := _hψ.principalInvariant _
    rw [hvec, radicalP21_add, mul_assoc, apply_radicalP21_algebraMap_mul Φ _hinv, hch, AddChar.map_add_eq_mul, hpi,
      one_mul]
  have key := integral_integral_cond_adelicBox_comp_inv_mulVec_eq_of_periodic
    (fun z y => Φ (radicalP21 ![z, y] * g) *
      ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (v 0) * z + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (v 1) * y)))
    hH hper₁ hper₂ γ
  rw [← hM] at key
  simp only [hpt]
  exact key.symm

end S_LanglandsTunnell_CubicInduction_radicalCoefficient_eq_radicalCoefficient_psi_neg_iotaGL_globalPoints_mul
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_radicalCoefficient_eq_radicalCoefficient_psi_neg_iotaGL_globalPoints_mul (solution)
