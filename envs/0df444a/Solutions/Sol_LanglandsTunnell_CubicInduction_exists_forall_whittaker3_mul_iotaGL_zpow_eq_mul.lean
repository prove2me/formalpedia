-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/aa106220-f795-50ef-82a7-834f12ee6d3c

import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_RatIdele_Normalizer
import Theorems.Thm_LanglandsTunnell_CubicInduction_eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn
import Theorems.Thm_LanglandsTunnell_CubicInduction_sphericalTorusValue_eq_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
open Matrix IsDedekindDomain NumberField AutomorphicForm NumberField.StandardAddChar

namespace WhittakerTorusRecursion

open LanglandsTunnell.CubicInduction

section WhittakerTransport

open Matrix IsDedekindDomain NumberField AutomorphicForm

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

section Unipotent

private theorem upperUnipotent3_inv_coe' (x y z : AdeleRing (𝓞 ℚ) ℚ) :
    (((upperUnipotent3 x y z)⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      !![1, -x, x * y - z; 0, 1, -y; 0, 0, 1] :=
  rfl

private theorem continuous_upperUnipotent3 :
    Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
      (upperUnipotent3 p.1 p.2.1 p.2.2 : AdelicGL 3 (𝓞 ℚ) ℚ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    simp only [Function.comp_apply, upperUnipotent3_coe]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    simp only [upperUnipotent3_inv_coe']
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem continuous_radicalP21_pair :
    Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => (radicalP21 ![p.1, p.2] : AdelicGL 3 (𝓞 ℚ) ℚ) := by
  show Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => upperUnipotent3 0 p.2 p.1
  exact continuous_upperUnipotent3.comp
    (f := fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => ((0 : AdeleRing (𝓞 ℚ) ℚ), p.2, p.1)) (by fun_prop)

private theorem continuous_radicalP12_pair :
    Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => (radicalP12 ![p.1, p.2] : AdelicGL 3 (𝓞 ℚ) ℚ) := by
  show Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => upperUnipotent3 p.1 0 p.2
  exact continuous_upperUnipotent3.comp
    (f := fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => (p.1, (0 : AdeleRing (𝓞 ℚ) ℚ), p.2)) (by fun_prop)

end Unipotent

section Box

private scoped instance secondCountable_adeleRing : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ) :=
  NumberField.AdeleRing.secondCountableTopology ℚ

private abbrev boxMeasure : MeasureTheory.Measure (AdeleRing (𝓞 ℚ) ℚ) :=
  ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ)

private scoped instance isProbabilityMeasure_boxMeasure : MeasureTheory.IsProbabilityMeasure boxMeasure :=
  AdelicBox.isProbabilityMeasure_cond_adelicBox ℚ

private theorem integrable_boxMeasure_of_continuous {f : AdeleRing (𝓞 ℚ) ℚ → ℂ} (hf : Continuous f) :
    MeasureTheory.Integrable f boxMeasure := by
  obtain ⟨C, hC, hsub⟩ := AdelicBox.exists_isCompact_adelicBox_subset ℚ
  have h1 : MeasureTheory.IntegrableOn f C (AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) :=
    hf.continuousOn.integrableOn_compact hC
  have h2 : MeasureTheory.IntegrableOn f (AdelicBox.adelicBox ℚ) (AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) :=
    h1.mono_set hsub
  exact MeasureTheory.Integrable.smul_measure h2
    (ENNReal.inv_ne_top.mpr (AdelicBox.adelicAddHaar_adelicBox_pos ℚ).ne')

private theorem continuous_integral_boxMeasure {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [LocallyCompactSpace X] {f : X → AdeleRing (𝓞 ℚ) ℚ → ℂ} (hf : Continuous (Function.uncurry f)) :
    Continuous fun x => ∫ y, f x y ∂boxMeasure := by
  obtain ⟨C, hC, hsub⟩ := AdelicBox.exists_isCompact_adelicBox_subset ℚ
  refine continuous_iff_continuousAt.mpr fun x₀ => ?_
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds x₀
  obtain ⟨M, hM⟩ := (hK.prod hC).exists_bound_of_continuousOn hf.continuousOn
  refine MeasureTheory.continuousAt_of_dominated (bound := fun _ => M) ?_ ?_ (MeasureTheory.integrable_const M) ?_
  · exact Filter.Eventually.of_forall fun x =>
      (hf.comp (f := fun y => (x, y)) (by fun_prop)).aestronglyMeasurable
  · refine Filter.mem_of_superset hKn fun x hx => ?_
    exact (ProbabilityTheory.ae_cond_mem (AdelicBox.measurableSet_adelicBox ℚ)).mono fun y hy =>
      hM (x, y) ⟨hx, hsub hy⟩
  · exact Filter.Eventually.of_forall fun y => (hf.comp (f := fun x => (x, y)) (by fun_prop)).continuousAt

private theorem integral2_boxMeasure_add {φ φ' : AdeleRing (𝓞 ℚ) ℚ → AdeleRing (𝓞 ℚ) ℚ → ℂ}
    (hφ : Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => φ p.1 p.2)
    (hφ' : Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => φ' p.1 p.2) :
    (∫ x, ∫ y, (φ x y + φ' x y) ∂boxMeasure ∂boxMeasure) =
      (∫ x, ∫ y, φ x y ∂boxMeasure ∂boxMeasure) + ∫ x, ∫ y, φ' x y ∂boxMeasure ∂boxMeasure := by
  have hy : ∀ x, Continuous fun y => φ x y := fun x => hφ.comp (f := fun y => (x, y)) (by fun_prop)
  have hy' : ∀ x, Continuous fun y => φ' x y := fun x => hφ'.comp (f := fun y => (x, y)) (by fun_prop)
  have hx : Continuous fun x => ∫ y, φ x y ∂boxMeasure := continuous_integral_boxMeasure (f := φ) hφ
  have hx' : Continuous fun x => ∫ y, φ' x y ∂boxMeasure := continuous_integral_boxMeasure (f := φ') hφ'
  have hyadd : ∀ x, (∫ y, (φ x y + φ' x y) ∂boxMeasure) =
      (∫ y, φ x y ∂boxMeasure) + ∫ y, φ' x y ∂boxMeasure := fun x =>
    MeasureTheory.integral_add (integrable_boxMeasure_of_continuous (hy x))
      (integrable_boxMeasure_of_continuous (hy' x))
  simp_rw [hyadd]
  exact MeasureTheory.integral_add (integrable_boxMeasure_of_continuous hx) (integrable_boxMeasure_of_continuous hx')

private theorem integral3_boxMeasure_add
    {φ φ' : AdeleRing (𝓞 ℚ) ℚ → AdeleRing (𝓞 ℚ) ℚ → AdeleRing (𝓞 ℚ) ℚ → ℂ}
    (hφ : Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => φ p.1 p.2.1 p.2.2)
    (hφ' : Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => φ' p.1 p.2.1 p.2.2) :
    (∫ x, ∫ y, ∫ z, (φ x y z + φ' x y z) ∂boxMeasure ∂boxMeasure ∂boxMeasure) =
      (∫ x, ∫ y, ∫ z, φ x y z ∂boxMeasure ∂boxMeasure ∂boxMeasure) +
        ∫ x, ∫ y, ∫ z, φ' x y z ∂boxMeasure ∂boxMeasure ∂boxMeasure := by
  have hz : ∀ x y, Continuous fun z => φ x y z := fun x y => hφ.comp (f := fun z => (x, y, z)) (by fun_prop)
  have hz' : ∀ x y, Continuous fun z => φ' x y z := fun x y => hφ'.comp (f := fun z => (x, y, z)) (by fun_prop)
  have hzadd : ∀ x y, (∫ z, (φ x y z + φ' x y z) ∂boxMeasure) =
      (∫ z, φ x y z ∂boxMeasure) + ∫ z, φ' x y z ∂boxMeasure := fun x y =>
    MeasureTheory.integral_add (integrable_boxMeasure_of_continuous (hz x y))
      (integrable_boxMeasure_of_continuous (hz' x y))
  simp_rw [hzadd]
  have h1 : Continuous fun q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => ∫ z, φ q.1 q.2 z ∂boxMeasure :=
    continuous_integral_boxMeasure
      (f := fun (q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) (z : AdeleRing (𝓞 ℚ) ℚ) => φ q.1 q.2 z)
      (hφ.comp (f := fun r : (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ => (r.1.1, r.1.2, r.2))
        (by fun_prop))
  have h1' : Continuous fun q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => ∫ z, φ' q.1 q.2 z ∂boxMeasure :=
    continuous_integral_boxMeasure
      (f := fun (q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) (z : AdeleRing (𝓞 ℚ) ℚ) => φ' q.1 q.2 z)
      (hφ'.comp (f := fun r : (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ => (r.1.1, r.1.2, r.2))
        (by fun_prop))
  exact integral2_boxMeasure_add (φ := fun x y => ∫ z, φ x y z ∂boxMeasure)
    (φ' := fun x y => ∫ z, φ' x y z ∂boxMeasure) h1 h1'

end Box

section Pins

variable (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
  (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)

private abbrev prodPins : CarrierPins ℚ := productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)

variable {D U gen}

section Whittaker

variable (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) {F F' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}

private theorem continuous_whittakerIntegrand (hψ : Continuous ψ) (hF : Continuous F) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
      F (upperUnipotent3 p.1 p.2.1 p.2.2 * g) * ψ (-(p.1 + p.2.1)) :=
  (hF.comp (continuous_upperUnipotent3.mul continuous_const)).mul (hψ.comp (by fun_prop))

private theorem whittaker3_prodPins_add (hψ : Continuous ψ) (hF : Continuous F) (hF' : Continuous F')
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 (prodPins D U gen) ψ (F + F') g =
      whittaker3 (prodPins D U gen) ψ F g + whittaker3 (prodPins D U gen) ψ F' g := by
  have h := integral3_boxMeasure_add
    (φ := fun x y z => F (upperUnipotent3 x y z * g) * ψ (-(x + y)))
    (φ' := fun x y z => F' (upperUnipotent3 x y z * g) * ψ (-(x + y)))
    (continuous_whittakerIntegrand ψ hψ hF g) (continuous_whittakerIntegrand ψ hψ hF' g)
  simp only [whittaker3, Pi.add_apply, add_mul]
  exact h

private theorem whittaker3_smul (pins : CarrierPins ℚ) (c : ℂ) (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 pins ψ (c • F) g = c * whittaker3 pins ψ F g := by
  simp only [whittaker3, Pi.smul_apply, smul_eq_mul, mul_assoc, MeasureTheory.integral_const_mul]

private theorem whittaker3_zero (pins : CarrierPins ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 pins ψ (0 : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) g = 0 := by
  simp [whittaker3]

end Whittaker

end Pins

open NumberField.AdelicHaar MeasureTheory
open scoped ProbabilityTheory Pointwise

local notation "μbox" =>
  ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ)

section BoxShift

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

private theorem integral_box_comp_add_right {f : AdeleRing (𝓞 ℚ) ℚ → ℂ}
    (hf : ∀ (α : ℚ) (y : AdeleRing (𝓞 ℚ) ℚ), f (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α + y) = f y)
    (s : AdeleRing (𝓞 ℚ) ℚ) :
    ∫ y, f (y + s) ∂μbox = ∫ y, f y ∂μbox := by
  rw [ProbabilityTheory.cond, integral_smul_measure, integral_smul_measure, setIntegral_adelicBox_comp_add_right hf s]

end BoxShift

section Unipotent

variable {A : Type*} [CommRing A]

private theorem upperUnipotent3_mul_upperUnipotent3 (x y z x' y' z' : A) :
    upperUnipotent3 x y z * upperUnipotent3 x' y' z' = upperUnipotent3 (x + x') (y + y') (z + z' + x * y') := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

end Unipotent

section Law

variable (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
  (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)

private theorem whittaker3_productionPinsOf_eq (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ Φ g =
      ∫ x, ∫ y, ∫ z, Φ (upperUnipotent3 x y z * g) * ψ (-(x + y)) ∂μbox ∂μbox ∂μbox := rfl

variable {D U gen}

private theorem whittaker3_upperUnipotent3_mul {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ}
    (hψ : ∀ q : ℚ, ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q) = 1) {Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hΦ : ∀ (q₁ q₂ q₃ : ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      Φ (upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q₁) (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q₂)
        (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q₃) * g) = Φ g)
    (a b c : AdeleRing (𝓞 ℚ) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ Φ (upperUnipotent3 a b c * g) =
      ψ (a + b) * whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ Φ g := by

  set G : AdeleRing (𝓞 ℚ) ℚ → AdeleRing (𝓞 ℚ) ℚ → ℂ := fun x y => ∫ z, Φ (upperUnipotent3 x y z * g) ∂μbox
    with hG
  have h0 : algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) 0 = 0 := map_zero _

  have hz : ∀ (x y : AdeleRing (𝓞 ℚ) ℚ) (q : ℚ) (z : AdeleRing (𝓞 ℚ) ℚ),
      Φ (upperUnipotent3 x y (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + z) * g) = Φ (upperUnipotent3 x y z * g) := by
    intro x y q z
    have e : upperUnipotent3 x y (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + z) =
        upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) 0) (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) 0)
          (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q) * upperUnipotent3 x y z := by
      rw [upperUnipotent3_mul_upperUnipotent3, h0]
      congr 1 <;> ring
    rw [e, mul_assoc, hΦ]

  have hGy : ∀ (x : AdeleRing (𝓞 ℚ) ℚ) (q : ℚ) (y : AdeleRing (𝓞 ℚ) ℚ),
      G x (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + y) = G x y := by
    intro x q y
    simp only [hG]
    congr 1
    funext z
    have e : upperUnipotent3 x (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + y) z =
        upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) 0) (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q)
          (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) 0) * upperUnipotent3 x y z := by
      rw [upperUnipotent3_mul_upperUnipotent3, h0]
      congr 1 <;> ring
    rw [e, mul_assoc, hΦ]

  have hGx : ∀ (q : ℚ) (x y : AdeleRing (𝓞 ℚ) ℚ), G (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + x) y = G x y := by
    intro q x y
    simp only [hG]
    have e : ∀ z : AdeleRing (𝓞 ℚ) ℚ, upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + x) y z =
        upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q) (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) 0)
          (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) 0) *
            upperUnipotent3 x y (z + -(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q * y)) := by
      intro z
      rw [upperUnipotent3_mul_upperUnipotent3, h0]
      congr 1 <;> ring
    calc ∫ z, Φ (upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + x) y z * g) ∂μbox
        = ∫ z, Φ (upperUnipotent3 x y (z + -(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q * y)) * g) ∂μbox := by
          congr 1
          funext z
          rw [e z, mul_assoc, hΦ]
      _ = ∫ z, Φ (upperUnipotent3 x y z * g) ∂μbox :=
          integral_box_comp_add_right (f := fun z => Φ (upperUnipotent3 x y z * g)) (hz x y) _

  have h1 : ∀ x y : AdeleRing (𝓞 ℚ) ℚ,
      (∫ z, Φ (upperUnipotent3 x y z * (upperUnipotent3 a b c * g)) * ψ (-(x + y)) ∂μbox) =
        G (x + a) (y + b) * ψ (-(x + y)) := by
    intro x y
    rw [integral_mul_const]
    congr 1
    calc ∫ z, Φ (upperUnipotent3 x y z * (upperUnipotent3 a b c * g)) ∂μbox
        = ∫ z, Φ (upperUnipotent3 (x + a) (y + b) (z + (c + x * b)) * g) ∂μbox := by
          congr 1
          funext z
          rw [← mul_assoc, upperUnipotent3_mul_upperUnipotent3, add_assoc]
      _ = G (x + a) (y + b) :=
          integral_box_comp_add_right (f := fun z => Φ (upperUnipotent3 (x + a) (y + b) z * g)) (hz (x + a) (y + b)) _

  have h2 : ∀ x : AdeleRing (𝓞 ℚ) ℚ,
      (∫ y, G (x + a) (y + b) * ψ (-(x + y)) ∂μbox) = ψ b * ∫ y, G (x + a) y * ψ (-(x + y)) ∂μbox := by
    intro x
    have hper : ∀ (q : ℚ) (y : AdeleRing (𝓞 ℚ) ℚ),
        G (x + a) (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + y) * ψ (-(x + (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + y))) =
          G (x + a) y * ψ (-(x + y)) := by
      intro q y
      rw [hGy]
      congr 1
      have : -(x + (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + y)) = algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (-q) + -(x + y) := by
        rw [map_neg]
        ring
      rw [this, AddChar.map_add_eq_mul, hψ, one_mul]
    calc ∫ y, G (x + a) (y + b) * ψ (-(x + y)) ∂μbox
        = ∫ y, G (x + a) (y + b) * ψ (-(x + (y + b))) * ψ b ∂μbox := by
          congr 1
          funext y
          rw [mul_assoc, ← AddChar.map_add_eq_mul]
          congr 2
          ring
      _ = (∫ y, G (x + a) y * ψ (-(x + y)) ∂μbox) * ψ b := by
          rw [← integral_mul_const]
          exact integral_box_comp_add_right (f := fun y => G (x + a) y * ψ (-(x + y)) * ψ b)
            (fun q y => by beta_reduce; rw [hper]) b
      _ = ψ b * ∫ y, G (x + a) y * ψ (-(x + y)) ∂μbox := mul_comm _ _

  have h3 : (∫ x, ψ b * ∫ y, G (x + a) y * ψ (-(x + y)) ∂μbox ∂μbox) =
      ψ b * (ψ a * ∫ x, ∫ y, G x y * ψ (-(x + y)) ∂μbox ∂μbox) := by
    rw [integral_const_mul]
    congr 1
    have hper : ∀ (q : ℚ) (x : AdeleRing (𝓞 ℚ) ℚ),
        (∫ y, G (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + x) y * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + x + y))
          ∂μbox) = ∫ y, G x y * ψ (-(x + y)) ∂μbox := by
      intro q x
      congr 1
      funext y
      rw [hGx]
      congr 1
      have : -(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + x + y) = algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (-q) + -(x + y) := by
        rw [map_neg]
        ring
      rw [this, AddChar.map_add_eq_mul, hψ, one_mul]
    calc ∫ x, ∫ y, G (x + a) y * ψ (-(x + y)) ∂μbox ∂μbox
        = ∫ x, (∫ y, G (x + a) y * ψ (-(x + a + y)) ∂μbox) * ψ a ∂μbox := by
          congr 1
          funext x
          rw [← integral_mul_const]
          congr 1
          funext y
          rw [mul_assoc, ← AddChar.map_add_eq_mul]
          congr 2
          ring
      _ = (∫ x, ∫ y, G x y * ψ (-(x + y)) ∂μbox ∂μbox) * ψ a := by
          rw [← integral_mul_const]
          exact integral_box_comp_add_right
            (f := fun x => (∫ y, G x y * ψ (-(x + y)) ∂μbox) * ψ a) (fun q x => by beta_reduce; rw [hper]) a
      _ = ψ a * ∫ x, ∫ y, G x y * ψ (-(x + y)) ∂μbox ∂μbox := mul_comm _ _

  have hW : whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ Φ g =
      ∫ x, ∫ y, G x y * ψ (-(x + y)) ∂μbox ∂μbox := by
    rw [whittaker3_productionPinsOf_eq]
    congr 1
    funext x
    congr 1
    funext y
    rw [integral_mul_const]
  rw [whittaker3_productionPinsOf_eq]
  calc ∫ x, ∫ y, ∫ z, Φ (upperUnipotent3 x y z * (upperUnipotent3 a b c * g)) * ψ (-(x + y)) ∂μbox ∂μbox ∂μbox
      = ∫ x, ∫ y, G (x + a) (y + b) * ψ (-(x + y)) ∂μbox ∂μbox := by
        congr 1
        funext x
        congr 1
        funext y
        exact h1 x y
    _ = ∫ x, ψ b * ∫ y, G (x + a) y * ψ (-(x + y)) ∂μbox ∂μbox := by
        congr 1
        funext x
        exact h2 x
    _ = ψ b * (ψ a * ∫ x, ∫ y, G x y * ψ (-(x + y)) ∂μbox ∂μbox) := h3
    _ = ψ (a + b) * whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ Φ g := by
        rw [hW, ← mul_assoc, ← AddChar.map_add_eq_mul, add_comm b a]

end Law

section Transport

variable (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)

private theorem globalPointsGL_upperUnipotent3 (q₁ q₂ q₃ : ℚ) :
    globalPointsGL 3 (𝓞 ℚ) ℚ (upperUnipotent3 q₁ q₂ q₃) =
      upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q₁) (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q₂)
        (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q₃) := by
  refine Units.ext ?_
  ext i j
  simp only [globalPointsGL, Matrix.GeneralLinearGroup.map, Units.coe_map, upperUnipotent3_coe]
  fin_cases i <;> fin_cases j <;> simp

variable {D : Set (AdelicGL2 (𝓞 ℚ) ℚ)} {U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)}
  {gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ}

private theorem whittaker3_upperUnipotent3_mul_of_globalPointsGL {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ}
    (hψ : ∀ q : ℚ, ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q) = 1) {Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      Φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = Φ g)
    (a b c : AdeleRing (𝓞 ℚ) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 (prodPins D U gen) ψ Φ (upperUnipotent3 a b c * g) =
      ψ (a + b) * whittaker3 (prodPins D U gen) ψ Φ g :=
  whittaker3_upperUnipotent3_mul hψ
    (fun q₁ q₂ q₃ g' => by rw [← globalPointsGL_upperUnipotent3]; exact haut _ g') a b c g

private theorem whittaker3_mul_right (pins : CarrierPins ℚ) (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (g r : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 pins ψ F (g * r) = whittaker3 pins ψ (fun h => F (h * r)) g := by
  simp only [whittaker3, mul_assoc]

private theorem isRightInvariant_whittaker3 (pins : CarrierPins ℚ) {V : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ)}
    {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : IsRightInvariant V F) :
    IsRightInvariant V (whittaker3 pins ψ F) := by
  intro g u hu
  rw [whittaker3_mul_right]
  exact congrArg (fun Φ => whittaker3 pins ψ Φ g) (funext fun h => hF h u hu)

private theorem whittaker3_centralScalarGL_mul (pins : CarrierPins ℚ) {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    {ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ}
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      F (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * F g)
    (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 pins ψ F (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * whittaker3 pins ψ F g := by
  have hcomm : ∀ n : AdelicGL 3 (𝓞 ℚ) ℚ,
      n * centralScalarGL 3 (𝓞 ℚ) ℚ z = centralScalarGL 3 (𝓞 ℚ) ℚ z * n := by
    intro n
    refine Units.ext ?_
    show (n : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) *
        Matrix.scalar (Fin 3) (z : AdeleRing (𝓞 ℚ) ℚ) =
      Matrix.scalar (Fin 3) (z : AdeleRing (𝓞 ℚ) ℚ) * (n : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))
    exact ((Matrix.scalar_commute (z : AdeleRing (𝓞 ℚ) ℚ) (fun r' => Commute.all _ r') _).eq).symm
  have hpt : ∀ x y w : AdeleRing (𝓞 ℚ) ℚ,
      F (upperUnipotent3 x y w * (centralScalarGL 3 (𝓞 ℚ) ℚ z * g)) * ψ (-(x + y)) =
        (ω z : ℂ) * (F (upperUnipotent3 x y w * g) * ψ (-(x + y))) := by
    intro x y w
    rw [← mul_assoc, hcomm, mul_assoc, hcen, mul_assoc]
  simp only [whittaker3, hpt, MeasureTheory.integral_const_mul]

variable {D : Set (AdelicGL2 (𝓞 ℚ) ℚ)} {U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)}
  {gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ}

private theorem whittaker3_prodPins_finset_sum {ι : Type*} (s : Finset ι) (Fs : ι → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hψ : Continuous ψ) (hFs : ∀ i, Continuous (Fs i)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 (prodPins D U gen) ψ (∑ i ∈ s, Fs i) g =
      ∑ i ∈ s, whittaker3 (prodPins D U gen) ψ (Fs i) g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact whittaker3_zero ψ (prodPins D U gen) g
  | insert i s hi ih =>
    have hsum : Continuous (∑ j ∈ s, Fs j) := by
      have heq : (∑ j ∈ s, Fs j) = fun h => ∑ j ∈ s, Fs j h := by
        funext h
        exact Finset.sum_apply h s Fs
      rw [heq]
      exact continuous_finsetSum s fun j _ => hFs j
    rw [Finset.sum_insert hi, Finset.sum_insert hi, whittaker3_prodPins_add ψ hψ (hFs i) hsum g, ih]

private theorem isCosetEigenfunction_whittaker3 {V : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ)} {t : AdelicGL 3 (𝓞 ℚ) ℚ}
    {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} {lam : ℂ} (hψ : Continuous ψ) (hF : Continuous F)
    (hT : IsCosetEigenfunction V t F lam) : IsCosetEigenfunction V t (whittaker3 (prodPins D U gen) ψ F) lam := by
  intro κ _ reps hsys g
  have h1 : cosetSum reps (whittaker3 (prodPins D U gen) ψ F) g =
      ∑ i, whittaker3 (prodPins D U gen) ψ (fun h => F (h * reps i)) g := by
    show (∑ i, whittaker3 (prodPins D U gen) ψ F (g * reps i)) = _
    exact Finset.sum_congr rfl fun i _ => whittaker3_mul_right ψ (prodPins D U gen) F g (reps i)
  have h2 : (∑ i ∈ Finset.univ, fun h => F (h * reps i)) = lam • F := by
    funext h
    rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact hT κ reps hsys h
  rw [h1, ← whittaker3_prodPins_finset_sum ψ Finset.univ (fun i h => F (h * reps i)) hψ
    (fun i => hF.comp (continuous_mul_const (reps i))) g, h2, whittaker3_smul]

end Transport

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell.CubicInduction"
end WhittakerTransport
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell.CubicInduction"

section SliceDescent

open IsDedekindDomain NumberField NumberField.StandardAddChar

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction

section CosetSystemMap

variable {G H : Type*} [Group G] [Group H]

private theorem mem_doubleCoset_map (f : G →* H) (U : Subgroup G) (g : G) {x : G}
    (hx : x ∈ HeckePair.doubleCoset U g) : f x ∈ HeckePair.doubleCoset (U.map f) (f g) := by
  obtain ⟨u, hu, u', hu', rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  exact HeckePair.mem_doubleCoset_iff.mpr
    ⟨f u, Subgroup.mem_map_of_mem f hu, f u', Subgroup.mem_map_of_mem f hu', by simp [map_mul]⟩

private theorem exists_of_mem_doubleCoset_map (f : G →* H) (U : Subgroup G) (g : G) {y : H}
    (hy : y ∈ HeckePair.doubleCoset (U.map f) (f g)) :
    ∃ x ∈ HeckePair.doubleCoset U g, f x = y := by
  obtain ⟨a, ha, b, hb, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hy
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.mp hb
  exact ⟨u * g * u', HeckePair.mem_doubleCoset_iff.mpr ⟨u, hu, u', hu', rfl⟩, by simp [map_mul]⟩

private theorem mk_map_eq_of_mk_eq (f : G →* H) (U : Subgroup G) {x x' : G}
    (h : (QuotientGroup.mk x : G ⧸ U) = QuotientGroup.mk x') :
    (QuotientGroup.mk (f x) : H ⧸ U.map f) = QuotientGroup.mk (f x') := by
  rw [QuotientGroup.eq] at h ⊢
  rw [← map_inv, ← map_mul]
  exact Subgroup.mem_map_of_mem f h

private theorem mk_eq_of_mk_map_eq {f : G →* H} (hf : Function.Injective f) (U : Subgroup G) {x x' : G}
    (h : (QuotientGroup.mk (f x) : H ⧸ U.map f) = QuotientGroup.mk (f x')) :
    (QuotientGroup.mk x : G ⧸ U) = QuotientGroup.mk x' := by
  rw [QuotientGroup.eq] at h ⊢
  rw [← map_inv, ← map_mul] at h
  obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp h
  rwa [← hf hux]

namespace IsHeckeCosetSystem
private theorem _root_.WhittakerTorusRecursion.LanglandsTunnell.CubicInduction.IsHeckeCosetSystem.map {f : G →* H} (hf : Function.Injective f) {U : Subgroup G} {g : G}
    {ι : Type*} {reps : ι → G} (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U g reps) :
    HeckeIntegralSeam.IsHeckeCosetSystem (U.map f) (f g) (fun i => f (reps i)) where
  mem_doubleCoset i := mem_doubleCoset_map f U g (hsys.mem_doubleCoset i)
  covers y hy := by
    obtain ⟨x, hx, rfl⟩ := exists_of_mem_doubleCoset_map f U g hy
    obtain ⟨i, hi⟩ := hsys.covers x hx
    exact ⟨i, mk_map_eq_of_mk_eq f U hi⟩
  mk_injective i j hij := hsys.mk_injective (mk_eq_of_mk_map_eq hf U hij)

end IsHeckeCosetSystem
p2m_export "WhittakerTorusRecursion.LanglandsTunnell.CubicInduction" "IsHeckeCosetSystem.map"
end CosetSystemMap
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell.CubicInduction"

section Injective

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem localToAdelic3_injective : Function.Injective (localToAdelic3 v) := by
  intro a b hab
  have h := congrArg (fun x : AdelicGL 3 (𝓞 ℚ) ℚ =>
    (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v).mapMatrix ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix
      (x : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)))) hab
  change (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v).mapMatrix ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix
      (finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ v (a : Matrix (Fin 3) (Fin 3) _)))) =
    (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v).mapMatrix ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix
      (finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ v (b : Matrix (Fin 3) (Fin 3) _)))) at h
  rw [mapMatrix_fin_finMatN, mapMatrix_fin_finMatN, mapMatrix_localMatN_self,
    mapMatrix_localMatN_self] at h
  exact Units.ext h

end Injective
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell.CubicInduction"

section Slice

variable (v : HeightOneSpectrum (𝓞 ℚ))

private def sliceAt (g₀ : AdelicGL 3 (𝓞 ℚ) ℚ) (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (h : LocalGL3 v) : ℂ :=
  W (g₀ * localToAdelic3 v h)

variable {v}

private theorem sliceAt_one (g₀ : AdelicGL 3 (𝓞 ℚ) ℚ) (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    sliceAt v g₀ W 1 = W g₀ := by
  simp [sliceAt]

private theorem isRightInvariant_sliceAt {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hK : IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ v).map (localToAdelic3 v)) W)
    (g₀ : AdelicGL 3 (𝓞 ℚ) ℚ) : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) (sliceAt v g₀ W) := by
  intro h k hk
  simp only [sliceAt, map_mul, ← mul_assoc]
  exact hK _ _ (Subgroup.mem_map_of_mem _ hk)

private theorem sliceAt_centralGen_mul {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} {ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ}
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      W (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * W g)
    {g₀ : AdelicGL 3 (𝓞 ℚ) ℚ} (hg₀ : ∀ x : LocalGL3 v, g₀ * localToAdelic3 v x = localToAdelic3 v x * g₀)
    {ζ : (AdeleRing (𝓞 ℚ) ℚ)ˣ} (hζ : localToAdelic3 v (centralGen v) = centralScalarGL 3 (𝓞 ℚ) ℚ ζ)
    (h : LocalGL3 v) : sliceAt v g₀ W (centralGen v * h) = (ω ζ : ℂ) * sliceAt v g₀ W h := by
  simp only [sliceAt, map_mul]
  rw [← mul_assoc, hg₀, mul_assoc, hζ, hcen]

private theorem isCosetEigenfunction_sliceAt {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} {gen : LocalGL3 v} {lam : ℂ}
    (hT : IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ v).map (localToAdelic3 v))
      (localToAdelic3 v gen) W lam) (g₀ : AdelicGL 3 (𝓞 ℚ) ℚ) :
    IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) gen (sliceAt v g₀ W) lam := by
  intro ι _ reps hsys h
  have key := hT ι (fun i => localToAdelic3 v (reps i))
    (IsHeckeCosetSystem.map (localToAdelic3_injective v) hsys) (g₀ * localToAdelic3 v h)
  simp only [cosetSum, sliceAt, map_mul, mul_assoc] at key ⊢
  exact key

private theorem localToAdelic3_upperUnipotent3 (x y z : v.adicCompletion ℚ) :
    localToAdelic3 v (upperUnipotent3 x y z) =
      upperUnipotent3 (adeleSingleAt ℚ v x) (adeleSingleAt ℚ v y) (adeleSingleAt ℚ v z) := by
  apply Units.ext
  refine matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ ?_ ?_
  · change (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (finMatN (Fin 3) (𝓞 ℚ) ℚ _) = _
    rw [mapMatrix_arch_finMatN]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [RingHom.mapMatrix_apply, Matrix.map_apply, adeleSingleAt_apply, AdelicLevel.adeleArch_apply,
        upperUnipotent3_coe] <;> rfl
  · change (AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (finMatN (Fin 3) (𝓞 ℚ) ℚ
        (localMatN (Fin 3) (𝓞 ℚ) ℚ v (upperUnipotent3 x y z : Matrix (Fin 3) (Fin 3) _))) = _
    rw [mapMatrix_fin_finMatN]
    refine matrixFin_ext (Fin 3) (𝓞 ℚ) ℚ fun w => ?_
    by_cases hw : w = v
    · subst hw
      rw [mapMatrix_localMatN_self]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [RingHom.mapMatrix_apply, Matrix.map_apply, adeleSingleAt_apply, AdelicLevel.adeleFin_apply,
          AdelicLevel.finAdeleEval_apply, finAdeleSingleAt_apply_self, upperUnipotent3_coe] <;> rfl
    · rw [mapMatrix_localMatN_of_ne (Fin 3) (𝓞 ℚ) ℚ v _ hw]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [RingHom.mapMatrix_apply, Matrix.map_apply, adeleSingleAt_apply, AdelicLevel.adeleFin_apply,
          AdelicLevel.finAdeleEval_apply, finAdeleSingleAt_apply_of_ne _ _ _ hw, upperUnipotent3_coe] <;> rfl

private theorem isGL3PsiWhittakerFn_sliceAt {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hψ : IsGL3PsiWhittakerFn ψ W) {g₀ : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hg₀ : ∀ x : LocalGL3 v, g₀ * localToAdelic3 v x = localToAdelic3 v x * g₀) :
    IsGL3PsiWhittakerFn (psiLoc ψ v) (sliceAt v g₀ W) := by
  intro x y z h
  simp only [sliceAt, map_mul]
  rw [← mul_assoc, hg₀, mul_assoc, localToAdelic3_upperUnipotent3, hψ]
  simp [psiLoc, map_add]

end Slice
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell.CubicInduction"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell.CubicInduction"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell.CubicInduction"
end SliceDescent
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell.CubicInduction"

section TorusPoints

open IsDedekindDomain NumberField Matrix

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem twoRowPointLocal_coe (k₁ k₂ : ℕ) :
    (twoRowPointLocal v k₁ k₂ : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![ratPrimeAt v ^ k₁, ratPrimeAt v ^ k₂, 1] := by
  rw [twoRowPointLocal, coe_iotaGL, coe_diagUnits2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, ratPrimeUnit, Matrix.diagonal]

private theorem iotaTorusLocal_coe (n : ℕ) :
    (iotaTorusLocal v n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![ratPrimeAt v ^ n, 1, 1] := by
  rw [← twoRowPointLocal_zero_right, twoRowPointLocal_coe, pow_zero]

variable {v}

private theorem eq_twoRowPointLocal_of_coe_eq {t : LocalGL3 v} {k₁ k₂ : ℕ}
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![ratPrimeAt v ^ k₁, ratPrimeAt v ^ k₂, 1]) :
    t = twoRowPointLocal v k₁ k₂ :=
  Units.ext (ht.trans (twoRowPointLocal_coe v k₁ k₂).symm)

private theorem ratPrimeUnit_zpow_of_nonneg {m : ℤ} (hm : 0 ≤ m) :
    ratPrimeUnit v ^ m = ratPrimeUnit v ^ m.toNat := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  simp

private theorem coe_ratPrimeUnit_zpow (m : ℤ) :
    ((ratPrimeUnit v ^ m : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = ratPrimeAt v ^ m := by
  simp [ratPrimeUnit]

private theorem eq_twoRowPointLocal_toNat_of_coe_eq {t : LocalGL3 v} {m : ℤ × ℤ} (hm : 0 ≤ m.2)
    (hm' : 0 ≤ m.1)
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![((ratPrimeUnit v ^ m.1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ),
        ((ratPrimeUnit v ^ m.2 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ), 1]) :
    t = twoRowPointLocal v m.1.toNat m.2.toNat := by
  apply eq_twoRowPointLocal_of_coe_eq
  rw [ht, ratPrimeUnit_zpow_of_nonneg hm', ratPrimeUnit_zpow_of_nonneg hm]
  simp [ratPrimeUnit]

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell.CubicInduction"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell.CubicInduction"
end TorusPoints
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell.CubicInduction"

section CentreImage

open IsDedekindDomain NumberField NumberField.AdelicLevel AutomorphicForm

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem centralGen_coe :
    (centralGen v : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal fun _ => varpi v := by
  show Matrix.diagonal ![varpi v, varpi v, varpi v] = _
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem localToAdelic3_centralGen :
    localToAdelic3 v (centralGen v) = centralScalarGL 3 (𝓞 ℚ) ℚ (uniformizerIdele ℚ v) := by
  apply Units.ext
  refine matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ ?_ ?_
  · change (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (finMatN (Fin 3) (𝓞 ℚ) ℚ _) = _
    rw [mapMatrix_arch_finMatN]
    ext i j
    by_cases h : i = j <;>
      simp [h, centralScalarGL, uniformizerIdele, RingHom.mapMatrix_apply, Matrix.map_apply,
        AdelicLevel.adeleArch_apply, Matrix.one_apply, finIncl_apply_fst]
    rfl
  · change (AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (finMatN (Fin 3) (𝓞 ℚ) ℚ
        (localMatN (Fin 3) (𝓞 ℚ) ℚ v (centralGen v : Matrix (Fin 3) (Fin 3) _))) = _
    rw [mapMatrix_fin_finMatN]
    refine matrixFin_ext (Fin 3) (𝓞 ℚ) ℚ fun w => ?_
    by_cases hw : w = v
    · subst hw
      rw [mapMatrix_localMatN_self, centralGen_coe]
      ext i j
      by_cases h : i = j <;>
        simp [h, centralScalarGL, uniformizerIdele, varpi, RingHom.mapMatrix_apply, Matrix.map_apply,
          AdelicLevel.adeleFin_apply, AdelicLevel.finAdeleEval_apply, finIncl_apply_snd, localUnit_apply_self]
      rfl
    · rw [mapMatrix_localMatN_of_ne (Fin 3) (𝓞 ℚ) ℚ v _ hw]
      ext i j
      by_cases h : i = j <;>
        simp [h, centralScalarGL, uniformizerIdele, RingHom.mapMatrix_apply, Matrix.map_apply,
          AdelicLevel.adeleFin_apply, AdelicLevel.finAdeleEval_apply, Matrix.one_apply, finIncl_apply_snd,
          localUnit_apply_of_ne (𝓞 ℚ) ℚ v _ hw]
      rfl

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell.CubicInduction"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell.CubicInduction"
end CentreImage
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell.CubicInduction"

section TorusTable

open Matrix IsDedekindDomain NumberField

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction

open RatIdele Rat.HeightOneSpectrum in

private theorem absNorm_asIdeal_eq_natGenerator (v : HeightOneSpectrum (𝓞 ℚ)) :
    Ideal.absNorm v.asIdeal = natGenerator v := by
  rw [asIdeal_eq_span_natGenerator, Ideal.absNorm_span_singleton,
    show ((natGenerator v : ℕ) : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) (natGenerator v : ℕ) from (map_natCast _ _).symm,
    Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one]
  simp

open RatIdele Rat.HeightOneSpectrum in

private theorem valued_ratPrimeAt (v : HeightOneSpectrum (𝓞 ℚ)) : Valued.v (ratPrimeAt v) = WithZero.exp (-1 : ℤ) := by
  unfold ratPrimeAt
  rw [absNorm_asIdeal_eq_natGenerator, ← map_natCast (algebraMap ℚ (v.adicCompletion ℚ)) (natGenerator v : ℕ),
    valued_algebraMap_rat]
  exact valuation_natGenerator v

private theorem valued_ratPrimeAt_zpow (v : HeightOneSpectrum (𝓞 ℚ)) (m : ℤ) :
    Valued.v (ratPrimeAt v ^ m) = WithZero.exp (-m) := by
  rw [map_zpow₀, valued_ratPrimeAt, ← WithZero.exp_zsmul]
  congr 1
  simp

private def torusValueTable (N e₁ e₂ e₃ : ℂ) (m : ℤ × ℤ) : ℂ :=
  if 0 ≤ m.2 ∧ m.2 ≤ m.1 then
    match m.2.toNat with
    | 0 => N⁻¹ ^ m.1.toNat * sphericalTorusValue e₁ e₂ e₃ m.1.toNat
    | k₂ + 1 =>
      N⁻¹ ^ m.1.toNat *
        (sphericalTorusValue e₁ e₂ e₃ m.1.toNat * sphericalTorusValue e₁ e₂ e₃ (k₂ + 1) -
          sphericalTorusValue e₁ e₂ e₃ (m.1.toNat + 1) * sphericalTorusValue e₁ e₂ e₃ k₂)
  else 0

private theorem torusValueTable_zero (N e₁ e₂ e₃ : ℂ) : torusValueTable N e₁ e₂ e₃ (0, 0) = 1 := by
  simp [torusValueTable, sphericalTorusValue]

private theorem torusValueTable_of_not_dominant (N e₁ e₂ e₃ : ℂ) {m : ℤ × ℤ} (hm : ¬ (0 ≤ m.2 ∧ m.2 ≤ m.1)) :
    torusValueTable N e₁ e₂ e₃ m = 0 := by
  simp [torusValueTable, hm]

private theorem isCosetEigenfunction_cNormQ_mul_div {v : HeightOneSpectrum (𝓞 ℚ)} (hN : cNormQ v ≠ 0)
    {U : Subgroup (LocalGL3 v)} {gen : LocalGL3 v} {W : LocalGL3 v → ℂ} {lam : ℂ}
    (h : IsCosetEigenfunction U gen W lam) : IsCosetEigenfunction U gen W (cNormQ v * (lam / cNormQ v)) := by
  rwa [mul_div_cancel₀ lam hN]

variable {v : HeightOneSpectrum (𝓞 ℚ)}

private theorem pointOfCone {t : LocalGL3 v} {m : ℤ × ℤ} (hm : 0 ≤ m.2 ∧ m.2 ≤ m.1)
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![ratPrimeAt v ^ m.1, ratPrimeAt v ^ m.2, 1]) :
    t = twoRowPointLocal v m.1.toNat m.2.toNat := by
  apply Units.ext
  rw [ht]
  unfold twoRowPointLocal
  rw [coe_iotaGL, coe_diagUnits2]
  have h1 : ratPrimeAt v ^ m.1 = ratPrimeAt v ^ m.1.toNat := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (le_trans hm.1 hm.2)]
  have h2 : ratPrimeAt v ^ m.2 = ratPrimeAt v ^ m.2.toNat := by
    rw [← zpow_natCast, Int.toNat_of_nonneg hm.1]
  rw [h1, h2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, ratPrimeUnit, Matrix.diagonal]

private theorem eq_mul_torusValueTable_of_conclusions (W : LocalGL3 v → ℂ) (e₁ e₂ e₃ : ℂ)
    (hsupp : ∀ (t : LocalGL3 v) (d : Fin 3 → v.adicCompletion ℚ),
      (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d →
        (Valued.v (d 1) < Valued.v (d 0) ∨ Valued.v (d 2) < Valued.v (d 1)) → W t = 0)
    (huniq : (∀ n : ℕ, W (iotaTorusLocal v n) = W 1 * ((cNormQ v)⁻¹ ^ n * sphericalTorusValue e₁ e₂ e₃ n)) ∧
      (∀ k₁ k₂ : ℕ, k₂ + 1 ≤ k₁ → W (twoRowPointLocal v k₁ (k₂ + 1)) =
        W 1 * ((cNormQ v)⁻¹ ^ k₁ *
          (sphericalTorusValue e₁ e₂ e₃ k₁ * sphericalTorusValue e₁ e₂ e₃ (k₂ + 1) -
            sphericalTorusValue e₁ e₂ e₃ (k₁ + 1) * sphericalTorusValue e₁ e₂ e₃ k₂))))
    (m : ℤ × ℤ) (t : LocalGL3 v)
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![ratPrimeAt v ^ m.1, ratPrimeAt v ^ m.2, 1]) :
    W t = W 1 * torusValueTable (cNormQ v) e₁ e₂ e₃ m := by
  by_cases hm : 0 ≤ m.2 ∧ m.2 ≤ m.1
  · rw [pointOfCone hm ht]
    unfold torusValueTable
    rw [if_pos hm]
    rcases hk : m.2.toNat with _ | k₂
    ·
      rw [twoRowPointLocal_zero_right, huniq.1]
    ·
      have hle : k₂ + 1 ≤ m.1.toNat := by omega
      rw [huniq.2 m.1.toNat k₂ hle]
  ·
    rw [torusValueTable_of_not_dominant _ _ _ _ hm, mul_zero]
    refine hsupp t _ ht ?_
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, valued_ratPrimeAt_zpow, Valuation.map_one]
    rcases not_and_or.mp hm with h | h
    ·
      right
      rw [← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (by omega)
    ·
      left
      exact WithZero.exp_lt_exp.mpr (by omega)

private theorem
    eq_mul_torusValueTable_of_isGL3PsiWhittakerFn (ψv : AddChar (v.adicCompletion ℚ) ℂ) (W : LocalGL3 v → ℂ)
    (e₁ e₂ e₃ : ℂ)
    (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W (cNormQ v * e₁) ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W (cNormQ v * e₂) ∧
      ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)
    (hψ : IsGL3PsiWhittakerFn ψv W) (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψv x = 1)
    (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ ψv ((varpi v)⁻¹ * x) ≠ 1) (m : ℤ × ℤ) (t : LocalGL3 v)
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![ratPrimeAt v ^ m.1, ratPrimeAt v ^ m.2, 1]) :
    W t = W 1 * torusValueTable (cNormQ v) e₁ e₂ e₃ m :=
  eq_mul_torusValueTable_of_conclusions W e₁ e₂ e₃
    (eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn v ψv W hW.1 hψ hψ1)
    (sphericalTorusValue_eq_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn v ψv W e₁ e₂ e₃ hW hψ hψ0 hψ1) m t ht

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell.CubicInduction"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell.CubicInduction"
end TorusTable
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell.CubicInduction"

section Recursion

noncomputable section

open Matrix IsDedekindDomain NumberField AutomorphicForm NumberField.StandardAddChar NumberField.AdelicLevel

namespace LanglandsTunnell
namespace CubicInduction

section SliceCharacter

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem psiLoc_psiQ_apply (x : v.adicCompletion ℚ) : psiLoc psiQ v x = psiV v x := by
  show psiQ (adeleSingleAt ℚ v x) = psiV v x
  rw [adeleSingleAt_apply, psiQ_apply]
  show psiArch (0 : InfiniteAdeleRing ℚ) * psiFin (finAdeleSingleAt ℚ v x) = psiV v x
  have hside : ∀ w, w ≠ v → psiV w (finAdeleSingleAt ℚ v x w) = 1 := fun w hw => by
    rw [finAdeleSingleAt_apply_of_ne _ _ _ hw, AddChar.map_zero_eq_one]
  rw [AddChar.map_zero_eq_one, one_mul, psiFin_apply,
    finprod_eq_single (fun w => psiV w (finAdeleSingleAt ℚ v x w)) v hside, finAdeleSingleAt_apply_self]

private theorem psiV_eq_one_of_valued_le_one {x : v.adicCompletion ℚ} (hx : Valued.v x ≤ 1) : psiV v x = 1 :=
  psiV_eq_one_of_mem_integers v hx

open RatIdele Rat.HeightOneSpectrum in

private theorem exists_psiV_varpi_inv_mul_ne_one :
    ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ psiV v ((varpi v)⁻¹ * x) ≠ 1 := by
  refine ⟨varpi v * (ratPrimeAt v)⁻¹, ?_, ?_⟩
  · rw [map_mul, map_inv₀, valued_ratPrimeAt,
      show Valued.v (varpi v) = WithZero.exp (-1 : ℤ) from valued_uniformizerUnit ℚ v,
      mul_inv_cancel₀ WithZero.exp_ne_zero]
  · rw [← mul_assoc, inv_mul_cancel₀ (varpi_ne_zero v), one_mul]
    have h : (ratPrimeAt v)⁻¹ = algebraMap ℚ (v.adicCompletion ℚ) ((natGenerator v : ℚ))⁻¹ := by
      rw [map_inv₀]
      congr 1
      show ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion ℚ) = _
      rw [absNorm_asIdeal_eq_natGenerator, ← map_natCast (algebraMap ℚ (v.adicCompletion ℚ)) (natGenerator v)]
    rw [h]
    exact psiV_algebraMap_inv_ne_one v

private theorem cNormQ_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) : cNormQ v ≠ 0 :=
  Nat.cast_ne_zero.mpr fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)

end SliceCharacter
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell.CubicInduction"

section Assembly

end Assembly
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell.CubicInduction"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell.CubicInduction"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell.CubicInduction"
end Recursion
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell.CubicInduction"

end WhittakerTorusRecursion
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.WhittakerTorusRecursion"

open LanglandsTunnell.CubicInduction WhittakerTorusRecursion.LanglandsTunnell.CubicInduction in
open Matrix IsDedekindDomain NumberField AutomorphicForm NumberField.StandardAddChar NumberField.AdelicLevel in
theorem solution
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (lam1 lam2 : HeightOneSpectrum (𝓞 ℚ) → ℂ) (p : HeightOneSpectrum (𝓞 ℚ)) (hp : p ∉ S) :
    ∃ u : ℤ × ℤ → ℂ, u (0, 0) = 1 ∧ (∀ m : ℤ × ℤ, ¬ (0 ≤ m.2 ∧ m.2 ≤ m.1) → u m = 0) ∧
      ∀ (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (_hc : Continuous f)
        (_haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g)
        (_hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
          f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * f g)
        (_hK : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f)
        (_hT1 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
          (localToAdelic3 p (heckeGen1 p)) f (lam1 p))
        (_hT2 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
          (localToAdelic3 p (heckeGen2 p)) f (lam2 p))
        (g₀ : AdelicGL 3 (𝓞 ℚ) ℚ) (_hg₀ : ∀ x : LocalGL3 p, g₀ * localToAdelic3 p x = localToAdelic3 p x * g₀)
        (m : ℤ × ℤ),
        whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) psiQ f
            (g₀ * localToAdelic3 p (iotaGL (diagUnits2 (ratPrimeUnit p ^ m.1) (ratPrimeUnit p ^ m.2)))) =
          whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) psiQ f g₀ *
            u m := by
  refine ⟨torusValueTable (cNormQ p) (lam1 p / cNormQ p) (lam2 p / cNormQ p) (ω (uniformizerIdele ℚ p) : ℂ),
    torusValueTable_zero _ _ _ _, fun m hm => torusValueTable_of_not_dominant _ _ _ _ hm, ?_⟩
  intro f hc haut hcen hK hT1 hT2 g₀ hg₀ m

  show whittaker3 (prodPins ∅ (fun _ => ⊥) (fun _ => 1)) psiQ f
      (g₀ * localToAdelic3 p (iotaGL (diagUnits2 (ratPrimeUnit p ^ m.1) (ratPrimeUnit p ^ m.2)))) =
    whittaker3 (prodPins ∅ (fun _ => ⊥) (fun _ => 1)) psiQ f g₀ * _
  have hN : cNormQ p ≠ 0 := cNormQ_ne_zero p

  have hKW : IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (whittaker3 (prodPins ∅ (fun _ => ⊥) (fun _ => 1)) psiQ f) :=
    isRightInvariant_whittaker3 psiQ _ (hK p hp)

  have hT1W : IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen1 p)) (whittaker3 (prodPins ∅ (fun _ => ⊥) (fun _ => 1)) psiQ f) (lam1 p) :=
    isCosetEigenfunction_whittaker3 psiQ continuous_psiQ hc (hT1 p hp)
  have hT2W : IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen2 p)) (whittaker3 (prodPins ∅ (fun _ => ⊥) (fun _ => 1)) psiQ f) (lam2 p) :=
    isCosetEigenfunction_whittaker3 psiQ continuous_psiQ hc (hT2 p hp)

  have hcenW : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      whittaker3 (prodPins ∅ (fun _ => ⊥) (fun _ => 1)) psiQ f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) =
        (ω z : ℂ) * whittaker3 (prodPins ∅ (fun _ => ⊥) (fun _ => 1)) psiQ f g :=
    fun z g => whittaker3_centralScalarGL_mul psiQ _ hcen z g

  have hψW : IsGL3PsiWhittakerFn psiQ (whittaker3 (prodPins ∅ (fun _ => ⊥) (fun _ => 1)) psiQ f) :=
    fun x y z g => whittaker3_upperUnipotent3_mul_of_globalPointsGL psiQ_algebraMap haut x y z g
  have hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ p)
        (sliceAt p g₀ (whittaker3 (prodPins ∅ (fun _ => ⊥) (fun _ => 1)) psiQ f)) ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ p) (heckeGen1 p)
        (sliceAt p g₀ (whittaker3 (prodPins ∅ (fun _ => ⊥) (fun _ => 1)) psiQ f))
        (cNormQ p * (lam1 p / cNormQ p)) ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ p) (heckeGen2 p)
        (sliceAt p g₀ (whittaker3 (prodPins ∅ (fun _ => ⊥) (fun _ => 1)) psiQ f))
        (cNormQ p * (lam2 p / cNormQ p)) ∧
      ∀ g : LocalGL3 p, sliceAt p g₀ (whittaker3 (prodPins ∅ (fun _ => ⊥) (fun _ => 1)) psiQ f)
          (centralGen p * g) =
        (ω (uniformizerIdele ℚ p) : ℂ) *
          sliceAt p g₀ (whittaker3 (prodPins ∅ (fun _ => ⊥) (fun _ => 1)) psiQ f) g :=
    ⟨isRightInvariant_sliceAt hKW g₀,
      isCosetEigenfunction_cNormQ_mul_div hN (isCosetEigenfunction_sliceAt hT1W g₀),
      isCosetEigenfunction_cNormQ_mul_div hN (isCosetEigenfunction_sliceAt hT2W g₀),
      fun g => sliceAt_centralGen_mul hcenW hg₀ (localToAdelic3_centralGen p) g⟩
  have hψ : IsGL3PsiWhittakerFn (psiLoc psiQ p)
      (sliceAt p g₀ (whittaker3 (prodPins ∅ (fun _ => ⊥) (fun _ => 1)) psiQ f)) :=
    isGL3PsiWhittakerFn_sliceAt hψW hg₀
  have hψ0 : ∀ x : p.adicCompletion ℚ, Valued.v x ≤ 1 → psiLoc psiQ p x = 1 := fun x hx => by
    rw [psiLoc_psiQ_apply]
    exact psiV_eq_one_of_valued_le_one p hx
  have hψ1 : ∃ x : p.adicCompletion ℚ, Valued.v x ≤ 1 ∧ psiLoc psiQ p ((varpi p)⁻¹ * x) ≠ 1 := by
    obtain ⟨x, hx, hne⟩ := exists_psiV_varpi_inv_mul_ne_one p
    exact ⟨x, hx, by rwa [psiLoc_psiQ_apply]⟩

  have ht : ((iotaGL (diagUnits2 (ratPrimeUnit p ^ m.1) (ratPrimeUnit p ^ m.2)) : LocalGL3 p) :
        Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) =
      Matrix.diagonal ![ratPrimeAt p ^ m.1, ratPrimeAt p ^ m.2, 1] := by
    rw [coe_iotaGL, coe_diagUnits2, coe_ratPrimeUnit_zpow, coe_ratPrimeUnit_zpow]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.diagonal]

  have key := eq_mul_torusValueTable_of_isGL3PsiWhittakerFn (psiLoc psiQ p)
    (sliceAt p g₀ (whittaker3 (prodPins ∅ (fun _ => ⊥) (fun _ => 1)) psiQ f))
    (lam1 p / cNormQ p) (lam2 p / cNormQ p) (ω (uniformizerIdele ℚ p) : ℂ) hW hψ hψ0 hψ1 m
    (iotaGL (diagUnits2 (ratPrimeUnit p ^ m.1) (ratPrimeUnit p ^ m.2))) ht
  rw [sliceAt_one] at key
  exact key

#print axioms solution

end S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul (solution)
