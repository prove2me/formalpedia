-- Prove2me | solution 1 for NumberField.AdelicBox.lintegral_pi_pureTensor_two_eq_sq_mul_lintegral_pi_volume_mul_lintegral_pi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/bb04ddd5-79c5-5285-9875-c7f2d1e34426

import Definitions.Def_NumberField_AdelicBox
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Theorems.Thm_NumberField_AdelicBox_map_ringEquiv_mixedSpace_eq_smul_volume_prod
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicBox_lintegral_pi_pureTensor_two_eq_sq_mul_lintegral_pi_volume_mul_lintegral_pi
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_AdelicBox_lintegral_pi_pureTensor_two_eq_sq_mul_lintegral_pi_volume_mul_lintegral_pi.NumberField NumberField.InfinitePlace NumberField.AdelicBox P2MW.S_NumberField_AdelicBox_lintegral_pi_pureTensor_two_eq_sq_mul_lintegral_pi_volume_mul_lintegral_pi.NumberField.AdelicBox IsDedekindDomain"
open scoped ENNReal NNReal

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing discr mk mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace InfinitePlace AdeleRing mixedEmbedding.integerLattice mixedEmbedding.covolume_integerLattice AdelicBox.continuous_ringEquiv_mixedSpace AdelicBox.map_ringEquiv_mixedSpace_eq_smul_volume_prod AdeleRing.secondCountableTopology"
namespace AdelicBox
p2m_export "NumberField.AdelicBox" "integralFiniteAdeles continuous_ringEquiv_mixedSpace adelicBox map_ringEquiv_mixedSpace_eq_smul_volume_prod"
namespace TensorMass
p2m_open "NumberField.AdelicBox NumberField"

open scoped Classical

variable (F : Type) [Field F] [NumberField F]
  [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
  [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F
local notation "E∞" => mixedEmbedding.mixedSpace F

def split (x : 𝔸) : E∞ × 𝔸f := (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1, x.2)

theorem continuous_split : Continuous (split F) := by
  have h1 : Continuous fun x : 𝔸 => InfiniteAdeleRing.ringEquiv_mixedSpace F x.1 :=
    (NumberField.AdelicBox.continuous_ringEquiv_mixedSpace F).comp continuous_fst
  have h2 : Continuous fun x : 𝔸 => x.2 := continuous_snd
  exact h1.prodMk h2

theorem measurable_split : Measurable (split F) := (continuous_split F).measurable

theorem secondCountableTopology_finiteAdeleRing :
    SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := by
  haveI : SecondCountableTopology (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology F
  exact (isEmbedding_prodMkRight (0 : InfiniteAdeleRing F) :
    Topology.IsEmbedding (Prod.mk (0 : InfiniteAdeleRing F) :
      FiniteAdeleRing (𝓞 F) F → InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)).secondCountableTopology

theorem pi_smul_const {X : Type*} [MeasurableSpace X] (ρ : Measure X) [SigmaFinite ρ] (c : ℝ≥0) :
    Measure.pi (fun _ : Fin 2 => c • ρ) = (c ^ 2) • Measure.pi (fun _ : Fin 2 => ρ) := by
  haveI : ∀ i : Fin 2, SigmaFinite ((fun _ : Fin 2 => c • ρ) i) := fun _ =>
    inferInstanceAs (SigmaFinite (c • ρ))
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.coe_nnreal_smul_apply, Measure.pi_pi]
  simp only [Measure.coe_nnreal_smul_apply, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ENNReal.coe_pow]

variable {F}

theorem main (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (G : (Fin 2 → E∞) → ℝ≥0∞) (hG : Measurable G)
    (H : (Fin 2 → 𝔸f) → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ x, G (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) * H (fun i => (x i).2)
        ∂(Measure.pi fun _ : Fin 2 => μ) =
      ENNReal.ofReal ((μ (adelicBox F)).toReal /
            (ZLattice.covolume (mixedEmbedding.integerLattice F) volume
              * (ν (integralFiniteAdeles (𝓞 F) F)).toReal)) ^ 2 *
        (∫⁻ y, G y ∂(Measure.pi fun _ : Fin 2 => (volume : Measure E∞))) *
        ∫⁻ z, H z ∂(Measure.pi fun _ : Fin 2 => ν) := by
  haveI : SecondCountableTopology 𝔸f := secondCountableTopology_finiteAdeleRing F
  haveI : SigmaFinite ν := by infer_instance
  haveI hσν : ∀ i : Fin 2, SigmaFinite ((fun _ : Fin 2 => ν) i) := fun _ => inferInstanceAs (SigmaFinite ν)
  haveI hσv : ∀ i : Fin 2, SigmaFinite ((fun _ : Fin 2 => (volume : Measure E∞)) i) := fun _ =>
    inferInstanceAs (SigmaFinite (volume : Measure E∞))

  obtain ⟨hκpos, hsplit⟩ := NumberField.AdelicBox.map_ringEquiv_mixedSpace_eq_smul_volume_prod F μ ν
  set κr : ℝ := (μ (adelicBox F)).toReal /
      (ZLattice.covolume (mixedEmbedding.integerLattice F) volume * (ν (integralFiniteAdeles (𝓞 F) F)).toReal)
    with hκr
  set κ : ℝ≥0 := κr.toNNReal with hκ
  have hsplit' : Measure.map (split F) μ = κ • (volume : Measure E∞).prod ν := hsplit

  set Θ : (Fin 2 → E∞ × 𝔸f) → ℝ≥0∞ := fun y => G (fun i => (y i).1) * H (fun i => (y i).2) with hΘ
  have hΘm : Measurable Θ := by
    refine Measurable.mul (hG.comp ?_) (hH.comp ?_)
    · exact measurable_pi_lambda _ fun i => measurable_fst.comp (measurable_pi_apply i)
    · exact measurable_pi_lambda _ fun i => measurable_snd.comp (measurable_pi_apply i)
  have hSm : Measurable (fun (x : Fin 2 → 𝔸) (i : Fin 2) => split F (x i)) :=
    measurable_pi_lambda (fun (x : Fin 2 → 𝔸) (i : Fin 2) => split F (x i))
      fun i => (measurable_split F).comp (measurable_pi_apply i)
  have hstep1 : ∫⁻ x, G (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) * H (fun i => (x i).2)
      ∂(Measure.pi fun _ : Fin 2 => μ) =
      ∫⁻ y, Θ y ∂((Measure.pi fun _ : Fin 2 => μ).map (fun x i => split F (x i))) := by
    rw [lintegral_map hΘm hSm]
    rfl

  haveI hσ : ∀ i : Fin 2, SigmaFinite (((fun _ : Fin 2 => μ) i).map ((fun _ : Fin 2 => split F) i)) := fun i => by
    show SigmaFinite (μ.map (split F))
    rw [hsplit']; infer_instance
  have hstep2 : (Measure.pi fun _ : Fin 2 => μ).map (fun x i => split F (x i)) =
      (κ ^ 2) • Measure.pi (fun _ : Fin 2 => (volume : Measure E∞).prod ν) := by
    have h := Measure.pi_map_pi (μ := fun _ : Fin 2 => μ) (f := fun _ : Fin 2 => split F) (hμ := hσ)
      (fun _ => (measurable_split F).aemeasurable)
    rw [h]
    simp only [hsplit']
    exact pi_smul_const ((volume : Measure E∞).prod ν) κ

  have hstep3 : ∫⁻ y, Θ y ∂(Measure.pi (fun _ : Fin 2 => (volume : Measure E∞).prod ν)) =
      (∫⁻ y, G y ∂(Measure.pi fun _ : Fin 2 => (volume : Measure E∞))) * ∫⁻ z, H z ∂(Measure.pi fun _ : Fin 2 => ν) := by
    have hmp := measurePreserving_arrowProdEquivProdArrow E∞ 𝔸f (Fin 2)
      (fun _ => (volume : Measure E∞)) (fun _ => ν)
    have hΘ' : Θ = fun y => (fun p : (Fin 2 → E∞) × (Fin 2 → 𝔸f) => G p.1 * H p.2)
        (MeasurableEquiv.arrowProdEquivProdArrow E∞ 𝔸f (Fin 2) y) := by
      funext y; rfl
    rw [hΘ', hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
    exact lintegral_prod_mul hG.aemeasurable hH.aemeasurable
  rw [hstep1, hstep2, lintegral_smul_measure, hstep3, ENNReal.smul_def, smul_eq_mul, ← mul_assoc]
  congr 2

theorem main' (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (G : (Fin 2 → E∞) → ℝ≥0∞) (hG : Measurable G)
    (H : (Fin 2 → 𝔸f) → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ x, G (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) * H (fun i => (x i).2)
        ∂(Measure.pi fun _ : Fin 2 => μ) =
      ENNReal.ofReal ((μ (adelicBox F)).toReal * 2 ^ nrComplexPlaces F /
            (Real.sqrt |(discr F : ℝ)| * (ν (integralFiniteAdeles (𝓞 F) F)).toReal)) ^ 2 *
        (∫⁻ y, G y ∂(Measure.pi fun _ : Fin 2 => (volume : Measure E∞))) *
        ∫⁻ z, H z ∂(Measure.pi fun _ : Fin 2 => ν) := by
  rw [main μ ν G hG H hH, NumberField.mixedEmbedding.covolume_integerLattice]
  congr 3
  have h2 : ((2 : ℝ)⁻¹) ^ nrComplexPlaces F * Real.sqrt |(discr F : ℝ)| * (ν (integralFiniteAdeles (𝓞 F) F)).toReal =
      (Real.sqrt |(discr F : ℝ)| * (ν (integralFiniteAdeles (𝓞 F) F)).toReal) / 2 ^ nrComplexPlaces F := by
    rw [inv_pow]; field_simp
  rw [h2, div_div_eq_mul_div]

end NumberField.AdelicBox.TensorMass

end

open MeasureTheory _root_.NumberField _root_.P2MW.S_NumberField_AdelicBox_lintegral_pi_pureTensor_two_eq_sq_mul_lintegral_pi_volume_mul_lintegral_pi.NumberField _root_.NumberField.InfinitePlace.NumberField _root_.NumberField.InfinitePlace _root_.NumberField.InfinitePlace.NumberField.InfinitePlace _root_.NumberField.AdelicBox _root_.P2MW.S_NumberField_AdelicBox_lintegral_pi_pureTensor_two_eq_sq_mul_lintegral_pi_volume_mul_lintegral_pi.NumberField.AdelicBox IsDedekindDomain in
open scoped Classical in
theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (G : (Fin 2 → mixedEmbedding.mixedSpace F) → ENNReal) (hG : Measurable G)
    (H : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ENNReal) (hH : Measurable H) :
    ∫⁻ x, G (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) * H (fun i => (x i).2)
        ∂(Measure.pi fun _ : Fin 2 => μ) =
      ENNReal.ofReal ((μ (adelicBox F)).toReal * 2 ^ nrComplexPlaces F /
            (Real.sqrt |(discr F : ℝ)| * (ν (integralFiniteAdeles (𝓞 F) F)).toReal)) ^ 2 *
        (∫⁻ y, G y ∂(Measure.pi fun _ : Fin 2 => (volume : Measure (mixedEmbedding.mixedSpace F)))) *
        ∫⁻ z, H z ∂(Measure.pi fun _ : Fin 2 => ν) :=
  NumberField.AdelicBox.TensorMass.main' μ ν G hG H hH

end S_NumberField_AdelicBox_lintegral_pi_pureTensor_two_eq_sq_mul_lintegral_pi_volume_mul_lintegral_pi
end P2MW
export P2MW.S_NumberField_AdelicBox_lintegral_pi_pureTensor_two_eq_sq_mul_lintegral_pi_volume_mul_lintegral_pi (solution)
