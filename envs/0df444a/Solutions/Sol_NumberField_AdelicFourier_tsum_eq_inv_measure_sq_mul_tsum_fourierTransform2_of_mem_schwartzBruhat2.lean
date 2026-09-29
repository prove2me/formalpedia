-- Prove2me | solution 1 for NumberField.AdelicFourier.tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_of_mem_schwartzBruhat2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/7600d54e-a2e0-5fd4-817b-47fc16ff7590

import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_NumberField_AdelicBox_exists_eq_sum_indicator_pi_image_integralFiniteAdeles
import Theorems.Thm_NumberField_AdelicBox_map_ringEquiv_mixedSpace_eq_smul_volume_prod
import Theorems.Thm_NumberField_AdelicFourier_tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_schwartzMap_mul_indicator_pi
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Theorems.Thm_NumberField_AdelicBox_isLocallyConstant_and_hasCompactSupport_indicator_image_integralFiniteAdeles
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_of_mem_schwartzBruhat2
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
set_option synthInstance.maxSize 1024

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_AdelicFourier_tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_of_mem_schwartzBruhat2.NumberField NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_of_mem_schwartzBruhat2.NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain"
open scoped SchwartzMap NNReal ENNReal

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing mk mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace AdeleRing mixedEmbedding.integerLattice AdelicBox.exists_eq_sum_indicator_pi_image_integralFiniteAdeles AdelicBox.map_ringEquiv_mixedSpace_eq_smul_volume_prod AdelicFourier.tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_schwartzMap_mul_indicator_pi AdeleRing.secondCountableTopology"
namespace AdelicFourier
p2m_export "NumberField.AdelicFourier" "pureTensorSet2 schwartzBruhat2 pairHaar pairChar pairChar_apply fourierTransform2 schwartzBruhat2_induction fourierIntegral_zero fourierIntegral_smul fourierIntegral_add tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_schwartzMap_mul_indicator_pi norm_apply_eq_one_of_isGlobalAddChar"
namespace Poisson2Assembly
p2m_open "NumberField.AdelicFourier NumberField"

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

theorem secondCountableTopology_finiteAdeleRing :
    SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := by
  haveI : SecondCountableTopology (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology F
  exact (isEmbedding_prodMkRight (0 : InfiniteAdeleRing F) :
    Topology.IsEmbedding (Prod.mk (0 : InfiniteAdeleRing F) :
      FiniteAdeleRing (𝓞 F) F → InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)).secondCountableTopology

def split2 (F : Type) [Field F] [NumberField F] (x : Fin 2 → AdeleRing (𝓞 F) F) :
    (Fin 2 → mixedEmbedding.mixedSpace F) × (Fin 2 → FiniteAdeleRing (𝓞 F) F) :=
  (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2)

theorem measurable_split1 [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] :
    Measurable (fun x : AdeleRing (𝓞 F) F =>
      (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1, x.2)) := by
  have hc1 : Continuous fun x : AdeleRing (𝓞 F) F => x.1 := continuous_fst
  have hc2 : Continuous fun x : AdeleRing (𝓞 F) F => x.2 := continuous_snd
  have h1 : Measurable fun x : AdeleRing (𝓞 F) F => InfiniteAdeleRing.ringEquiv_mixedSpace F x.1 :=
    ((continuous_ringEquiv_mixedSpace F).comp hc1).measurable
  have h2 : Measurable fun x : AdeleRing (𝓞 F) F => x.2 := hc2.measurable
  exact h1.prodMk h2

theorem measurable_split2 [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] :
    Measurable (split2 F) := by
  have hc1 : Continuous fun x : AdeleRing (𝓞 F) F => x.1 := continuous_fst
  have hc2 : Continuous fun x : AdeleRing (𝓞 F) F => x.2 := continuous_snd
  have h1 : Measurable fun x : AdeleRing (𝓞 F) F => InfiniteAdeleRing.ringEquiv_mixedSpace F x.1 :=
    ((continuous_ringEquiv_mixedSpace F).comp hc1).measurable
  have h2 : Measurable fun x : AdeleRing (𝓞 F) F => x.2 := hc2.measurable
  refine Measurable.prodMk ?_ ?_
  · exact measurable_pi_lambda _ fun i => h1.comp (measurable_pi_apply i)
  · exact measurable_pi_lambda _ fun i => h2.comp (measurable_pi_apply i)

theorem pi_const_smul_two {X : Type*} [MeasurableSpace X] (ρ : Measure X) [SigmaFinite ρ] (c : ℝ≥0) :
    Measure.pi (fun _ : Fin 2 => c • ρ) = (c ^ 2 : ℝ≥0) • Measure.pi (fun _ : Fin 2 => ρ) := by
  refine Measure.pi_eq (μ := fun _ : Fin 2 => c • ρ) fun s _ => ?_
  rw [Measure.coe_nnreal_smul_apply, Measure.pi_pi]
  simp only [Measure.coe_nnreal_smul_apply, Fin.prod_univ_two]
  push_cast
  ring

theorem map_split2_pairHaar
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure] [SigmaFinite ν] :
    Measure.map (split2 F) (pairHaar μ)
      = ((((μ (adelicBox F)).toReal /
          (ZLattice.covolume (mixedEmbedding.integerLattice F) volume
            * (ν (integralFiniteAdeles (𝓞 F) F)).toReal)).toNNReal) ^ 2 : ℝ≥0)
        • ((volume : Measure (Fin 2 → mixedEmbedding.mixedSpace F)).prod
            (Measure.pi fun _ : Fin 2 => ν)) := by
  set c : ℝ≥0 := ((μ (adelicBox F)).toReal /
          (ZLattice.covolume (mixedEmbedding.integerLattice F) volume
            * (ν (integralFiniteAdeles (𝓞 F) F)).toReal)).toNNReal with hc
  have h1 := (map_ringEquiv_mixedSpace_eq_smul_volume_prod F μ ν).2
  rw [← hc] at h1
  set T : AdeleRing (𝓞 F) F → mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F :=
    fun x => (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1, x.2) with hT
  have hTm : Measurable T := measurable_split1
  set A := MeasurableEquiv.arrowProdEquivProdArrow (mixedEmbedding.mixedSpace F)
    (FiniteAdeleRing (𝓞 F) F) (Fin 2) with hA
  have hsplit : split2 F = A ∘ fun x i => T (x i) := by
    funext x
    rfl
  have hPm : Measurable fun (x : Fin 2 → AdeleRing (𝓞 F) F) i => T (x i) :=
    measurable_pi_lambda _ fun i => hTm.comp (measurable_pi_apply i)
  rw [hsplit, ← Measure.map_map A.measurable hPm]
  haveI : SigmaFinite (Measure.map T μ) := by rw [h1]; infer_instance
  have hpi : Measure.map (fun (x : Fin 2 → AdeleRing (𝓞 F) F) i => T (x i)) (pairHaar μ)
      = Measure.pi fun _ : Fin 2 => Measure.map T μ := by
    unfold pairHaar
    exact Measure.pi_map_pi fun _ => hTm.aemeasurable
  rw [hpi, h1, pi_const_smul_two, Measure.map_smul]
  congr 1
  exact (measurePreserving_arrowProdEquivProdArrow (mixedEmbedding.mixedSpace F)
    (FiniteAdeleRing (𝓞 F) F) (Fin 2) (fun _ => volume) (fun _ => ν)).map_eq

theorem integrable_tensor2
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure] [SigmaFinite ν]
    {G : (Fin 2 → mixedEmbedding.mixedSpace F) → ℂ} (hG : Integrable G volume)
    {H : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ} (hH : Integrable H (Measure.pi fun _ : Fin 2 => ν)) :
    Integrable (fun x : Fin 2 → AdeleRing (𝓞 F) F =>
      G (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) * H (fun i => (x i).2))
      (pairHaar μ) := by
  have hprod : Integrable (fun z : (Fin 2 → mixedEmbedding.mixedSpace F) ×
      (Fin 2 → FiniteAdeleRing (𝓞 F) F) => G z.1 * H z.2)
      (Measure.map (split2 F) (pairHaar μ)) := by
    rw [map_split2_pairHaar μ ν]
    exact (hG.mul_prod hH).smul_measure_nnreal
  exact (integrable_map_measure hprod.aestronglyMeasurable
    (measurable_split2).aemeasurable).mp hprod

def coset (F : Type) [Field F] [NumberField F] (d : 𝓞 F) (k : F) : Set (FiniteAdeleRing (𝓞 F) F) :=
  (fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
    + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F

theorem indicator_pi_eq_prod {ι : Type*} [Fintype ι] {X : Type*} (S : ι → Set X) (q : ι → X) :
    (Set.pi Set.univ S).indicator (1 : (ι → X) → ℂ) q = ∏ i, (S i).indicator (1 : X → ℂ) (q i) := by
  by_cases hq : q ∈ Set.pi Set.univ S
  · rw [Set.indicator_of_mem hq, Pi.one_apply]
    symm
    refine Finset.prod_eq_one fun i _ => ?_
    rw [Set.indicator_of_mem (hq i (Set.mem_univ i)), Pi.one_apply]
  · rw [Set.indicator_of_notMem hq]
    simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hq
    obtain ⟨i, hi⟩ := hq
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)

theorem integrable_indicator_pi_coset
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure] [SigmaFinite ν]
    (d : 𝓞 F) (hd : d ≠ 0) (k : Fin 2 → F) :
    Integrable ((Set.pi Set.univ fun i => coset F d (k i)).indicator
      (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ)) (Measure.pi fun _ : Fin 2 => ν) := by
  have h : ((Set.pi Set.univ fun i => coset F d (k i)).indicator
      (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ))
      = fun q => ∏ i, (coset F d (k i)).indicator (1 : FiniteAdeleRing (𝓞 F) F → ℂ) (q i) := by
    funext q
    exact indicator_pi_eq_prod _ q
  rw [h]
  refine Integrable.fintype_prod (f := fun i => (coset F d (k i)).indicator
    (1 : FiniteAdeleRing (𝓞 F) F → ℂ)) fun i => ?_
  obtain ⟨hlc, hcs⟩ :=
    isLocallyConstant_and_hasCompactSupport_indicator_image_integralFiniteAdeles F d hd (k i)
  exact hlc.continuous.integrable_of_hasCompactSupport hcs

section Predicate

variable [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
  (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
  (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)

def P (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) : Prop :=
  Integrable Φ (pairHaar μ) ∧
  Summable (fun ξ : Fin 2 → F => Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))) ∧
  Summable (fun ξ : Fin 2 → F =>
    fourierTransform2 ψ μ Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))) ∧
  ∑' ξ : Fin 2 → F, Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))
    = (((μ (adelicBox F)).toReal : ℂ) ^ 2)⁻¹ *
        ∑' ξ : Fin 2 → F, fourierTransform2 ψ μ Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))

variable {μ ψ}

omit [BorelSpace (AdeleRing (𝓞 F) F)] [μ.IsAddHaarMeasure] in
theorem P_zero : P μ ψ 0 := by
  refine ⟨integrable_zero _ _ _, ?_, ?_, ?_⟩
  · simp
  · unfold fourierTransform2
    rw [fourierIntegral_zero]
    simp
  · unfold fourierTransform2
    rw [fourierIntegral_zero]
    simp

omit [BorelSpace (AdeleRing (𝓞 F) F)] [μ.IsAddHaarMeasure] in
theorem P_smul (c : ℂ) {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} (h : P μ ψ Φ) : P μ ψ (c • Φ) := by
  obtain ⟨hint, hs1, hs2, heq⟩ := h
  refine ⟨hint.smul c, ?_, ?_, ?_⟩
  · simpa [Pi.smul_apply, smul_eq_mul] using hs1.mul_left c
  · unfold fourierTransform2 at hs2 ⊢
    rw [fourierIntegral_smul]
    simpa [Pi.smul_apply, smul_eq_mul] using hs2.mul_left c
  · unfold fourierTransform2 at heq hs2 ⊢
    rw [fourierIntegral_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [tsum_mul_left, tsum_mul_left, heq]
    ring

omit [μ.IsAddHaarMeasure] in

theorem integrable_kernel_mul (hψc : Continuous ψ) (hψu : ∀ x, ‖ψ x‖ = 1)
    {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Integrable Φ (pairHaar μ))
    (w : Fin 2 → AdeleRing (𝓞 F) F) :
    Integrable (fun v => pairChar ψ (-(v * w)) * Φ v) (pairHaar μ) := by
  haveI := NumberField.AdeleRing.secondCountableTopology F
  have hcont : Continuous fun v : Fin 2 → AdeleRing (𝓞 F) F => pairChar ψ (-(v * w)) := by
    have h1 : Continuous fun v : Fin 2 → AdeleRing (𝓞 F) F => (-(v * w)) 0 + (-(v * w)) 1 :=
      ((continuous_apply 0).comp ((continuous_mul_const w).neg)).add
        ((continuous_apply 1).comp ((continuous_mul_const w).neg))
    have h2 : (fun v : Fin 2 → AdeleRing (𝓞 F) F => pairChar ψ (-(v * w)))
        = fun v => ψ ((-(v * w)) 0 + (-(v * w)) 1) := by
      funext v; exact pairChar_apply ψ _
    rw [h2]
    exact hψc.comp h1
  refine hΦ.bdd_mul (c := 1) hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun v => ?_)
  rw [pairChar_apply]
  exact (hψu _).le

omit [μ.IsAddHaarMeasure] in
theorem P_add (hψc : Continuous ψ) (hψu : ∀ x, ‖ψ x‖ = 1)
    {Φ Ψ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} (hΦ : P μ ψ Φ) (hΨ : P μ ψ Ψ) :
    P μ ψ (Φ + Ψ) := by
  obtain ⟨hint, hs1, hs2, heq⟩ := hΦ
  obtain ⟨hint', hs1', hs2', heq'⟩ := hΨ
  have hadd : fourierTransform2 ψ μ (Φ + Ψ) = fourierTransform2 ψ μ Φ + fourierTransform2 ψ μ Ψ := by
    funext w
    unfold fourierTransform2
    rw [Pi.add_apply]
    exact fourierIntegral_add _ _ w (integrable_kernel_mul hψc hψu hint w)
      (integrable_kernel_mul hψc hψu hint' w)
  refine ⟨hint.add hint', ?_, ?_, ?_⟩
  · simpa [Pi.add_apply] using hs1.add hs1'
  · rw [hadd]
    simpa [Pi.add_apply] using hs2.add hs2'
  · rw [hadd]
    simp only [Pi.add_apply]
    rw [hs1.tsum_add hs1', hs2.tsum_add hs2', heq, heq']
    ring

omit [μ.IsAddHaarMeasure] in
theorem P_sum (hψc : Continuous ψ) (hψu : ∀ x, ‖ψ x‖ = 1)
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (Φ : ι → (Fin 2 → AdeleRing (𝓞 F) F) → ℂ)
    (h : ∀ i ∈ s, P μ ψ (Φ i)) : P μ ψ (∑ i ∈ s, c i • Φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (P_zero : P μ ψ 0)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact P_add hψc hψu (P_smul (c a) (h a (Finset.mem_insert_self a s)))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end Predicate

theorem P_box_tensor
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (g : 𝓢((Fin 2 → mixedEmbedding.mixedSpace F), ℂ)) (d : 𝓞 F) (hd : d ≠ 0) (k : Fin 2 → F) :
    P μ ψ (fun x : Fin 2 → AdeleRing (𝓞 F) F =>
      g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)
        * (Set.pi Set.univ fun i => coset F d (k i)).indicator
            (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) (fun i => (x i).2)) := by

  letI : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := secondCountableTopology_finiteAdeleRing
  set ν : Measure (FiniteAdeleRing (𝓞 F) F) := Measure.addHaar with hν
  have hint := integrable_tensor2 μ ν (G := ⇑g) g.integrable
    (integrable_indicator_pi_coset ν d hd k)
  obtain ⟨hs1, hs2, heq⟩ :=
    tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_schwartzMap_mul_indicator_pi F μ hψ g d hd k rfl
  exact ⟨hint, hs1, hs2, heq⟩

theorem P_pureTensor
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ pureTensorSet2 F) : P μ ψ Φ := by
  obtain ⟨g, h, hlc, hcs, rfl⟩ := hΦ
  obtain ⟨d, hd, s, c, hh⟩ := exists_eq_sum_indicator_pi_image_integralFiniteAdeles F (Fin 2) hlc hcs
  have hψu : ∀ x, ‖ψ x‖ = 1 := norm_apply_eq_one_of_isGlobalAddChar F hψ
  have key : (fun x : Fin 2 → AdeleRing (𝓞 F) F =>
        g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) * h (fun i => (x i).2))
      = ∑ k ∈ s, c k • fun x : Fin 2 → AdeleRing (𝓞 F) F =>
          g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)
            * (Set.pi Set.univ fun i => coset F d (k i)).indicator
                (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) (fun i => (x i).2) := by
    funext x
    rw [hh]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, coset]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [key]
  exact P_sum hψ.continuous hψu s c _ fun k _ => P_box_tensor μ hψ g d hd k

end NumberField.AdelicFourier.Poisson2Assembly

end

open MeasureTheory _root_.NumberField _root_.P2MW.S_NumberField_AdelicFourier_tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_of_mem_schwartzBruhat2.NumberField _root_.NumberField.AdelicFourier _root_.P2MW.S_NumberField_AdelicFourier_tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_of_mem_schwartzBruhat2.NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm NumberField.AdelicFourier.Poisson2Assembly in

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 F) :
    Summable (fun ξ : Fin 2 → F => Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))) ∧
    Summable (fun ξ : Fin 2 → F =>
      fourierTransform2 ψ μ Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))) ∧
    ∑' ξ : Fin 2 → F, Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))
      = (((μ (adelicBox F)).toReal : ℂ) ^ 2)⁻¹ *
          ∑' ξ : Fin 2 → F, fourierTransform2 ψ μ Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) := by
  have hψu : ∀ x, ‖ψ x‖ = 1 := norm_apply_eq_one_of_isGlobalAddChar F hψ
  have main : P μ ψ Φ :=
    schwartzBruhat2_induction (p := fun Φ _ => P μ ψ Φ)
      (fun Φ hΦ => P_pureTensor μ hψ hΦ) P_zero
      (fun Φ Ψ _ _ ihΦ ihΨ => P_add hψ.continuous hψu ihΦ ihΨ)
      (fun c Φ _ ih => P_smul c ih) hΦ
  exact main.2

end S_NumberField_AdelicFourier_tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_of_mem_schwartzBruhat2
end P2MW
export P2MW.S_NumberField_AdelicFourier_tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_of_mem_schwartzBruhat2 (solution)
