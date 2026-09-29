-- Prove2me | solution 1 for NumberField.AdelicFourier.fourierTransform2_mem_schwartzBruhat2_and_reflectPair_mem_schwartzBruhat2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/cc1e3439-ae24-569f-b046-9a5d45a37baa

import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_NumberField_AdelicBox_exists_eq_sum_indicator_pi_image_integralFiniteAdeles
import Theorems.Thm_NumberField_AdelicBox_map_ringEquiv_mixedSpace_eq_smul_volume_prod
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdelicBox_isLocallyConstant_and_hasCompactSupport_indicator_image_integralFiniteAdeles
import Theorems.Thm_SchwartzMap_exists_coe_eq_vectorFourierIntegral
import Theorems.Thm_NumberField_mixedEmbedding_traceForm_mixedSpace_nondegenerate
import Theorems.Thm_NumberField_AdelicFourier_exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar
import Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat
import Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Theorems.Thm_NumberField_AdelicFourier_continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_fourierTransform2_mem_schwartzBruhat2_and_reflectPair_mem_schwartzBruhat2
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
set_option synthInstance.maxSize 1024

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_AdelicFourier_fourierTransform2_mem_schwartzBruhat2_and_reflectPair_mem_schwartzBruhat2.NumberField NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_fourierTransform2_mem_schwartzBruhat2_and_reflectPair_mem_schwartzBruhat2.NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain"
open scoped SchwartzMap NNReal ENNReal FourierTransform

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing mk mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace AdeleRing mixedEmbedding.integerLattice AdeleRing.secondCountableTopology mixedEmbedding.traceForm_mixedSpace_nondegenerate AdelicFourier.continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2"
namespace AdelicFourier
p2m_export "NumberField.AdelicFourier" "pureTensorSet2 schwartzBruhat2 pairHaar pairChar pairChar_apply fourierTransform2 reflectPair tensor_mem_pureTensorSet2 mem_schwartzBruhat2_of_mem_pureTensorSet2 zero_mem_schwartzBruhat2 schwartzBruhat2_induction fourierIntegral fourierIntegral_def fourierIntegral_zero fourierIntegral_smul fourierIntegral_add schwartzBruhat tensor_mem_pureTensorSet mem_schwartzBruhat_of_mem_pureTensorSet schwartzBruhat_induction exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar fourierIntegral_mem_schwartzBruhat fourierIntegral_pureTensor_eq norm_apply_eq_one_of_isGlobalAddChar continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2"
namespace FT2StableSol
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

def cst (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] (μ : Measure (AdeleRing (𝓞 F) F))
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] (ν : Measure (FiniteAdeleRing (𝓞 F) F)) : ℝ :=
  (μ (adelicBox F)).toReal /
    (ZLattice.covolume (mixedEmbedding.integerLattice F) volume
      * (ν (integralFiniteAdeles (𝓞 F) F)).toReal)

theorem map_split2_pairHaar
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure] [SigmaFinite ν] :
    Measure.map (split2 F) (pairHaar μ)
      = (((cst F μ ν).toNNReal) ^ 2 : ℝ≥0)
        • ((volume : Measure (Fin 2 → mixedEmbedding.mixedSpace F)).prod
            (Measure.pi fun _ : Fin 2 => ν)) := by
  set c : ℝ≥0 := (cst F μ ν).toNNReal with hc
  have h1 := (map_ringEquiv_mixedSpace_eq_smul_volume_prod F μ ν).2
  rw [show ((μ (adelicBox F)).toReal /
          (ZLattice.covolume (mixedEmbedding.integerLattice F) volume
            * (ν (integralFiniteAdeles (𝓞 F) F)).toReal)).toNNReal = c from rfl] at h1
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

theorem integral_tensor2
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure] [SigmaFinite ν]
    {G : (Fin 2 → mixedEmbedding.mixedSpace F) → ℂ}
    (hG : AEStronglyMeasurable G volume)
    {H : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hH : AEStronglyMeasurable H (Measure.pi fun _ : Fin 2 => ν)) :
    ∫ x : Fin 2 → AdeleRing (𝓞 F) F,
      G (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) * H (fun i => (x i).2) ∂(pairHaar μ)
      = ((cst F μ ν).toNNReal : ℂ) ^ 2 * (∫ a, G a) * ∫ q, H q ∂(Measure.pi fun _ : Fin 2 => ν) := by
  have hGH : AEStronglyMeasurable (fun z : (Fin 2 → mixedEmbedding.mixedSpace F) ×
      (Fin 2 → FiniteAdeleRing (𝓞 F) F) => G z.1 * H z.2)
      (Measure.map (split2 F) (pairHaar μ)) := by
    rw [map_split2_pairHaar μ ν]
    exact (hG.comp_fst.mul hH.comp_snd).smul_measure _
  have h := integral_map (measurable_split2 (F := F)).aemeasurable hGH
  have h' : (fun x : Fin 2 → AdeleRing (𝓞 F) F =>
      G (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) * H (fun i => (x i).2))
      = fun x => (fun z : (Fin 2 → mixedEmbedding.mixedSpace F) ×
          (Fin 2 → FiniteAdeleRing (𝓞 F) F) => G z.1 * H z.2) (split2 F x) := rfl
  rw [h', ← h, map_split2_pairHaar μ ν, integral_smul_nnreal_measure, integral_prod_mul,
    NNReal.smul_def, Complex.real_smul]
  push_cast
  ring

variable (F) in

def B2 : LinearMap.BilinForm ℝ (Fin 2 → mixedEmbedding.mixedSpace F) :=
  ∑ i : Fin 2, (Algebra.traceForm ℝ (mixedEmbedding.mixedSpace F)).compl₁₂
    (LinearMap.proj i) (LinearMap.proj i)

theorem B2_apply (v w : Fin 2 → mixedEmbedding.mixedSpace F) :
    B2 F v w = ∑ i : Fin 2, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (v i * w i) := by
  simp [B2, Algebra.traceForm_apply]

theorem B2_nondegenerate : (B2 F).Nondegenerate := by
  have hT := mixedEmbedding.traceForm_mixedSpace_nondegenerate F
  have aux : ∀ v : Fin 2 → mixedEmbedding.mixedSpace F,
      (∀ w, B2 F v w = 0) → v = 0 := by
    intro v hv
    funext i
    refine hT.1 (v i) fun y => ?_
    have := hv (Pi.single i y)
    rw [B2_apply, Finset.sum_eq_single i] at this
    · simpa [Algebra.traceForm_apply] using this
    · intro j _ hj; simp [Pi.single_eq_of_ne hj]
    · intro h; exact absurd (Finset.mem_univ i) h
  refine ⟨fun v hv => aux v hv, fun w hw => ?_⟩
  refine aux w fun v => ?_
  have := hw v
  rw [B2_apply] at this ⊢
  rw [← this]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]

section BoxTensor

variable [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
  (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
  [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
  (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure] [SigmaFinite ν]
  {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ}

variable (ψ) in

def psiF (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ :=
  ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

omit [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
  [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] in
theorem psiF_apply (y : FiniteAdeleRing (𝓞 F) F) : psiF ψ y = ψ (0, y) := rfl

omit [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
  [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] in
theorem continuous_psiF (hψ : Continuous ψ) : Continuous (psiF ψ) := by
  have : (psiF ψ : FiniteAdeleRing (𝓞 F) F → ℂ) = fun y => ψ (((0 : InfiniteAdeleRing F), y) :
      InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) := rfl
  rw [this]
  exact hψ.comp (continuous_const.prodMk continuous_id)

omit [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
  [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] in

theorem pairChar_neg_mul_eq
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
      ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    (v w : Fin 2 → AdeleRing (𝓞 F) F) :
    pairChar ψ (-(v * w))
      = (𝐞 (-(B2 F (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (v i).1)
            (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (w i).1))) : ℂ)
        * psiF ψ (-((v 0).2 * (w 0).2 + (v 1).2 * (w 1).2)) := by
  rw [pairChar_apply]
  set u : AdeleRing (𝓞 F) F := (-(v * w)) 0 + (-(v * w)) 1 with hu
  have hsplit : u = ((u.1, 0) : AdeleRing (𝓞 F) F) + ((0, u.2) : AdeleRing (𝓞 F) F) :=
    Prod.ext (by simp) (by simp)
  have hmul : ψ u = ψ ((u.1, 0) : AdeleRing (𝓞 F) F) * ψ ((0, u.2) : AdeleRing (𝓞 F) F) := by
    conv_lhs => rw [hsplit]
    exact AddChar.map_add_eq_mul ψ _ _
  rw [hmul, hψ_inf u.1]
  have hu1 : u.1 = -((v 0).1 * (w 0).1) + -((v 1).1 * (w 1).1) := rfl
  have hu2 : u.2 = -((v 0).2 * (w 0).2) + -((v 1).2 * (w 1).2) := rfl
  congr 1
  · congr 2
    rw [hu1, B2_apply, Fin.sum_univ_two]
    simp only [map_neg, map_add, map_mul]
    ring
  · rw [psiF_apply, hu2, neg_add]

omit [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
  [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] in

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

def coset (F : Type) [Field F] [NumberField F] (d : 𝓞 F) (k : F) : Set (FiniteAdeleRing (𝓞 F) F) :=
  (fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
    + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F

variable {μ ν}

theorem fourierTransform2_boxTensor_eq
    (hψ : Continuous ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
      ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    (g : 𝓢((Fin 2 → mixedEmbedding.mixedSpace F), ℂ)) (d : 𝓞 F) (hd : d ≠ 0) (k : Fin 2 → F)
    (w : Fin 2 → AdeleRing (𝓞 F) F) :
    fourierTransform2 ψ μ (fun x => g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)
        * (Set.pi Set.univ fun i => coset F d (k i)).indicator
          (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) (fun i => (x i).2)) w
      = ((cst F μ ν).toNNReal : ℂ) ^ 2
        * VectorFourier.fourierIntegral 𝐞 volume (B2 F) g
            (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (w i).1)
        * ∏ i, fourierIntegral (psiF ψ) ν ((coset F d (k i)).indicator 1) ((w i).2) := by
  haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := secondCountableTopology_finiteAdeleRing
  set b : Fin 2 → mixedEmbedding.mixedSpace F := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (w i).1
    with hb
  set r : Fin 2 → FiniteAdeleRing (𝓞 F) F := fun i => (w i).2 with hr
  set G : (Fin 2 → mixedEmbedding.mixedSpace F) → ℂ := fun a => (𝐞 (-(B2 F a b)) : ℂ) * g a with hG
  set H : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ := fun q =>
    psiF ψ (-(q 0 * r 0 + q 1 * r 1)) * (Set.pi Set.univ fun i => coset F d (k i)).indicator
      (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) q with hH

  have hint : fourierTransform2 ψ μ (fun x => g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)
        * (Set.pi Set.univ fun i => coset F d (k i)).indicator
          (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) (fun i => (x i).2)) w
      = ∫ x : Fin 2 → AdeleRing (𝓞 F) F,
          G (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) * H (fun i => (x i).2) ∂(pairHaar μ) := by
    unfold fourierTransform2
    rw [fourierIntegral_def]
    congr 1
    funext v
    rw [pairChar_neg_mul_eq hψ_inf v w]
    simp only [hG, hH]
    ring
  rw [hint]

  have hGm : AEStronglyMeasurable G volume := by
    refine (Continuous.mul ?_ g.continuous).aestronglyMeasurable
    refine continuous_subtype_val.comp (Real.continuous_fourierChar.comp ?_)
    exact ((B2 F).flip b).continuous_of_finiteDimensional.neg
  have hcoset : ∀ i, Continuous ((coset F d (k i)).indicator (1 : FiniteAdeleRing (𝓞 F) F → ℂ)) := by
    intro i
    exact (isLocallyConstant_and_hasCompactSupport_indicator_image_integralFiniteAdeles F d hd (k i)).1.continuous
  have hHc : Continuous H := by
    refine Continuous.mul ?_ ?_
    · refine (continuous_psiF hψ).comp (Continuous.neg ?_)
      exact (((continuous_apply 0).mul continuous_const).add ((continuous_apply 1).mul continuous_const))
    · have : ((Set.pi Set.univ fun i => coset F d (k i)).indicator
          (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ))
          = fun q => ∏ i, (coset F d (k i)).indicator (1 : FiniteAdeleRing (𝓞 F) F → ℂ) (q i) := by
        funext q; exact indicator_pi_eq_prod _ q
      rw [this]
      exact continuous_finsetProd _ fun i _ => (hcoset i).comp (continuous_apply i)
  have hHm : AEStronglyMeasurable H (Measure.pi fun _ : Fin 2 => ν) := hHc.aestronglyMeasurable
  rw [integral_tensor2 μ ν hGm hHm]

  have hGint : ∫ a, G a = VectorFourier.fourierIntegral 𝐞 volume (B2 F) g b := by
    simp only [hG, VectorFourier.fourierIntegral, Circle.smul_def, smul_eq_mul]

  have hHint : ∫ q, H q ∂(Measure.pi fun _ : Fin 2 => ν)
      = ∏ i, fourierIntegral (psiF ψ) ν ((coset F d (k i)).indicator 1) (r i) := by
    have hH' : H = fun q => ∏ i, (psiF ψ (-(q i * r i))
        * (coset F d (k i)).indicator (1 : FiniteAdeleRing (𝓞 F) F → ℂ) (q i)) := by
      funext q
      simp only [hH]
      rw [indicator_pi_eq_prod, Fin.prod_univ_two, Fin.prod_univ_two, neg_add, AddChar.map_add_eq_mul]
      ring
    rw [hH']
    rw [integral_fintype_prod_eq_prod (𝕜 := ℂ)
      (f := fun i z => psiF ψ (-(z * r i)) * (coset F d (k i)).indicator (1 : FiniteAdeleRing (𝓞 F) F → ℂ) z)]
    rfl
  rw [hGint, hHint]

end BoxTensor

theorem prod_two_regular {A B : FiniteAdeleRing (𝓞 F) F → ℂ}
    (hA : IsLocallyConstant A) (hAc : HasCompactSupport A)
    (hB : IsLocallyConstant B) (hBc : HasCompactSupport B) :
    IsLocallyConstant (fun q : Fin 2 → FiniteAdeleRing (𝓞 F) F => A (q 0) * B (q 1)) ∧
    HasCompactSupport (fun q : Fin 2 → FiniteAdeleRing (𝓞 F) F => A (q 0) * B (q 1)) := by
  refine ⟨?_, ?_⟩
  · exact (hA.comp_continuous (continuous_apply 0)).mul (hB.comp_continuous (continuous_apply 1))
  · let S : Fin 2 → Set (FiniteAdeleRing (𝓞 F) F) := fun i => if i = 0 then tsupport A else tsupport B
    have hS : ∀ i, IsCompact (S i) := fun i => by
      by_cases hi : i = 0
      · simp only [S, if_pos hi]; exact hAc.isCompact
      · simp only [S, if_neg hi]; exact hBc.isCompact
    refine HasCompactSupport.intro (isCompact_univ_pi hS) fun q hq => ?_
    simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hq
    obtain ⟨i, hi⟩ := hq
    fin_cases i
    · have hi' : q 0 ∉ tsupport A := by simpa [S] using hi
      rw [image_eq_zero_of_notMem_tsupport hi', zero_mul]
    · have hi' : q 1 ∉ tsupport B := by simpa [S] using hi
      rw [image_eq_zero_of_notMem_tsupport hi', mul_zero]

theorem boxIndicator_regular (d : 𝓞 F) (hd : d ≠ 0) (k : Fin 2 → F) :
    IsLocallyConstant ((Set.pi Set.univ fun i => coset F d (k i)).indicator
      (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ)) ∧
    HasCompactSupport ((Set.pi Set.univ fun i => coset F d (k i)).indicator
      (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ)) := by
  have h : ((Set.pi Set.univ fun i => coset F d (k i)).indicator
      (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ))
      = fun q => (coset F d (k 0)).indicator (1 : FiniteAdeleRing (𝓞 F) F → ℂ) (q 0)
          * (coset F d (k 1)).indicator (1 : FiniteAdeleRing (𝓞 F) F → ℂ) (q 1) := by
    funext q
    rw [indicator_pi_eq_prod _ q, Fin.prod_univ_two]
  rw [h]
  obtain ⟨h0, h0c⟩ := isLocallyConstant_and_hasCompactSupport_indicator_image_integralFiniteAdeles F d hd (k 0)
  obtain ⟨h1, h1c⟩ := isLocallyConstant_and_hasCompactSupport_indicator_image_integralFiniteAdeles F d hd (k 1)
  exact prod_two_regular h0 h0c h1 h1c

theorem slice_regular {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) (x₀ : InfiniteAdeleRing F) :
    IsLocallyConstant (fun z : FiniteAdeleRing (𝓞 F) F => f (x₀, z)) ∧
    HasCompactSupport (fun z : FiniteAdeleRing (𝓞 F) F => f (x₀, z)) := by
  refine schwartzBruhat_induction
    (p := fun f _ => IsLocallyConstant (fun z : FiniteAdeleRing (𝓞 F) F => f (x₀, z)) ∧
      HasCompactSupport (fun z : FiniteAdeleRing (𝓞 F) F => f (x₀, z))) ?_ ?_ ?_ ?_ hf
  · intro f hf
    obtain ⟨g, h, hlc, hcs, rfl⟩ := hf
    exact ⟨(IsLocallyConstant.const (g (InfiniteAdeleRing.ringEquiv_mixedSpace F x₀))).mul hlc, hcs.mul_left⟩
  · exact ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  · intro f g _ _ hf hg
    exact ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  · intro c f _ hf
    exact ⟨(IsLocallyConstant.const c).mul hf.1, hf.2.mul_left⟩

theorem finite_transform_regular
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {h : FiniteAdeleRing (𝓞 F) F → ℂ} (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) :
    IsLocallyConstant (fourierIntegral (psiF ψ) ν h) ∧ HasCompactSupport (fourierIntegral (psiF ψ) ν h) := by
  borelize (AdeleRing (𝓞 F) F)
  set μ : Measure (AdeleRing (𝓞 F) F) := Measure.addHaar with hμ
  haveI : μ.IsAddHaarMeasure := inferInstanceAs (Measure.addHaar (G := AdeleRing (𝓞 F) F)).IsAddHaarMeasure
  set e := InfiniteAdeleRing.ringEquiv_mixedSpace F with he

  let b : ContDiffBump (0 : mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
  have hbs : HasCompactSupport (fun x : mixedEmbedding.mixedSpace F => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  have hbd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : mixedEmbedding.mixedSpace F => ((b x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  set g₁ : 𝓢(mixedEmbedding.mixedSpace F, ℂ) := hbs.toSchwartzMap hbd with hg₁def
  have hg₁ : ∀ x, g₁ x = ((b x : ℝ) : ℂ) := fun x => rfl

  set f : AdeleRing (𝓞 F) F → ℂ := fun x => g₁ (e x.1) * h x.2 with hfdef
  have hfmem : f ∈ schwartzBruhat F :=
    mem_schwartzBruhat_of_mem_pureTensorSet (tensor_mem_pureTensorSet g₁ h hlc hcs)
  have hFT : fourierIntegral ψ μ f ∈ schwartzBruhat F := fourierIntegral_mem_schwartzBruhat F μ hψ hfmem
  have hψu : ∀ x, ‖ψ x‖ = 1 := norm_apply_eq_one_of_isGlobalAddChar F hψ

  have hfac : ∀ z : FiniteAdeleRing (𝓞 F) F,
      fourierIntegral ψ μ f ((e.symm 0, z) : AdeleRing (𝓞 F) F)
        = ((μ (adelicBox F)).toReal /
            (ZLattice.covolume (mixedEmbedding.integerLattice F) MeasureTheory.volume
              * (ν (integralFiniteAdeles (𝓞 F) F)).toReal) : ℂ)
          * fourierIntegral
              (ψ.compAddMonoidHom ((AddMonoidHom.inl _ _).comp e.symm.toAddMonoidHom))
              MeasureTheory.volume (g₁ : mixedEmbedding.mixedSpace F → ℂ) 0
          * fourierIntegral (psiF ψ) ν h z := by
    intro z
    have h1 := fourierIntegral_pureTensor_eq F μ ν hψ.continuous hψu g₁ hlc hcs
      ((e.symm 0, z) : AdeleRing (𝓞 F) F)
    rw [show ((e.symm 0, z) : AdeleRing (𝓞 F) F).1 = e.symm 0 from rfl, RingEquiv.apply_symm_apply] at h1
    exact h1

  have harch : fourierIntegral
      (ψ.compAddMonoidHom ((AddMonoidHom.inl _ _).comp e.symm.toAddMonoidHom))
      MeasureTheory.volume (g₁ : mixedEmbedding.mixedSpace F → ℂ) 0 = ((∫ x, b x : ℝ) : ℂ) := by
    rw [fourierIntegral_def]
    simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, one_mul, hg₁]
    exact integral_ofReal
  have hpos : (0 : ℝ) < ∫ x, b x := b.integral_pos
  have hC : ((μ (adelicBox F)).toReal /
      (ZLattice.covolume (mixedEmbedding.integerLattice F) MeasureTheory.volume
        * (ν (integralFiniteAdeles (𝓞 F) F)).toReal) : ℂ) ≠ 0 := by
    have h := (map_ringEquiv_mixedSpace_eq_smul_volume_prod F μ ν).1
    have h' : (((μ (adelicBox F)).toReal /
      (ZLattice.covolume (mixedEmbedding.integerLattice F) MeasureTheory.volume
        * (ν (integralFiniteAdeles (𝓞 F) F)).toReal) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h.ne'
    push_cast at h'
    exact h'
  set K : ℂ := ((μ (adelicBox F)).toReal /
      (ZLattice.covolume (mixedEmbedding.integerLattice F) MeasureTheory.volume
        * (ν (integralFiniteAdeles (𝓞 F) F)).toReal) : ℂ) * ((∫ x, b x : ℝ) : ℂ) with hK
  have hK0 : K ≠ 0 := mul_ne_zero hC (by exact_mod_cast hpos.ne')
  have heq : fourierIntegral (psiF ψ) ν h
      = fun z => K⁻¹ * fourierIntegral ψ μ f ((e.symm 0, z) : AdeleRing (𝓞 F) F) := by
    funext z
    rw [hfac z, harch, ← hK, ← mul_assoc, inv_mul_cancel₀ hK0, one_mul]
  have hslice := slice_regular hFT (e.symm 0)
  rw [heq]
  exact ⟨(IsLocallyConstant.const K⁻¹).mul hslice.1, hslice.2.mul_left⟩

section Standard

variable [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
  (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
  {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ}

theorem boxTensor_transform_mem (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
      ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    (g : 𝓢((Fin 2 → mixedEmbedding.mixedSpace F), ℂ)) (d : 𝓞 F) (hd : d ≠ 0) (k : Fin 2 → F) :
    fourierTransform2 ψ μ (fun x : Fin 2 → AdeleRing (𝓞 F) F =>
        g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)
          * (Set.pi Set.univ fun i => coset F d (k i)).indicator
            (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) (fun i => (x i).2))
      ∈ schwartzBruhat2 F := by
  letI : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := secondCountableTopology_finiteAdeleRing
  set ν : Measure (FiniteAdeleRing (𝓞 F) F) := Measure.addHaar with hν
  haveI hV : (volume : Measure (Fin 2 → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure := inferInstance

  obtain ⟨G, hG⟩ := SchwartzMap.exists_coe_eq_vectorFourierIntegral
    (V := Fin 2 → mixedEmbedding.mixedSpace F) volume (B2 F) B2_nondegenerate g

  have hreg : ∀ i, IsLocallyConstant (fourierIntegral (psiF ψ) ν ((coset F d (k i)).indicator 1)) ∧
      HasCompactSupport (fourierIntegral (psiF ψ) ν ((coset F d (k i)).indicator 1)) := fun i =>
    finite_transform_regular ν hψ
      (isLocallyConstant_and_hasCompactSupport_indicator_image_integralFiniteAdeles F d hd (k i)).1
      (isLocallyConstant_and_hasCompactSupport_indicator_image_integralFiniteAdeles F d hd (k i)).2
  set H : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ := fun q =>
    fourierIntegral (psiF ψ) ν ((coset F d (k 0)).indicator 1) (q 0)
      * fourierIntegral (psiF ψ) ν ((coset F d (k 1)).indicator 1) (q 1) with hH
  obtain ⟨hHlc, hHcs⟩ := prod_two_regular (hreg 0).1 (hreg 0).2 (hreg 1).1 (hreg 1).2
  have heq : fourierTransform2 ψ μ (fun x : Fin 2 → AdeleRing (𝓞 F) F =>
        g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)
          * (Set.pi Set.univ fun i => coset F d (k i)).indicator
            (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) (fun i => (x i).2))
      = (((cst F μ ν).toNNReal : ℂ) ^ 2) • fun y : Fin 2 → AdeleRing (𝓞 F) F =>
          G (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (y i).1) * H (fun i => (y i).2) := by
    funext y
    rw [fourierTransform2_boxTensor_eq (μ := μ) (ν := ν) hψ.continuous hψ_inf g d hd k y, Pi.smul_apply,
      smul_eq_mul, hG, Fin.prod_univ_two]
    simp only [hH]
    ring
  rw [heq]
  exact Submodule.smul_mem _ _ (mem_schwartzBruhat2_of_mem_pureTensorSet2 (tensor_mem_pureTensorSet2 G H hHlc hHcs))

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
theorem fourierTransform2_add (hψc : Continuous ψ) (hψu : ∀ x, ‖ψ x‖ = 1)
    {Φ Ψ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Integrable Φ (pairHaar μ)) (hΨ : Integrable Ψ (pairHaar μ)) :
    fourierTransform2 ψ μ (Φ + Ψ) = fourierTransform2 ψ μ Φ + fourierTransform2 ψ μ Ψ := by
  funext w
  unfold fourierTransform2
  rw [Pi.add_apply]
  exact fourierIntegral_add _ _ w (integrable_kernel_mul μ hψc hψu hΦ w) (integrable_kernel_mul μ hψc hψu hΨ w)

omit [BorelSpace (AdeleRing (𝓞 F) F)] [μ.IsAddHaarMeasure] in
theorem fourierTransform2_smul (c : ℂ) (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) :
    fourierTransform2 ψ μ (c • Φ) = c • fourierTransform2 ψ μ Φ := by
  unfold fourierTransform2
  exact fourierIntegral_smul _ _ c Φ

omit [BorelSpace (AdeleRing (𝓞 F) F)] [μ.IsAddHaarMeasure] in
theorem fourierTransform2_zero :
    fourierTransform2 ψ μ (0 : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) = 0 := by
  unfold fourierTransform2
  exact fourierIntegral_zero _ _

omit [μ.IsAddHaarMeasure] in

theorem fourierTransform2_sum (hψc : Continuous ψ) (hψu : ∀ x, ‖ψ x‖ = 1)
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (Φ : ι → (Fin 2 → AdeleRing (𝓞 F) F) → ℂ)
    (h : ∀ i ∈ s, Integrable (Φ i) (pairHaar μ)) :
    fourierTransform2 ψ μ (∑ i ∈ s, c i • Φ i) = ∑ i ∈ s, c i • fourierTransform2 ψ μ (Φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using fourierTransform2_zero μ (ψ := ψ)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hint : Integrable (∑ i ∈ s, c i • Φ i) (pairHaar μ) :=
      integrable_finsetSum' _ fun i hi => (h i (Finset.mem_insert_of_mem hi)).smul (c i)
    rw [fourierTransform2_add μ hψc hψu ((h a (Finset.mem_insert_self a s)).smul (c a)) hint,
      fourierTransform2_smul, ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

theorem pureTensor_transform_mem (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
      ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ pureTensorSet2 F) :
    fourierTransform2 ψ μ Φ ∈ schwartzBruhat2 F := by
  obtain ⟨g, h, hlc, hcs, rfl⟩ := hΦ
  obtain ⟨d, hd, s, c, hh⟩ := exists_eq_sum_indicator_pi_image_integralFiniteAdeles F (Fin 2) hlc hcs
  have hψu : ∀ x, ‖ψ x‖ = 1 := norm_apply_eq_one_of_isGlobalAddChar F hψ
  set box : (Fin 2 → F) → (Fin 2 → AdeleRing (𝓞 F) F) → ℂ := fun k x =>
    g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)
      * (Set.pi Set.univ fun i => coset F d (k i)).indicator
          (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) (fun i => (x i).2) with hbox
  have key : (fun x : Fin 2 → AdeleRing (𝓞 F) F =>
        g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) * h (fun i => (x i).2))
      = ∑ k ∈ s, c k • box k := by
    funext x
    rw [hh]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, coset, hbox]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hmem : ∀ k, box k ∈ schwartzBruhat2 F := fun k => by
    obtain ⟨hl, hc⟩ := boxIndicator_regular d hd k
    exact mem_schwartzBruhat2_of_mem_pureTensorSet2 (tensor_mem_pureTensorSet2 g _ hl hc)
  have hint : ∀ k ∈ s, Integrable (box k) (pairHaar μ) := fun k _ =>
    (NumberField.AdelicFourier.continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2
      F (box k) (hmem k)).2.2.2.1 μ
  rw [key, fourierTransform2_sum μ hψ.continuous hψu s c box hint]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (boxTensor_transform_mem μ hψ hψ_inf g d hd k)

theorem transform_mem_standard (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
      ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 F) :
    fourierTransform2 ψ μ Φ ∈ schwartzBruhat2 F := by
  have hψu : ∀ x, ‖ψ x‖ = 1 := norm_apply_eq_one_of_isGlobalAddChar F hψ
  refine schwartzBruhat2_induction (p := fun Φ _ => fourierTransform2 ψ μ Φ ∈ schwartzBruhat2 F)
    (fun Φ hΦt => pureTensor_transform_mem μ hψ hψ_inf hΦt) ?_ ?_ ?_ hΦ
  · show fourierTransform2 ψ μ 0 ∈ schwartzBruhat2 F
    rw [fourierTransform2_zero]
    exact zero_mem_schwartzBruhat2
  · intro Φ Ψ hΦ hΨ ihΦ ihΨ
    show fourierTransform2 ψ μ (Φ + Ψ) ∈ schwartzBruhat2 F
    have hiΦ : Integrable Φ (pairHaar μ) :=
      (NumberField.AdelicFourier.continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2
        F Φ hΦ).2.2.2.1 μ
    have hiΨ : Integrable Ψ (pairHaar μ) :=
      (NumberField.AdelicFourier.continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2
        F Ψ hΨ).2.2.2.1 μ
    rw [fourierTransform2_add μ hψ.continuous hψu hiΦ hiΨ]
    exact Submodule.add_mem _ ihΦ ihΨ
  · intro c Φ _ ih
    show fourierTransform2 ψ μ (c • Φ) ∈ schwartzBruhat2 F
    rw [fourierTransform2_smul]
    exact Submodule.smul_mem _ c ih

end Standard

theorem mulLeft_algebraMap_inl (a : F) (x : InfiniteAdeleRing F) :
    AddMonoidHom.mulLeft (algebraMap F (AdeleRing (𝓞 F) F) a) (x, 0)
      = (algebraMap F (InfiniteAdeleRing F) a * x, 0) :=
  Prod.ext rfl (mul_zero _)

theorem isGlobalAddChar_twist {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {a : F} (ha : a ≠ 0) :
    IsGlobalAddChar F
      (ψ.compAddMonoidHom (AddMonoidHom.mulLeft (algebraMap F (AdeleRing (𝓞 F) F) a))) where
  principalInvariant α := by
    show ψ (algebraMap F _ a * algebraMap F _ α) = 1
    rw [← map_mul]
    exact hψ.principalInvariant _
  continuous := hψ.continuous.comp (continuous_const_mul _)
  nontrivial h1 := hψ.nontrivial <| by
    refine DFunLike.ext _ _ fun x => ?_
    have hx := DFunLike.congr_fun h1 (algebraMap F (AdeleRing (𝓞 F) F) a⁻¹ * x)
    rw [AddChar.one_apply] at hx ⊢
    rw [← hx]
    show ψ x = ψ (algebraMap F _ a * (algebraMap F _ a⁻¹ * x))
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]

theorem fourierTransform2_twist
    [MeasurableSpace (AdeleRing (𝓞 F) F)] (μ : Measure (AdeleRing (𝓞 F) F))
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) {a : F} (ha : a ≠ 0)
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (w : Fin 2 → AdeleRing (𝓞 F) F) :
    fourierTransform2 ψ μ Φ w
      = fourierTransform2 (ψ.compAddMonoidHom (AddMonoidHom.mulLeft (algebraMap F (AdeleRing (𝓞 F) F) a)))
          μ Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) a⁻¹ * w i) := by
  unfold fourierTransform2
  rw [fourierIntegral_def, fourierIntegral_def]
  congr 1
  funext v
  congr 1
  rw [pairChar_apply, pairChar_apply, AddChar.compAddMonoidHom_apply, AddMonoidHom.coe_mulLeft]
  congr 1
  have hinv : algebraMap F (AdeleRing (𝓞 F) F) a * algebraMap F (AdeleRing (𝓞 F) F) a⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ ha, map_one]
  simp only [Pi.neg_apply, Pi.mul_apply]
  linear_combination (v 0 * w 0 + v 1 * w 1) * hinv

theorem transform_mem
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 F) :
    fourierTransform2 ψ μ Φ ∈ schwartzBruhat2 F := by
  obtain ⟨a, ha, ha'⟩ := exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar F hψ
  set ψa := ψ.compAddMonoidHom (AddMonoidHom.mulLeft (algebraMap F (AdeleRing (𝓞 F) F) a)) with hψa
  have hψa_glob : IsGlobalAddChar F ψa := isGlobalAddChar_twist hψ ha
  have hψa_inf : ∀ x : InfiniteAdeleRing F,
      ψa (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ) := by
    intro x
    show ψ (AddMonoidHom.mulLeft (algebraMap F (AdeleRing (𝓞 F) F) a) (x, 0)) = _
    rw [mulLeft_algebraMap_inl]
    exact ha' x
  have hstd := transform_mem_standard μ hψa_glob hψa_inf hΦ

  set u : (AdeleRing (𝓞 F) F)ˣ :=
    Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom (Units.mk0 a⁻¹ (inv_ne_zero ha)) with hu
  have hucoe : (u : AdeleRing (𝓞 F) F) = algebraMap F (AdeleRing (𝓞 F) F) a⁻¹ := rfl
  have heq : fourierTransform2 ψ μ Φ = fun y => fourierTransform2 ψa μ Φ ((u : AdeleRing (𝓞 F) F) • y) := by
    funext y
    rw [fourierTransform2_twist μ ψ ha Φ y, hucoe]
    rfl
  rw [heq]
  exact (NumberField.AdelicFourier.continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2
    F _ hstd).2.2.2.2.2.1 u

def wInv : AdelicGL2 (𝓞 F) F :=
  ⟨!![0, -1; 1, 0], !![0, 1; -1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem vecMul_wInv (x : Fin 2 → AdeleRing (𝓞 F) F) :
    Matrix.vecMul x ((wInv : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = ![x 1, -x 0] := by
  funext i
  fin_cases i <;> simp [wInv, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem reflectPair_eq_comp [MeasurableSpace (AdeleRing (𝓞 F) F)] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (μ : Measure (AdeleRing (𝓞 F) F)) (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) :
    reflectPair ψ μ Φ = fun x => fourierTransform2 ψ μ Φ
      (Matrix.vecMul x ((wInv : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) := by
  funext x
  rw [vecMul_wInv]
  rfl

end NumberField.AdelicFourier.FT2StableSol

end

open MeasureTheory _root_.NumberField _root_.P2MW.S_NumberField_AdelicFourier_fourierTransform2_mem_schwartzBruhat2_and_reflectPair_mem_schwartzBruhat2.NumberField _root_.NumberField.AdelicFourier _root_.P2MW.S_NumberField_AdelicFourier_fourierTransform2_mem_schwartzBruhat2_and_reflectPair_mem_schwartzBruhat2.NumberField.AdelicFourier AutomorphicForm NumberField.AdelicFourier.FT2StableSol in

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ₁ : Measure (AdeleRing (𝓞 F) F)) [μ₁.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 F) :
    fourierTransform2 ψ μ₁ Φ ∈ schwartzBruhat2 F ∧ reflectPair ψ μ₁ Φ ∈ schwartzBruhat2 F := by
  have h := transform_mem μ₁ hψ hΦ
  refine ⟨h, ?_⟩
  rw [reflectPair_eq_comp]
  exact (NumberField.AdelicFourier.continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2
    F _ h).2.2.2.2.1 wInv

end S_NumberField_AdelicFourier_fourierTransform2_mem_schwartzBruhat2_and_reflectPair_mem_schwartzBruhat2
end P2MW
export P2MW.S_NumberField_AdelicFourier_fourierTransform2_mem_schwartzBruhat2_and_reflectPair_mem_schwartzBruhat2 (solution)
