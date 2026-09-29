-- Prove2me | solution 1 for NumberField.AdelicFourier.tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_schwartzMap_mul_indicator_pi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/e5f69028-ca15-5b2d-96eb-0de1c4a80e1f

import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_NumberField_AdelicBox_map_ringEquiv_mixedSpace_eq_smul_volume_prod
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_ZLattice_tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral
import Theorems.Thm_ZLattice_summable_fourierIntegral_mul_fourierChar_dualSubmodule
import Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_indicator_principalCoset_finiteAdeleRing
import Theorems.Thm_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual
import Theorems.Thm_NumberField_AdelicFourier_addChar_zero_finitePart_algebraMap_eq_fourierChar_neg_trace
import Theorems.Thm_NumberField_AdelicFourier_exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar
import Theorems.Thm_NumberField_mixedEmbedding_coe_dualSubmodule_flip_traceForm_idealLattice
import Theorems.Thm_NumberField_mixedEmbedding_traceForm_mixedSpace_nondegenerate
import Theorems.Thm_NumberField_mixedEmbedding_trace_mixedEmbedding
import Theorems.Thm_NumberField_AdelicBox_absNorm_mul_measure_image_integralFiniteAdeles
import Theorems.Thm_NumberField_AdelicBox_algebraMap_mem_image_integralFiniteAdeles_iff
import Theorems.Thm_NumberField_AdelicBox_isLocallyConstant_and_hasCompactSupport_indicator_image_integralFiniteAdeles
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_schwartzMap_mul_indicator_pi
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
set_option synthInstance.maxSize 1024

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_AdelicFourier_tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_schwartzMap_mul_indicator_pi.NumberField NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_schwartzMap_mul_indicator_pi.NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain"
open scoped SchwartzMap NNReal ENNReal FourierTransform nonZeroDivisors

noncomputable section

namespace NumberField
p2m_export "NumberField" "mixedEmbedding.volume_fundamentalDomain_fractionalIdealLatticeBasis InfiniteAdeleRing mixedEmbedding.mem_idealLattice mk InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp mixedEmbedding.idealLattice mixedEmbedding.fractionalIdealLatticeBasis mixedEmbedding.fundamentalDomain_integerLattice RingOfIntegers mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace mixedEmbedding.mem_span_fractionalIdealLatticeBasis mixedEmbedding.latticeBasis AdeleRing mixedEmbedding_injective mixedEmbedding.integerLattice RingOfIntegers.coe_ne_zero_iff AdelicBox.map_ringEquiv_mixedSpace_eq_smul_volume_prod AdeleRing.secondCountableTopology mixedEmbedding.coe_dualSubmodule_flip_traceForm_idealLattice mixedEmbedding.traceForm_mixedSpace_nondegenerate mixedEmbedding.trace_mixedEmbedding"
namespace AdelicFourier
p2m_export "NumberField.AdelicFourier" "pairHaar pairChar pairChar_apply fourierTransform2 fourierIntegral fourierIntegral_def fourierIntegral_indicator_principalCoset_finiteAdeleRing forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual addChar_zero_finitePart_algebraMap_eq_fourierChar_neg_trace exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar"
namespace Poisson2Box
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

section Lattice

variable (F)

def iotaV (ξ : Fin 2 → F) : Fin 2 → mixedEmbedding.mixedSpace F := fun i => mixedEmbedding F (ξ i)

omit [NumberField F] in
theorem iotaV_add (ξ η : Fin 2 → F) : iotaV F (ξ + η) = iotaV F ξ + iotaV F η := by
  funext i; simp [iotaV]

omit [NumberField F] in
theorem iotaV_sub (ξ η : Fin 2 → F) : iotaV F (ξ - η) = iotaV F ξ - iotaV F η := by
  funext i; simp [iotaV]

theorem iotaV_injective : Function.Injective (iotaV F) := by
  intro ξ η h
  funext i
  exact (mixedEmbedding_injective F) (congr_fun h i)

variable {F}

def idl (d : 𝓞 F) (hd : d ≠ 0) : (FractionalIdeal (𝓞 F)⁰ F)ˣ :=
  Units.mk0 (FractionalIdeal.spanSingleton (𝓞 F)⁰ (d : F))
    (by rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact RingOfIntegers.coe_ne_zero_iff.mpr hd)

theorem mem_idl_iff {d : 𝓞 F} (hd : d ≠ 0) (x : F) :
    x ∈ ((idl d hd : FractionalIdeal (𝓞 F)⁰ F) : Set F) ↔ ∃ a : 𝓞 F, x = (d : F) * a := by
  show x ∈ (FractionalIdeal.spanSingleton (𝓞 F)⁰ (d : F) : FractionalIdeal (𝓞 F)⁰ F) ↔ _
  rw [FractionalIdeal.mem_spanSingleton]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, by rw [Algebra.smul_def, mul_comm]⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, by rw [Algebra.smul_def, mul_comm]⟩

def basV (d : 𝓞 F) (hd : d ≠ 0) :
    Module.Basis (Σ _ : Fin 2, Module.Free.ChooseBasisIndex ℤ (idl d hd : FractionalIdeal (𝓞 F)⁰ F))
      ℝ (Fin 2 → mixedEmbedding.mixedSpace F) :=
  Pi.basis fun _ : Fin 2 => mixedEmbedding.fractionalIdealLatticeBasis F (idl d hd)

def latL (d : 𝓞 F) (hd : d ≠ 0) : Submodule ℤ (Fin 2 → mixedEmbedding.mixedSpace F) :=
  Submodule.span ℤ (Set.range (basV d hd))

scoped instance (d : 𝓞 F) (hd : d ≠ 0) : DiscreteTopology (latL d hd) := by
  unfold latL; infer_instance

scoped instance (d : 𝓞 F) (hd : d ≠ 0) : IsZLattice ℝ (latL d hd) := by
  unfold latL; infer_instance

theorem mem_span_basis1_iff {d : 𝓞 F} (hd : d ≠ 0) (x : mixedEmbedding.mixedSpace F) :
    x ∈ Submodule.span ℤ (Set.range (mixedEmbedding.fractionalIdealLatticeBasis F (idl d hd)))
      ↔ ∃ a : 𝓞 F, x = mixedEmbedding F ((d : F) * a) := by
  rw [mixedEmbedding.mem_span_fractionalIdealLatticeBasis]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, rfl⟩ := (mem_idl_iff hd y).1 hy
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨(d : F) * a, (mem_idl_iff hd _).2 ⟨a, rfl⟩, rfl⟩

theorem mem_latL_iff {d : 𝓞 F} (hd : d ≠ 0) (v : Fin 2 → mixedEmbedding.mixedSpace F) :
    v ∈ latL d hd ↔ ∀ i, ∃ a : 𝓞 F, v i = mixedEmbedding F ((d : F) * a) := by
  have key : v ∈ latL d hd ↔ ∀ i, v i ∈ Submodule.span ℤ
      (Set.range (mixedEmbedding.fractionalIdealLatticeBasis F (idl d hd))) := by
    unfold latL basV
    rw [Module.Basis.mem_span_iff_repr_mem]
    simp only [Pi.basis_repr, Set.mem_range]
    constructor
    · intro h i
      rw [Module.Basis.mem_span_iff_repr_mem]
      intro j
      exact h ⟨i, j⟩
    · intro h ij
      have := (Module.Basis.mem_span_iff_repr_mem ℤ _ _).1 (h ij.1) ij.2
      exact this
  rw [key]
  exact forall_congr' fun i => mem_span_basis1_iff hd (v i)

theorem iotaV_sub_mem_latL {d : 𝓞 F} (hd : d ≠ 0) {k ξ : Fin 2 → F}
    (h : ∀ i, ∃ a : 𝓞 F, ξ i = k i + (d : F) * a) : iotaV F (ξ - k) ∈ latL d hd := by
  rw [mem_latL_iff]
  intro i
  obtain ⟨a, ha⟩ := h i
  refine ⟨a, ?_⟩
  simp [iotaV, ha]

def boxEquiv {d : 𝓞 F} (hd : d ≠ 0) (k : Fin 2 → F) :
    {ξ : Fin 2 → F // ∀ i, ∃ a : 𝓞 F, ξ i = k i + (d : F) * a} ≃ latL d hd :=
  Equiv.ofBijective (fun ξ => ⟨iotaV F (ξ.1 - k), iotaV_sub_mem_latL hd ξ.2⟩) (by
    constructor
    · intro ξ η h
      have h' : iotaV F (ξ.1 - k) = iotaV F (η.1 - k) := congrArg Subtype.val h
      exact Subtype.ext (sub_left_injective (iotaV_injective F h'))
    · intro x
      obtain ⟨x, hx⟩ := x
      rw [mem_latL_iff] at hx
      choose a ha using hx
      refine ⟨⟨fun i => k i + (d : F) * a i, fun i => ⟨a i, rfl⟩⟩, Subtype.ext ?_⟩
      funext i
      simp only [iotaV, Pi.sub_apply, add_sub_cancel_left]
      exact (ha i).symm)

theorem boxEquiv_apply {d : 𝓞 F} (hd : d ≠ 0) (k : Fin 2 → F)
    (ξ : {ξ : Fin 2 → F // ∀ i, ∃ a : 𝓞 F, ξ i = k i + (d : F) * a}) :
    ((boxEquiv hd k ξ : latL d hd) : Fin 2 → mixedEmbedding.mixedSpace F) = iotaV F (ξ.1 - k) := rfl

end Lattice

section Dual

variable (F)

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

variable {F}

theorem single_mem_latL {d : 𝓞 F} (hd : d ≠ 0) (i : Fin 2) {x : mixedEmbedding.mixedSpace F}
    (hx : x ∈ mixedEmbedding.idealLattice F (idl d hd)) :
    (Pi.single i x : Fin 2 → mixedEmbedding.mixedSpace F) ∈ latL d hd := by
  rw [mem_latL_iff]
  intro j
  rw [mixedEmbedding.mem_idealLattice] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨a, rfl⟩ := (mem_idl_iff hd y).1 hy
  by_cases hij : j = i
  · subst hij
    exact ⟨a, by simp⟩
  · exact ⟨0, by simp [Pi.single_eq_of_ne hij]⟩

theorem mem_dual_latL_iff {d : 𝓞 F} (hd : d ≠ 0) (y : Fin 2 → mixedEmbedding.mixedSpace F) :
    y ∈ LinearMap.BilinForm.dualSubmodule (B2 F).flip (latL d hd)
      ↔ ∀ i, y i ∈ LinearMap.BilinForm.dualSubmodule
          (Algebra.traceForm ℝ (mixedEmbedding.mixedSpace F)).flip
          (mixedEmbedding.idealLattice F (idl d hd)) := by
  simp only [LinearMap.BilinForm.mem_dualSubmodule, LinearMap.BilinForm.flip_apply,
    Algebra.traceForm_apply]
  constructor
  · intro h i x hx
    have := h (Pi.single i x) (single_mem_latL hd i hx)
    rw [B2_apply, Finset.sum_eq_single i] at this
    · simpa using this
    · intro j _ hj; simp [Pi.single_eq_of_ne hj]
    · intro h; exact absurd (Finset.mem_univ i) h
  · intro h x hx
    rw [B2_apply]
    refine Submodule.sum_mem _ fun i _ => h i (x i) ?_
    rw [mem_latL_iff] at hx
    obtain ⟨a, ha⟩ := hx i
    rw [mixedEmbedding.mem_idealLattice]
    exact ⟨(d : F) * a, (mem_idl_iff hd _).2 ⟨a, rfl⟩, ha.symm⟩

theorem mem_dual_idl_iff {d : 𝓞 F} (hd : d ≠ 0) (η : F) :
    η ∈ (FractionalIdeal.dual ℤ ℚ (idl d hd : FractionalIdeal (𝓞 F)⁰ F) : FractionalIdeal (𝓞 F)⁰ F)
      ↔ (d : F) * η ∈ (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) : FractionalIdeal (𝓞 F)⁰ F) := by
  have hI : (idl d hd : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := (idl d hd).ne_zero
  have h1 : (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := one_ne_zero' (FractionalIdeal (𝓞 F)⁰ F)
  rw [FractionalIdeal.mem_dual hI, FractionalIdeal.mem_dual h1]
  constructor
  · intro h a ha
    rw [FractionalIdeal.mem_one_iff (𝓞 F)⁰] at ha
    obtain ⟨a, rfl⟩ := ha
    have hda : (d : F) * (a : F) ∈ (idl d hd : FractionalIdeal (𝓞 F)⁰ F) :=
      (mem_idl_iff hd _).2 ⟨a, rfl⟩
    have := h _ hda
    rw [Algebra.traceForm_apply] at this ⊢
    rwa [show (d : F) * η * (algebraMap (𝓞 F) F a) = η * ((d : F) * a) by
      rw [show (algebraMap (𝓞 F) F a) = (a : F) from rfl]; ring]
  · intro h a ha
    obtain ⟨b, rfl⟩ := (mem_idl_iff hd a).1 ha
    have hb : (b : F) ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := (FractionalIdeal.mem_one_iff (𝓞 F)⁰).2 ⟨b, rfl⟩
    have := h _ hb
    rw [Algebra.traceForm_apply] at this ⊢
    rwa [show η * ((d : F) * b) = (d : F) * η * b by ring]

theorem mem_dual_latL_iff' {d : 𝓞 F} (hd : d ≠ 0) (y : Fin 2 → mixedEmbedding.mixedSpace F) :
    y ∈ LinearMap.BilinForm.dualSubmodule (B2 F).flip (latL d hd)
      ↔ ∃ η : Fin 2 → F, (∀ i, (d : F) * η i ∈
          (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) : FractionalIdeal (𝓞 F)⁰ F)) ∧
          y = iotaV F η := by
  rw [mem_dual_latL_iff hd]
  have hset := mixedEmbedding.coe_dualSubmodule_flip_traceForm_idealLattice F (idl d hd)
  constructor
  · intro h
    have h' : ∀ i, ∃ η : F, (d : F) * η ∈
        (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) : FractionalIdeal (𝓞 F)⁰ F) ∧
        y i = mixedEmbedding F η := by
      intro i
      have hi : y i ∈ (LinearMap.BilinForm.dualSubmodule
          (Algebra.traceForm ℝ (mixedEmbedding.mixedSpace F)).flip
          (mixedEmbedding.idealLattice F (idl d hd)) : Set (mixedEmbedding.mixedSpace F)) := h i
      rw [hset] at hi
      obtain ⟨η, hη, hηy⟩ := hi
      exact ⟨η, (mem_dual_idl_iff hd η).1 hη, hηy.symm⟩
    choose η hη hyη using h'
    exact ⟨η, hη, funext hyη⟩
  · rintro ⟨η, hη, rfl⟩ i
    have : mixedEmbedding F (η i) ∈ (LinearMap.BilinForm.dualSubmodule
        (Algebra.traceForm ℝ (mixedEmbedding.mixedSpace F)).flip
        (mixedEmbedding.idealLattice F (idl d hd)) : Set (mixedEmbedding.mixedSpace F)) := by
      rw [hset]
      exact ⟨η i, (mem_dual_idl_iff hd (η i)).2 (hη i), rfl⟩
    exact this

def dualEquiv {d : 𝓞 F} (hd : d ≠ 0) :
    {η : Fin 2 → F // ∀ i, (d : F) * η i ∈
        (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) : FractionalIdeal (𝓞 F)⁰ F)}
      ≃ LinearMap.BilinForm.dualSubmodule (B2 F).flip (latL d hd) :=
  Equiv.ofBijective (fun η => ⟨iotaV F η.1, (mem_dual_latL_iff' hd _).2 ⟨η.1, η.2, rfl⟩⟩) (by
    constructor
    · intro η η' h
      exact Subtype.ext (iotaV_injective F (congrArg Subtype.val h))
    · intro y
      obtain ⟨η, hη, hy⟩ := (mem_dual_latL_iff' hd y.1).1 y.2
      exact ⟨⟨η, hη⟩, Subtype.ext hy.symm⟩)

theorem dualEquiv_apply {d : 𝓞 F} (hd : d ≠ 0)
    (η : {η : Fin 2 → F // ∀ i, (d : F) * η i ∈
        (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) : FractionalIdeal (𝓞 F)⁰ F)}) :
    ((dualEquiv hd η : LinearMap.BilinForm.dualSubmodule (B2 F).flip (latL d hd)) :
      Fin 2 → mixedEmbedding.mixedSpace F) = iotaV F η.1 := rfl

theorem B2_iotaV (k η : Fin 2 → F) :
    B2 F (iotaV F k) (iotaV F η) = ∑ i : Fin 2, ((Algebra.trace ℚ F (k i * η i) : ℚ) : ℝ) := by
  rw [B2_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iotaV, iotaV, ← map_mul, mixedEmbedding.trace_mixedEmbedding]

end Dual

section LHS

theorem summable_schwartz_translate {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (g : 𝓢(V, ℂ)) (t : V) : Summable fun x : L => g (t + x) := by
  set m : ℕ := Module.finrank ℝ V + 1 with hm
  obtain ⟨C, hCpos, hC⟩ := g.decay m 0
  have hrank : Module.finrank ℤ L < m := by
    rw [ZLattice.rank ℝ L, hm]; exact Nat.lt_succ_self _
  have hs := (ZLattice.summable_norm_sub_inv_pow L m hrank (-t)).mul_left C
  refine Summable.of_norm_bounded_eventually hs ?_
  have hfin : {x : L | (x : V) = -t}.Finite := by
    refine Set.Subsingleton.finite ?_
    intro x hx y hy
    exact Subtype.ext (hx.trans hy.symm)
  rw [Filter.eventually_cofinite]
  refine hfin.subset ?_
  intro x hx
  by_contra hne
  have hne' : t + (x : V) ≠ 0 := fun h => hne (eq_neg_of_add_eq_zero_right h)
  have hpos : 0 < ‖t + (x : V)‖ := norm_pos_iff.2 hne'
  have h1 := hC (t + (x : V))
  rw [norm_iteratedFDeriv_zero] at h1
  have h2 : ‖g (t + (x : V))‖ ≤ C * ‖(x : V) - -t‖⁻¹ ^ m := by
    rw [sub_neg_eq_add, add_comm (x : V) t, inv_pow, ← div_eq_mul_inv,
      le_div_iff₀ (pow_pos hpos m), mul_comm]
    exact h1
  exact absurd h2 hx

variable (F)

theorem boxTensor_apply_algebraMap (g : 𝓢((Fin 2 → mixedEmbedding.mixedSpace F), ℂ))
    (d : 𝓞 F) (hd : d ≠ 0) (k ξ : Fin 2 → F) :
    (g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F
        ((algebraMap F (AdeleRing (𝓞 F) F) (ξ i)).1))
      * (Set.pi Set.univ fun i => (fun z : FiniteAdeleRing (𝓞 F) F ↦
            algebraMap F (FiniteAdeleRing (𝓞 F) F) (k i)
              + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F).indicator
          (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) (fun i => (algebraMap F (AdeleRing (𝓞 F) F) (ξ i)).2))
      = if (∀ i, ∃ a : 𝓞 F, ξ i = k i + (d : F) * a) then g (iotaV F ξ) else 0 := by
  have h1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((algebraMap F (AdeleRing (𝓞 F) F) (ξ i)).1))
      = iotaV F ξ := by
    funext i
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (InfiniteAdeleRing F) (ξ i)) = _
    rw [iotaV, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  rw [h1]
  have h2 : (fun i => (algebraMap F (AdeleRing (𝓞 F) F) (ξ i)).2)
      = fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i) := rfl
  rw [h2]
  by_cases h : ∀ i, ∃ a : 𝓞 F, ξ i = k i + (d : F) * a
  · rw [if_pos h, Set.indicator_of_mem, Pi.one_apply, mul_one]
    intro i _
    exact (algebraMap_mem_image_integralFiniteAdeles_iff F d hd (k i) (ξ i)).2 (h i)
  · rw [if_neg h, Set.indicator_of_notMem, mul_zero]
    intro hmem
    exact h fun i => (algebraMap_mem_image_integralFiniteAdeles_iff F d hd (k i) (ξ i)).1
      (hmem i (Set.mem_univ i))

variable {F}

theorem lhs_eq (g : 𝓢((Fin 2 → mixedEmbedding.mixedSpace F), ℂ)) (d : 𝓞 F) (hd : d ≠ 0) (k : Fin 2 → F)
    (f : (Fin 2 → F) → ℂ)
    (hf : ∀ ξ, f ξ = if (∀ i, ∃ a : 𝓞 F, ξ i = k i + (d : F) * a) then g (iotaV F ξ) else 0) :
    Summable f ∧ ∑' ξ, f ξ = ∑' x : latL d hd, g (iotaV F k + x) := by
  set S : Set (Fin 2 → F) := {ξ | ∀ i, ∃ a : 𝓞 F, ξ i = k i + (d : F) * a} with hS
  have hsupp : Function.support f ⊆ S := by
    intro ξ hξ
    by_contra h
    exact hξ (by rw [hf, if_neg (show ¬ (∀ i, ∃ a : 𝓞 F, ξ i = k i + (d : F) * a) from h)])
  have hL := summable_schwartz_translate (latL d hd) g (iotaV F k)

  have hcomp : (fun ξ : S => f ξ) = (fun x : latL d hd => g (iotaV F k + x)) ∘ boxEquiv hd k := by
    funext ξ
    simp only [Function.comp_apply, boxEquiv_apply]
    rw [hf, if_pos (show (∀ i, ∃ a : 𝓞 F, (ξ : Fin 2 → F) i = k i + (d : F) * a) from ξ.2), iotaV_sub,
      add_sub_cancel]
  have hS' : Summable (fun ξ : S => f ξ) := by
    rw [hcomp]; exact (Equiv.summable_iff (boxEquiv hd k)).2 hL
  refine ⟨(Function.Injective.summable_iff Subtype.val_injective ?_).1 hS', ?_⟩
  · intro ξ hξ
    by_contra h
    exact hξ ⟨⟨ξ, hsupp h⟩, rfl⟩
  · rw [← tsum_subtype_eq_of_support_subset hsupp,
      show (fun ξ : S => f ξ) = (fun x : latL d hd => g (iotaV F k + x)) ∘ boxEquiv hd k from hcomp]
    exact Equiv.tsum_eq (boxEquiv hd k) (fun x : latL d hd => g (iotaV F k + x))

end LHS

section RHS

variable [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
  (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
  [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
  (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure] [SigmaFinite ν]
  {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ}

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

omit [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)] [SigmaFinite ν] in

theorem finiteFactor_eq (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
      ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    (d : 𝓞 F) (hd : d ≠ 0) (k η : Fin 2 → F) :
    ∏ i, fourierIntegral (psiF ψ) ν ((coset F d (k i)).indicator 1)
        (algebraMap F (FiniteAdeleRing (𝓞 F) F) (η i))
      = (∏ i, ((ν (coset F d (k i))).toReal : ℂ))
        * (if (∀ i, (d : F) * η i ∈
              (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) : FractionalIdeal (𝓞 F)⁰ F))
            then (𝐞 (B2 F (iotaV F k) (iotaV F η)) : ℂ) else 0) := by
  have hψc : Continuous (psiF ψ) := continuous_psiF hψ.continuous
  have hfac : ∀ i, fourierIntegral (psiF ψ) ν ((coset F d (k i)).indicator 1)
        (algebraMap F (FiniteAdeleRing (𝓞 F) F) (η i))
      = ((ν (coset F d (k i))).toReal : ℂ)
        * ((𝐞 ((Algebra.trace ℚ F (k i * η i) : ℚ) : ℝ) : ℂ)
          * (if (d : F) * η i ∈
              (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) : FractionalIdeal (𝓞 F)⁰ F)
            then 1 else 0)) := by
    intro i
    have h := fourierIntegral_indicator_principalCoset_finiteAdeleRing F ν hψc d hd (k i) (η i)
    rw [show ((fun z ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) (k i)
        + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F)
        = coset F d (k i) from rfl] at h
    rw [h]

    have hphase : psiF ψ (-(algebraMap F (FiniteAdeleRing (𝓞 F) F) (k i * η i)))
        = ((𝐞 ((Algebra.trace ℚ F (k i * η i) : ℚ) : ℝ)) : ℂ) := by
      rw [← (algebraMap F (FiniteAdeleRing (𝓞 F) F)).map_neg, psiF_apply,
        addChar_zero_finitePart_algebraMap_eq_fourierChar_neg_trace F hψ hψ_inf (-(k i * η i)),
        (Algebra.trace ℚ F).map_neg, Rat.cast_neg, neg_neg]

    have hcond : (∀ z ∈ integralFiniteAdeles (𝓞 F) F,
        psiF ψ (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F) * η i) * z) = 1)
        ↔ (d : F) * η i ∈
          (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) : FractionalIdeal (𝓞 F)⁰ F) :=
      forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual F hψ hψ_inf ((d : F) * η i)
    rw [hphase]
    by_cases hc : (d : F) * η i ∈
        (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) : FractionalIdeal (𝓞 F)⁰ F)
    · rw [if_pos hc, if_pos (hcond.2 hc)]; ring
    · rw [if_neg hc, if_neg (fun h => hc (hcond.1 h))]; ring
  simp_rw [hfac]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Fintype.prod_boole]
  congr 1
  by_cases hall : ∀ i, (d : F) * η i ∈
      (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) : FractionalIdeal (𝓞 F)⁰ F)
  · rw [if_pos hall, if_pos hall, mul_one, B2_iotaV, Fin.sum_univ_two, Fin.prod_univ_two,
      AddChar.map_add_eq_mul, Circle.coe_mul]
  · rw [if_neg hall, if_neg hall, mul_zero]

theorem rhs_apply (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
      ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    (g : 𝓢((Fin 2 → mixedEmbedding.mixedSpace F), ℂ)) (d : 𝓞 F) (hd : d ≠ 0) (k η : Fin 2 → F) :
    fourierTransform2 ψ μ (fun x => g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)
        * (Set.pi Set.univ fun i => coset F d (k i)).indicator
          (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) (fun i => (x i).2))
        (fun i => algebraMap F (AdeleRing (𝓞 F) F) (η i))
      = (((cst F μ ν).toNNReal : ℂ) ^ 2 * ∏ i, ((ν (coset F d (k i))).toReal : ℂ))
        * (if (∀ i, (d : F) * η i ∈
              (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) : FractionalIdeal (𝓞 F)⁰ F))
            then VectorFourier.fourierIntegral 𝐞 volume (B2 F) g (iotaV F η)
              * (𝐞 (B2 F (iotaV F k) (iotaV F η)) : ℂ) else 0) := by
  rw [fourierTransform2_boxTensor_eq (μ := μ) (ν := ν) hψ.continuous hψ_inf g d hd k]
  have h1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((algebraMap F (AdeleRing (𝓞 F) F) (η i)).1))
      = iotaV F η := by
    funext i
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (InfiniteAdeleRing F) (η i)) = _
    rw [iotaV, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  have h2 : (fun i => fourierIntegral (psiF ψ) ν ((coset F d (k i)).indicator 1)
      ((algebraMap F (AdeleRing (𝓞 F) F) (η i)).2))
      = fun i => fourierIntegral (psiF ψ) ν ((coset F d (k i)).indicator 1)
          (algebraMap F (FiniteAdeleRing (𝓞 F) F) (η i)) := rfl
  rw [h1, show (∏ i, fourierIntegral (psiF ψ) ν ((coset F d (k i)).indicator 1)
      ((algebraMap F (AdeleRing (𝓞 F) F) (η i)).2))
      = ∏ i, fourierIntegral (psiF ψ) ν ((coset F d (k i)).indicator 1)
          (algebraMap F (FiniteAdeleRing (𝓞 F) F) (η i)) from rfl,
    finiteFactor_eq (ν := ν) hψ hψ_inf d hd k η]
  by_cases hall : ∀ i, (d : F) * η i ∈
      (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) : FractionalIdeal (𝓞 F)⁰ F)
  · rw [if_pos hall, if_pos hall]; ring
  · rw [if_neg hall, if_neg hall]; ring

theorem rhs_eq (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
      ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    (g : 𝓢((Fin 2 → mixedEmbedding.mixedSpace F), ℂ)) (d : 𝓞 F) (hd : d ≠ 0) (k : Fin 2 → F)
    (f : (Fin 2 → F) → ℂ)
    (hf : ∀ η, f η = fourierTransform2 ψ μ (fun x => g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)
        * (Set.pi Set.univ fun i => coset F d (k i)).indicator
          (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) (fun i => (x i).2))
        (fun i => algebraMap F (AdeleRing (𝓞 F) F) (η i))) :
    Summable f ∧ ∑' η, f η
      = (((cst F μ ν).toNNReal : ℂ) ^ 2 * ∏ i, ((ν (coset F d (k i))).toReal : ℂ))
        * ∑' y : LinearMap.BilinForm.dualSubmodule (B2 F).flip (latL d hd),
            VectorFourier.fourierIntegral 𝐞 volume (B2 F) g y
              * (𝐞 (B2 F (iotaV F k) y) : ℂ) := by
  haveI hV : (volume : Measure (Fin 2 → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure := inferInstance
  set K : ℂ := ((cst F μ ν).toNNReal : ℂ) ^ 2 * ∏ i, ((ν (coset F d (k i))).toReal : ℂ) with hK
  set A : (Fin 2 → mixedEmbedding.mixedSpace F) → ℂ := fun y =>
    VectorFourier.fourierIntegral 𝐞 volume (B2 F) g y * (𝐞 (B2 F (iotaV F k) y) : ℂ) with hA
  set P : (Fin 2 → F) → Prop := fun η => ∀ i, (d : F) * η i ∈
      (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) : FractionalIdeal (𝓞 F)⁰ F) with hP
  set f₀ : (Fin 2 → F) → ℂ := fun η => if P η then A (iotaV F η) else 0 with hf₀
  have hff₀ : f = fun η => K * f₀ η := by
    funext η
    rw [hf, rhs_apply (μ := μ) (ν := ν) hψ hψ_inf g d hd k η]
  have hD : Summable fun y : LinearMap.BilinForm.dualSubmodule (B2 F).flip (latL d hd) => A y :=
    ZLattice.summable_fourierIntegral_mul_fourierChar_dualSubmodule volume (B2 F) (B2_nondegenerate F)
      (latL d hd) g (iotaV F k)
  set S : Set (Fin 2 → F) := {η | P η} with hS
  have hsupp : Function.support f₀ ⊆ S := by
    intro η hη
    by_contra h
    exact hη (by simp only [hf₀]; rw [if_neg (show ¬ P η from h)])
  have hcomp : (fun η : S => f₀ η)
      = (fun y : LinearMap.BilinForm.dualSubmodule (B2 F).flip (latL d hd) => A y) ∘ dualEquiv hd := by
    funext η
    simp only [Function.comp_apply, dualEquiv_apply, hf₀]
    rw [if_pos (show P η from η.2)]
  have hS' : Summable (fun η : S => f₀ η) := by
    rw [hcomp]; exact (Equiv.summable_iff (dualEquiv hd)).2 hD
  have hf₀s : Summable f₀ := by
    refine (Function.Injective.summable_iff Subtype.val_injective ?_).1 hS'
    intro η hη
    by_contra h
    exact hη ⟨⟨η, hsupp h⟩, rfl⟩
  have hf₀t : ∑' η, f₀ η = ∑' y : LinearMap.BilinForm.dualSubmodule (B2 F).flip (latL d hd), A y := by
    rw [← tsum_subtype_eq_of_support_subset hsupp,
      show (fun η : S => f₀ η) = (fun y : LinearMap.BilinForm.dualSubmodule (B2 F).flip (latL d hd) => A y)
        ∘ dualEquiv hd from hcomp]
    exact Equiv.tsum_eq (dualEquiv hd)
      (fun y : LinearMap.BilinForm.dualSubmodule (B2 F).flip (latL d hd) => A y)
  refine ⟨?_, ?_⟩
  · rw [hff₀]; exact hf₀s.mul_left K
  · rw [hff₀, tsum_mul_left, hf₀t]

end RHS

section Constants

theorem fundamentalDomain_basV (d : 𝓞 F) (hd : d ≠ 0) :
    ZSpan.fundamentalDomain (basV d hd)
      = Set.pi Set.univ (fun _ : Fin 2 =>
          ZSpan.fundamentalDomain (mixedEmbedding.fractionalIdealLatticeBasis F (idl d hd))) := by
  ext v
  simp only [ZSpan.mem_fundamentalDomain, basV, Pi.basis_repr, Set.mem_pi, Set.mem_univ, true_implies]
  constructor
  · intro h i j; exact h ⟨i, j⟩
  · intro h ij; exact h ij.1 ij.2

theorem absNorm_idl (d : 𝓞 F) (hd : d ≠ 0) :
    ((FractionalIdeal.absNorm (idl d hd : FractionalIdeal (𝓞 F)⁰ F) : ℚ) : ℝ)
      = (Ideal.absNorm (Ideal.span {d}) : ℝ) := by
  show ((FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 F)⁰ (d : F)) : ℚ) : ℝ) = _
  rw [FractionalIdeal.absNorm_span_singleton, Ideal.absNorm_span_singleton]
  have : |Algebra.norm ℚ (d : F)| = ((Algebra.norm ℤ d).natAbs : ℚ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, Algebra.coe_norm_int]
  rw [this]
  push_cast
  rfl

theorem covolume_latL (d : 𝓞 F) (hd : d ≠ 0) :
    ZLattice.covolume (latL d hd) volume
      = ((Ideal.absNorm (Ideal.span {d}) : ℝ)
          * ZLattice.covolume (mixedEmbedding.integerLattice F) volume) ^ 2 := by
  haveI hV : (volume : Measure (Fin 2 → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure := inferInstance
  have hfd : IsAddFundamentalDomain (latL d hd) (ZSpan.fundamentalDomain (basV d hd)) volume := by
    unfold latL
    exact ZSpan.isAddFundamentalDomain (basV d hd) volume
  have hcov : (volume (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F))).toReal
      = ZLattice.covolume (mixedEmbedding.integerLattice F) volume := by
    rw [← measureReal_def]
    exact (ZLattice.covolume_eq_measure_fundamentalDomain _ _
      (mixedEmbedding.fundamentalDomain_integerLattice F)).symm
  have hnn : (0 : ℝ) ≤ ((FractionalIdeal.absNorm (idl d hd : FractionalIdeal (𝓞 F)⁰ F) : ℚ) : ℝ) := by
    exact_mod_cast FractionalIdeal.absNorm_nonneg _
  rw [ZLattice.covolume_eq_measure_fundamentalDomain (latL d hd) volume hfd, measureReal_def,
    fundamentalDomain_basV, volume_pi_pi, Fin.prod_univ_two,
    mixedEmbedding.volume_fundamentalDomain_fractionalIdealLatticeBasis, ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hnn, absNorm_idl, hcov]
  ring

theorem measureReal_coset [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure] (d : 𝓞 F) (hd : d ≠ 0) (k : F) :
    (ν (coset F d k)).toReal
      = (ν (integralFiniteAdeles (𝓞 F) F)).toReal / (Ideal.absNorm (Ideal.span {d}) : ℝ) := by
  have h := absNorm_mul_measure_image_integralFiniteAdeles F ν d hd k
  rw [show ((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
        + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F)
      = coset F d k from rfl] at h
  have hN : (Ideal.absNorm (Ideal.span {d}) : ℝ) ≠ 0 := by
    have : Ideal.absNorm (Ideal.span {d}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hd
    exact_mod_cast this
  have h' := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h'
  rw [← h']
  field_simp

end Constants

section Assembly

theorem main_std
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
      ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    (g : 𝓢((Fin 2 → mixedEmbedding.mixedSpace F), ℂ)) (d : 𝓞 F) (hd : d ≠ 0) (k : Fin 2 → F)
    {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ}
    (hΦ : Φ = fun x => g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)
      * (Set.pi Set.univ fun i => coset F d (k i)).indicator
          (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) (fun i => (x i).2)) :
    Summable (fun ξ : Fin 2 → F => Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))) ∧
    Summable (fun ξ : Fin 2 → F =>
      fourierTransform2 ψ μ Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))) ∧
    ∑' ξ : Fin 2 → F, Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))
      = (((μ (adelicBox F)).toReal : ℂ) ^ 2)⁻¹ *
          ∑' ξ : Fin 2 → F, fourierTransform2 ψ μ Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) := by

  letI : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := secondCountableTopology_finiteAdeleRing
  set ν : Measure (FiniteAdeleRing (𝓞 F) F) := Measure.addHaar with hν
  haveI hV : (volume : Measure (Fin 2 → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure := inferInstance

  obtain ⟨hLs, hLt⟩ := lhs_eq g d hd k (fun ξ => Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)))
    (fun ξ => by rw [hΦ]; exact boxTensor_apply_algebraMap F g d hd k ξ)

  obtain ⟨hRs, hRt⟩ := rhs_eq (μ := μ) (ν := ν) hψ hψ_inf g d hd k
    (fun η => fourierTransform2 ψ μ Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (η i)))
    (fun η => by rw [hΦ])

  have hP := ZLattice.tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral volume (B2 F)
    (B2_nondegenerate F) (latL d hd) g (iotaV F k)
  refine ⟨hLs, hRs, ?_⟩
  rw [hLt, hP, hRt, ← mul_assoc]
  congr 1

  have hc := (map_ringEquiv_mixedSpace_eq_smul_volume_prod F μ ν).1
  rw [show (μ (adelicBox F)).toReal /
      (ZLattice.covolume (mixedEmbedding.integerLattice F) volume
        * (ν (integralFiniteAdeles (𝓞 F) F)).toReal) = cst F μ ν from rfl] at hc
  set m : ℝ := (μ (adelicBox F)).toReal with hm
  set cov : ℝ := ZLattice.covolume (mixedEmbedding.integerLattice F) volume with hcov
  set nO : ℝ := (ν (integralFiniteAdeles (𝓞 F) F)).toReal with hnO
  set N : ℝ := (Ideal.absNorm (Ideal.span {d}) : ℝ) with hN
  have hcovpos : 0 < cov := ZLattice.covolume_pos _ _
  have hNne : N ≠ 0 := by
    have : Ideal.absNorm (Ideal.span {d}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hd
    rw [hN]; exact_mod_cast this
  have hOtop : ν (integralFiniteAdeles (𝓞 F) F) ≠ ∞ := (isCompact_integralFiniteAdeles F).measure_lt_top.ne
  have hOpos : ν (integralFiniteAdeles (𝓞 F) F) ≠ 0 :=
    ((isOpen_integralFiniteAdeles F).measure_pos ν
      ⟨0, fun v => (v.adicCompletionIntegers F).zero_mem⟩).ne'
  have hnOpos : 0 < nO := ENNReal.toReal_pos hOpos hOtop
  have hcst : cst F μ ν = m / (cov * nO) := rfl
  have hmpos : 0 < m := by
    have : m = cst F μ ν * (cov * nO) := by
      rw [hcst, div_mul_cancel₀ _ (mul_pos hcovpos hnOpos).ne']
    rw [this]; exact mul_pos hc (mul_pos hcovpos hnOpos)
  have hcoe : (((cst F μ ν).toNNReal : ℝ≥0) : ℂ) = ((cst F μ ν : ℝ) : ℂ) := by
    rw [show (((cst F μ ν).toNNReal : ℝ≥0) : ℂ) = ((((cst F μ ν).toNNReal : ℝ≥0) : ℝ) : ℂ) from rfl,
      Real.coe_toNNReal _ hc.le]
  have hcoset : ∀ i, ((ν (coset F d (k i))).toReal : ℂ) = ((nO / N : ℝ) : ℂ) := by
    intro i; rw [measureReal_coset ν d hd (k i)]
  simp_rw [hcoset]
  rw [hcoe, covolume_latL d hd, Fin.prod_univ_two, hcst]
  have hreal : ((N * cov) ^ 2)⁻¹ = (m ^ 2)⁻¹ * ((m / (cov * nO)) ^ 2 * (nO / N * (nO / N))) := by
    field_simp
  have := congrArg (fun r : ℝ => (r : ℂ)) hreal
  push_cast at this
  rw [← hN, ← hcov]
  push_cast
  exact this

end Assembly

section Twist

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

end Twist

end NumberField.AdelicFourier.Poisson2Box
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_schwartzMap_mul_indicator_pi.NumberField P2MW.S_NumberField_AdelicFourier_tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_schwartzMap_mul_indicator_pi.NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_schwartzMap_mul_indicator_pi.NumberField.AdelicFourier.Poisson2Box"
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_schwartzMap_mul_indicator_pi.NumberField P2MW.S_NumberField_AdelicFourier_tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_schwartzMap_mul_indicator_pi.NumberField.AdelicFourier"
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_schwartzMap_mul_indicator_pi.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_schwartzMap_mul_indicator_pi.NumberField P2MW.S_NumberField_AdelicFourier_tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_schwartzMap_mul_indicator_pi.NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_schwartzMap_mul_indicator_pi.NumberField.AdelicFourier.Poisson2Box"

open MeasureTheory _root_.NumberField _root_.P2MW.S_NumberField_AdelicFourier_tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_schwartzMap_mul_indicator_pi.NumberField _root_.NumberField.AdelicFourier _root_.P2MW.S_NumberField_AdelicFourier_tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_schwartzMap_mul_indicator_pi.NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm NumberField.AdelicFourier.Poisson2Box in

open scoped Classical in

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (g : SchwartzMap (Fin 2 → mixedEmbedding.mixedSpace F) ℂ) (d : 𝓞 F) (hd : d ≠ 0) (k : Fin 2 → F)
    {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ}
    (hΦ : Φ = fun x => g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)
      * (Set.pi Set.univ fun i => (fun z : FiniteAdeleRing (𝓞 F) F ↦
            algebraMap F (FiniteAdeleRing (𝓞 F) F) (k i)
              + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F).indicator
          (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) (fun i => (x i).2)) :
    Summable (fun ξ : Fin 2 → F => Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))) ∧
    Summable (fun ξ : Fin 2 → F =>
      fourierTransform2 ψ μ Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))) ∧
    ∑' ξ : Fin 2 → F, Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))
      = (((μ (adelicBox F)).toReal : ℂ) ^ 2)⁻¹ *
          ∑' ξ : Fin 2 → F, fourierTransform2 ψ μ Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) := by

  obtain ⟨a, ha0, ha⟩ := exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar F hψ
  set ψ' := ψ.compAddMonoidHom (AddMonoidHom.mulLeft (algebraMap F (AdeleRing (𝓞 F) F) a)) with hψ'
  have hψ'g : IsGlobalAddChar F ψ' := isGlobalAddChar_twist hψ ha0
  have hψ'_inf : ∀ x : InfiniteAdeleRing F,
      ψ' (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ) := by
    intro x
    show ψ (AddMonoidHom.mulLeft (algebraMap F (AdeleRing (𝓞 F) F) a) (x, 0)) = _
    rw [mulLeft_algebraMap_inl, ha x]
  have hΦ' : Φ = fun x => g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)
      * (Set.pi Set.univ fun i => coset F d (k i)).indicator
          (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) (fun i => (x i).2) := hΦ
  obtain ⟨hLs, hRs, heq⟩ := main_std μ hψ'g hψ'_inf g d hd k hΦ'

  set e : (Fin 2 → F) ≃ (Fin 2 → F) :=
    { toFun := fun η => a⁻¹ • η
      invFun := fun η => a • η
      left_inv := fun η => by
        show a • (a⁻¹ • η) = η
        rw [smul_smul, mul_inv_cancel₀ ha0, one_smul]
      right_inv := fun η => by
        show a⁻¹ • (a • η) = η
        rw [smul_smul, inv_mul_cancel₀ ha0, one_smul] } with he
  have hrel : (fun ξ : Fin 2 → F => fourierTransform2 ψ μ Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)))
      = (fun ξ : Fin 2 → F =>
          fourierTransform2 ψ' μ Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))) ∘ e := by
    funext ξ
    rw [Function.comp_apply, fourierTransform2_twist μ ψ ha0 Φ]
    congr 1
    funext i
    show algebraMap F (AdeleRing (𝓞 F) F) a⁻¹ * algebraMap F (AdeleRing (𝓞 F) F) (ξ i)
      = algebraMap F (AdeleRing (𝓞 F) F) ((a⁻¹ • ξ) i)
    rw [Pi.smul_apply, smul_eq_mul, map_mul]
  refine ⟨hLs, ?_, ?_⟩
  · rw [hrel]; exact (Equiv.summable_iff e).2 hRs
  · rw [heq, hrel]
    congr 1
    exact (Equiv.tsum_eq e (fun ξ : Fin 2 → F =>
      fourierTransform2 ψ' μ Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)))).symm

end S_NumberField_AdelicFourier_tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_schwartzMap_mul_indicator_pi
end P2MW
export P2MW.S_NumberField_AdelicFourier_tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_schwartzMap_mul_indicator_pi (solution)
