-- Prove2me | solution 1 for NumberField.AdelicBox.map_ringEquiv_mixedSpace_eq_smul_volume_prod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/26534381-25a5-5e67-9cc6-53b420e9ec2a

import Definitions.Def_NumberField_AdelicBox
import Mathlib.Algebra.Module.ZLattice.Covolume
import Theorems.Thm_NumberField_AdelicFourier_exists_smul_eq_of_isAddHaarMeasure_adeleRing
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicBox_map_ringEquiv_mixedSpace_eq_smul_volume_prod
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_AdelicBox_map_ringEquiv_mixedSpace_eq_smul_volume_prod.NumberField NumberField.AdelicBox P2MW.S_NumberField_AdelicBox_map_ringEquiv_mixedSpace_eq_smul_volume_prod.NumberField.AdelicBox NumberField.InfinitePlace IsDedekindDomain"
open scoped NNReal ENNReal

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing mk place mixedEmbedding.fundamentalDomain_integerLattice mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace_apply InfiniteAdeleRing.ringEquiv_mixedSpace mixedEmbedding.latticeBasis InfinitePlace AdeleRing mixedEmbedding.integerLattice AdelicHaar.adeleBorel AdelicFourier.exists_smul_eq_of_isAddHaarMeasure_adeleRing AdeleRing.secondCountableTopology"
namespace AdelicBox
p2m_export "NumberField.AdelicBox" "integralFiniteAdeles infiniteBox continuous_ringEquiv_mixedSpace adelicBox measurableSet_adelicBox isCompact_integralFiniteAdeles isOpen_integralFiniteAdeles"
namespace HaarSplit
p2m_open "NumberField.AdelicBox NumberField"

open scoped Classical

variable (F : Type) [Field F] [NumberField F]

def invMixed (y : mixedEmbedding.mixedSpace F) : InfiniteAdeleRing F := fun v =>
  if hv : IsReal v then (Completion.isometryEquivRealOfIsReal hv).symm (y.1 ⟨v, hv⟩)
  else (Completion.isometryEquivComplexOfIsComplex (not_isReal_iff_isComplex.1 hv)).symm
    (y.2 ⟨v, not_isReal_iff_isComplex.1 hv⟩)

omit [NumberField F] in
theorem continuous_invMixed : Continuous (invMixed F) := by
  refine continuous_pi fun v => ?_
  by_cases hv : IsReal v
  · have : (fun y : mixedEmbedding.mixedSpace F => invMixed F y v)
        = fun y => (Completion.isometryEquivRealOfIsReal hv).symm (y.1 ⟨v, hv⟩) := by
      funext y; simp [invMixed, hv]
    rw [this]
    exact (Completion.isometryEquivRealOfIsReal hv).symm.continuous.comp
      ((continuous_apply _).comp continuous_fst)
  · have : (fun y : mixedEmbedding.mixedSpace F => invMixed F y v)
        = fun y => (Completion.isometryEquivComplexOfIsComplex (not_isReal_iff_isComplex.1 hv)).symm
            (y.2 ⟨v, not_isReal_iff_isComplex.1 hv⟩) := by
      funext y; simp [invMixed, hv]
    rw [this]
    exact (Completion.isometryEquivComplexOfIsComplex _).symm.continuous.comp
      ((continuous_apply _).comp continuous_snd)

omit [NumberField F] in
theorem ringEquiv_invMixed (y : mixedEmbedding.mixedSpace F) :
    InfiniteAdeleRing.ringEquiv_mixedSpace F (invMixed F y) = y := by
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  refine Prod.ext ?_ ?_
  · funext w
    obtain ⟨v, hv⟩ := w
    show Completion.extensionEmbeddingOfIsReal hv (invMixed F y v) = y.1 ⟨v, hv⟩
    have h1 : invMixed F y v = (Completion.isometryEquivRealOfIsReal hv).symm (y.1 ⟨v, hv⟩) := by
      simp [invMixed, hv]
    rw [h1]
    exact (Completion.isometryEquivRealOfIsReal hv).apply_symm_apply _
  · funext w
    obtain ⟨v, hv⟩ := w
    have hv' : ¬ IsReal v := not_isReal_iff_isComplex.2 hv
    show Completion.extensionEmbedding v (invMixed F y v) = y.2 ⟨v, hv⟩
    have h1 : invMixed F y v =
        (Completion.isometryEquivComplexOfIsComplex (not_isReal_iff_isComplex.1 hv')).symm
          (y.2 ⟨v, not_isReal_iff_isComplex.1 hv'⟩) := by
      simp [invMixed, hv']
    rw [h1]
    exact (Completion.isometryEquivComplexOfIsComplex _).apply_symm_apply _

omit [NumberField F] in
theorem symm_eq_invMixed :
    ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace F).symm = invMixed F := by
  funext y
  apply (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective
  rw [RingEquiv.apply_symm_apply, ringEquiv_invMixed]

omit [NumberField F] in
theorem continuous_ringEquiv_mixedSpace_symm :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  rw [symm_eq_invMixed]
  exact continuous_invMixed F

def splitEquiv : AdeleRing (𝓞 F) F ≃+ mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F :=
  AddEquiv.prodCongr (InfiniteAdeleRing.ringEquiv_mixedSpace F).toAddEquiv
    (AddEquiv.refl (FiniteAdeleRing (𝓞 F) F))

theorem splitEquiv_apply (x : AdeleRing (𝓞 F) F) :
    splitEquiv F x = (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1, x.2) := rfl

theorem splitEquiv_symm_apply (p : mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F) :
    (splitEquiv F).symm p = ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm p.1, p.2) := rfl

theorem continuous_splitEquiv : Continuous (splitEquiv F) := by
  have hc1 : Continuous fun x : AdeleRing (𝓞 F) F => x.1 := continuous_fst
  have hc2 : Continuous fun x : AdeleRing (𝓞 F) F => x.2 := continuous_snd
  have h : (splitEquiv F : AdeleRing (𝓞 F) F → mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F)
      = fun x => (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1, x.2) := rfl
  rw [h]
  exact ((continuous_ringEquiv_mixedSpace F).comp hc1).prodMk hc2

theorem continuous_splitEquiv_symm : Continuous (splitEquiv F).symm := by
  have h : ((splitEquiv F).symm :
      mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F → AdeleRing (𝓞 F) F)
      = fun p => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm p.1, p.2) : AdeleRing (𝓞 F) F) := rfl
  rw [h]
  have h1 : Continuous fun p : mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F =>
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm p.1 :=
    (continuous_ringEquiv_mixedSpace_symm F).comp continuous_fst
  have h2 : Continuous fun p : mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F => p.2 :=
    continuous_snd
  exact (h1.prodMk h2 : Continuous fun p : mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F =>
    (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm p.1, p.2) :
      InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

theorem secondCountableTopology_finiteAdeleRing :
    SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := by
  haveI : SecondCountableTopology (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology F
  exact (isEmbedding_prodMkRight (0 : InfiniteAdeleRing F) :
    Topology.IsEmbedding (Prod.mk (0 : InfiniteAdeleRing F) :
      FiniteAdeleRing (𝓞 F) F → InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)).secondCountableTopology

theorem preimage_symm_adelicBox :
    (splitEquiv F).symm ⁻¹' adelicBox F
      = ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F) ×ˢ integralFiniteAdeles (𝓞 F) F := by
  ext p
  simp only [Set.mem_preimage, adelicBox, infiniteBox, Set.mem_setOf_eq, Set.mem_prod,
    splitEquiv_symm_apply, RingEquiv.apply_symm_apply]

end NumberField.AdelicBox.HaarSplit

end

open MeasureTheory _root_.NumberField _root_.P2MW.S_NumberField_AdelicBox_map_ringEquiv_mixedSpace_eq_smul_volume_prod.NumberField _root_.NumberField.InfinitePlace.NumberField _root_.NumberField.AdelicBox _root_.P2MW.S_NumberField_AdelicBox_map_ringEquiv_mixedSpace_eq_smul_volume_prod.NumberField.AdelicBox NumberField.AdelicBox.HaarSplit IsDedekindDomain in
open scoped Classical NNReal ENNReal in

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure] :
    0 < (μ (adelicBox F)).toReal /
        (ZLattice.covolume (mixedEmbedding.integerLattice F) volume
          * (ν (integralFiniteAdeles (𝓞 F) F)).toReal) ∧
    Measure.map (fun x : AdeleRing (𝓞 F) F => (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1, x.2)) μ
      = ((μ (adelicBox F)).toReal /
          (ZLattice.covolume (mixedEmbedding.integerLattice F) volume
            * (ν (integralFiniteAdeles (𝓞 F) F)).toReal)).toNNReal
        • (volume : Measure (mixedEmbedding.mixedSpace F)).prod ν := by
  haveI : SecondCountableTopology (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology F
  haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := secondCountableTopology_finiteAdeleRing F

  set ρ : Measure (mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F) := (volume).prod ν with hρ
  haveI : ρ.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  set S := (splitEquiv F).symm with hS
  haveI hρS : (Measure.map S ρ).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map ρ S (continuous_splitEquiv_symm F) (by
      show Continuous (splitEquiv F).symm.symm
      rw [AddEquiv.symm_symm]; exact continuous_splitEquiv F)

  obtain ⟨c, hc, hμ⟩ :=
    NumberField.AdelicFourier.exists_smul_eq_of_isAddHaarMeasure_adeleRing F μ (Measure.map S ρ)

  have hTm : Measurable (splitEquiv F) := (continuous_splitEquiv F).measurable
  have hSm : Measurable S := (continuous_splitEquiv_symm F).measurable
  have hmapT : Measure.map (fun x : AdeleRing (𝓞 F) F =>
      (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1, x.2)) μ = c • ρ := by
    have h1 : (fun x : AdeleRing (𝓞 F) F => (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1, x.2))
        = (splitEquiv F : AdeleRing (𝓞 F) F → _) := rfl
    rw [h1, hμ, Measure.map_smul, Measure.map_map hTm hSm]
    have h2 : (splitEquiv F : AdeleRing (𝓞 F) F → _) ∘ S = id := by
      funext p; exact (splitEquiv F).apply_symm_apply p
    rw [h2, Measure.map_id]

  have hcov : (volume (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F))).toReal
      = ZLattice.covolume (mixedEmbedding.integerLattice F) volume :=
    (ZLattice.covolume_eq_measure_fundamentalDomain _ _
      (mixedEmbedding.fundamentalDomain_integerLattice F)).symm
  have hPtop : volume (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)) ≠ ∞ :=
    (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  have hOtop : ν (integralFiniteAdeles (𝓞 F) F) ≠ ∞ := (isCompact_integralFiniteAdeles F).measure_lt_top.ne
  have hOpos : ν (integralFiniteAdeles (𝓞 F) F) ≠ 0 :=
    ((isOpen_integralFiniteAdeles F).measure_pos ν
      ⟨0, fun v => (v.adicCompletionIntegers F).zero_mem⟩).ne'
  have hcovpos : 0 < ZLattice.covolume (mixedEmbedding.integerLattice F) volume := ZLattice.covolume_pos _ _
  have hBox : μ (adelicBox F) = c * (volume (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F))
      * ν (integralFiniteAdeles (𝓞 F) F)) := by
    have hB : MeasurableSet (adelicBox F) := by
      have h := measurableSet_adelicBox F
      have heq : (‹MeasurableSpace (AdeleRing (𝓞 F) F)›) = NumberField.AdelicHaar.adeleBorel (𝓞 F) F :=
        BorelSpace.measurable_eq
      rw [heq]; exact h
    rw [hμ, Measure.coe_nnreal_smul_apply, Measure.map_apply hSm hB, preimage_symm_adelicBox,
      hρ, Measure.prod_prod]
  have hBoxReal : (μ (adelicBox F)).toReal = c * (ZLattice.covolume (mixedEmbedding.integerLattice F) volume
      * (ν (integralFiniteAdeles (𝓞 F) F)).toReal) := by
    rw [hBox, ENNReal.toReal_mul, ENNReal.toReal_mul, hcov, ENNReal.coe_toReal]
  have hden : 0 < ZLattice.covolume (mixedEmbedding.integerLattice F) volume
      * (ν (integralFiniteAdeles (𝓞 F) F)).toReal :=
    mul_pos hcovpos (ENNReal.toReal_pos hOpos hOtop)
  have hquot : (μ (adelicBox F)).toReal /
      (ZLattice.covolume (mixedEmbedding.integerLattice F) volume
        * (ν (integralFiniteAdeles (𝓞 F) F)).toReal) = c := by
    rw [hBoxReal, mul_div_assoc, div_self hden.ne', mul_one]
  refine ⟨?_, ?_⟩
  · rw [hquot]; exact_mod_cast hc
  · rw [hmapT, hquot, Real.toNNReal_coe]

end S_NumberField_AdelicBox_map_ringEquiv_mixedSpace_eq_smul_volume_prod
end P2MW
export P2MW.S_NumberField_AdelicBox_map_ringEquiv_mixedSpace_eq_smul_volume_prod (solution)
