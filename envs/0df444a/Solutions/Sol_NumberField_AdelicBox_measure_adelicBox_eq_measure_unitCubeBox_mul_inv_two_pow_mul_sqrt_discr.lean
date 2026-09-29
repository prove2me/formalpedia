-- Prove2me | solution 1 for NumberField.AdelicBox.measure_adelicBox_eq_measure_unitCubeBox_mul_inv_two_pow_mul_sqrt_discr
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/82b243e1-6a66-539f-9892-c6820f116f92

import Theorems.Thm_NumberField_AdelicBox_map_ringEquiv_mixedSpace_eq_smul_volume_prod
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicBox_measure_adelicBox_eq_measure_unitCubeBox_mul_inv_two_pow_mul_sqrt_discr
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_AdelicBox_measure_adelicBox_eq_measure_unitCubeBox_mul_inv_two_pow_mul_sqrt_discr.NumberField NumberField.AdelicBox P2MW.S_NumberField_AdelicBox_measure_adelicBox_eq_measure_unitCubeBox_mul_inv_two_pow_mul_sqrt_discr.NumberField.AdelicBox NumberField.InfinitePlace IsDedekindDomain"
open scoped NNReal ENNReal

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing mixedEmbedding.volume_fundamentalDomain_latticeBasis discr mk InfinitePlace.nrComplexPlaces mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace mixedEmbedding.latticeBasis InfinitePlace AdeleRing mixedEmbedding.integerLattice AdelicBox.map_ringEquiv_mixedSpace_eq_smul_volume_prod AdelicBox.integralFiniteAdeles AdelicBox.adelicBox AdeleRing.secondCountableTopology"
namespace AdelicBox
p2m_export "NumberField.AdelicBox" "map_ringEquiv_mixedSpace_eq_smul_volume_prod integralFiniteAdeles continuous_ringEquiv_mixedSpace adelicBox isClosed_integralFiniteAdeles isCompact_integralFiniteAdeles isOpen_integralFiniteAdeles"
namespace Covolume
p2m_open "NumberField.AdelicBox NumberField"

open scoped Classical

variable (K : Type) [Field K] [NumberField K]

def cube : Set (mixedEmbedding.mixedSpace K) :=
  {y | (∀ w : {w : InfinitePlace K // w.IsReal}, y.1 w ∈ Set.Icc (0 : ℝ) 1) ∧
    ∀ w : {w : InfinitePlace K // w.IsComplex}, (y.2 w).re ∈ Set.Icc (0 : ℝ) 1 ∧ (y.2 w).im ∈ Set.Icc (0 : ℝ) 1}

def square : Set ℂ := {z | z.re ∈ Set.Icc (0 : ℝ) 1 ∧ z.im ∈ Set.Icc (0 : ℝ) 1}

theorem square_eq_preimage :
    square = Complex.measurableEquivRealProd ⁻¹' (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
  ext z
  simp only [square, Set.mem_setOf_eq, Set.mem_preimage, Complex.measurableEquivRealProd_apply, Set.mem_prod]

theorem measurableSet_square : MeasurableSet square := by
  rw [square_eq_preimage]
  exact (measurableSet_Icc.prod measurableSet_Icc).preimage Complex.measurableEquivRealProd.measurable

theorem volume_square : volume square = 1 := by
  rw [square_eq_preimage, Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Icc]
  simp

theorem cube_eq_prod :
    cube K = (Set.pi Set.univ fun _ : {w : InfinitePlace K // w.IsReal} => Set.Icc (0 : ℝ) 1) ×ˢ
      (Set.pi Set.univ fun _ : {w : InfinitePlace K // w.IsComplex} => square) := by
  ext y
  simp only [cube, square, Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ_pi]

theorem measurableSet_cube : MeasurableSet (cube K) := by
  rw [cube_eq_prod]
  exact (MeasurableSet.univ_pi fun _ => measurableSet_Icc).prod
    (MeasurableSet.univ_pi fun _ => measurableSet_square)

theorem volume_cube : volume (cube K) = 1 := by
  rw [cube_eq_prod, Measure.volume_eq_prod, Measure.prod_prod, volume_pi_pi, volume_pi_pi]
  simp [Real.volume_Icc, volume_square]

theorem measurable_split [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)] :
    Measurable (fun x : AdeleRing (𝓞 K) K => (InfiniteAdeleRing.ringEquiv_mixedSpace K x.1, x.2)) := by
  have hc1 : Continuous fun x : AdeleRing (𝓞 K) K => x.1 := continuous_fst
  have hc2 : Continuous fun x : AdeleRing (𝓞 K) K => x.2 := continuous_snd
  have h1 : Measurable fun x : AdeleRing (𝓞 K) K => InfiniteAdeleRing.ringEquiv_mixedSpace K x.1 :=
    ((continuous_ringEquiv_mixedSpace K).comp hc1).measurable
  have h2 : Measurable fun x : AdeleRing (𝓞 K) K => x.2 := hc2.measurable
  exact h1.prodMk h2

theorem coe_sqrt_nnnorm_discr :
    ((NNReal.sqrt ‖(NumberField.discr K)‖₊ : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (Real.sqrt |(NumberField.discr K : ℝ)|) := by
  have h : ((NNReal.sqrt ‖(NumberField.discr K)‖₊ : ℝ≥0) : ℝ) = Real.sqrt |(NumberField.discr K : ℝ)| := by
    rw [Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs]
  rw [← h, ENNReal.ofReal_coe_nnreal]

end NumberField.AdelicBox.Covolume

end

open MeasureTheory _root_.NumberField _root_.P2MW.S_NumberField_AdelicBox_measure_adelicBox_eq_measure_unitCubeBox_mul_inv_two_pow_mul_sqrt_discr.NumberField _root_.NumberField.InfinitePlace.NumberField _root_.NumberField.AdelicBox _root_.P2MW.S_NumberField_AdelicBox_measure_adelicBox_eq_measure_unitCubeBox_mul_inv_two_pow_mul_sqrt_discr.NumberField.AdelicBox NumberField.AdelicBox.Covolume IsDedekindDomain in
open scoped Classical NNReal ENNReal in
theorem solution
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    (μ : Measure (AdeleRing (𝓞 K) K)) (hμ : μ.IsAddHaarMeasure) :
    μ {x | ((∀ w : {w : InfinitePlace K // w.IsReal},
              (InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).1 w ∈ Set.Icc (0 : ℝ) 1) ∧
            ∀ w : {w : InfinitePlace K // w.IsComplex},
              ((InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).2 w).re ∈ Set.Icc (0 : ℝ) 1 ∧
              ((InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).2 w).im ∈ Set.Icc (0 : ℝ) 1) ∧
          x.2 ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 K) K} ≠ 0 ∧
    μ {x | ((∀ w : {w : InfinitePlace K // w.IsReal},
              (InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).1 w ∈ Set.Icc (0 : ℝ) 1) ∧
            ∀ w : {w : InfinitePlace K // w.IsComplex},
              ((InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).2 w).re ∈ Set.Icc (0 : ℝ) 1 ∧
              ((InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).2 w).im ∈ Set.Icc (0 : ℝ) 1) ∧
          x.2 ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 K) K} ≠ ⊤ ∧
    μ (NumberField.AdelicBox.adelicBox K) =
      μ {x | ((∀ w : {w : InfinitePlace K // w.IsReal},
              (InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).1 w ∈ Set.Icc (0 : ℝ) 1) ∧
            ∀ w : {w : InfinitePlace K // w.IsComplex},
              ((InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).2 w).re ∈ Set.Icc (0 : ℝ) 1 ∧
              ((InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).2 w).im ∈ Set.Icc (0 : ℝ) 1) ∧
          x.2 ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 K) K} *
        ((2 : ENNReal)⁻¹ ^ NumberField.InfinitePlace.nrComplexPlaces K *
          ENNReal.ofReal (Real.sqrt |(NumberField.discr K : ℝ)|)) := by
  haveI := hμ

  letI : MeasurableSpace (FiniteAdeleRing (𝓞 K) K) := borel _
  haveI : BorelSpace (FiniteAdeleRing (𝓞 K) K) := ⟨rfl⟩
  haveI : SecondCountableTopology (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology K
  haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 K) K) :=
    (isEmbedding_prodMkRight (0 : InfiniteAdeleRing K) :
      Topology.IsEmbedding (Prod.mk (0 : InfiniteAdeleRing K) :
        FiniteAdeleRing (𝓞 K) K → InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K)).secondCountableTopology
  set ν : Measure (FiniteAdeleRing (𝓞 K) K) := Measure.addHaar with hν

  obtain ⟨hcpos, hmap⟩ := NumberField.AdelicBox.map_ringEquiv_mixedSpace_eq_smul_volume_prod K μ ν
  set c : ℝ≥0 := ((μ (adelicBox K)).toReal /
      (ZLattice.covolume (mixedEmbedding.integerLattice K) volume *
        (ν (integralFiniteAdeles (𝓞 K) K)).toReal)).toNNReal with hc
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by
    rw [ne_eq, ENNReal.coe_eq_zero, hc]
    exact (Real.toNNReal_pos.2 hcpos).ne'
  set T := fun x : AdeleRing (𝓞 K) K => (InfiniteAdeleRing.ringEquiv_mixedSpace K x.1, x.2) with hT
  have hTm : Measurable T := measurable_split K
  set E : Set (AdeleRing (𝓞 K) K) := {x | ((∀ w : {w : InfinitePlace K // w.IsReal},
              (InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).1 w ∈ Set.Icc (0 : ℝ) 1) ∧
            ∀ w : {w : InfinitePlace K // w.IsComplex},
              ((InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).2 w).re ∈ Set.Icc (0 : ℝ) 1 ∧
              ((InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).2 w).im ∈ Set.Icc (0 : ℝ) 1) ∧
          x.2 ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 K) K} with hE

  have hEpre : E = T ⁻¹' (cube K ×ˢ integralFiniteAdeles (𝓞 K) K) := Set.ext fun x => Iff.rfl
  have hBpre : adelicBox K = T ⁻¹' (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis K) ×ˢ
      integralFiniteAdeles (𝓞 K) K) := Set.ext fun x => Iff.rfl
  have hOmeas : MeasurableSet (integralFiniteAdeles (𝓞 K) K) := (isClosed_integralFiniteAdeles K).measurableSet
  have hOtop : ν (integralFiniteAdeles (𝓞 K) K) ≠ ⊤ := (isCompact_integralFiniteAdeles K).measure_lt_top.ne
  have hOpos : ν (integralFiniteAdeles (𝓞 K) K) ≠ 0 :=
    ((isOpen_integralFiniteAdeles K).measure_pos ν ⟨0, fun v => (v.adicCompletionIntegers K).zero_mem⟩).ne'
  have hEval : μ E = c * ν (integralFiniteAdeles (𝓞 K) K) := by
    rw [hEpre, ← Measure.map_apply hTm ((measurableSet_cube K).prod hOmeas), hmap,
      Measure.coe_nnreal_smul_apply, Measure.prod_prod, volume_cube, one_mul]
  have hBval : μ (adelicBox K) = c * ((2 : ℝ≥0∞)⁻¹ ^ NumberField.InfinitePlace.nrComplexPlaces K *
      ENNReal.ofReal (Real.sqrt |(NumberField.discr K : ℝ)|)) * ν (integralFiniteAdeles (𝓞 K) K) := by
    rw [hBpre, ← Measure.map_apply hTm ((ZSpan.fundamentalDomain_measurableSet _).prod hOmeas), hmap,
      Measure.coe_nnreal_smul_apply, Measure.prod_prod, mixedEmbedding.volume_fundamentalDomain_latticeBasis,
      coe_sqrt_nnnorm_discr]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hEval]; exact mul_ne_zero hc0 hOpos
  · rw [hEval]; exact ENNReal.mul_ne_top ENNReal.coe_ne_top hOtop
  · rw [hBval, hEval]; ring

end S_NumberField_AdelicBox_measure_adelicBox_eq_measure_unitCubeBox_mul_inv_two_pow_mul_sqrt_discr
end P2MW
export P2MW.S_NumberField_AdelicBox_measure_adelicBox_eq_measure_unitCubeBox_mul_inv_two_pow_mul_sqrt_discr (solution)
