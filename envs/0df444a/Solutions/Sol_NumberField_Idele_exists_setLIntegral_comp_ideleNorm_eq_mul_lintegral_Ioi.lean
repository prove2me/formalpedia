-- Prove2me | solution 1 for NumberField.Idele.exists_setLIntegral_comp_ideleNorm_eq_mul_lintegral_Ioi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/20ee3d6c-04ef-53ee-9d09-68a9aaa4e304

import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Theorems.Thm_NumberField_Idele_exists_setLIntegral_indicator_ideleNorm_sq_mul_mem_Icc_eq_const
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_Idele_exists_setLIntegral_comp_ideleNorm_eq_mul_lintegral_Ioi
p2m_attr_erase "instance" "FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.TateGlobal
open scoped ENNReal
open scoped Topology

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

private theorem sq_mul_exp_mem_Icc_iff {K : Type} [Field K] [NumberField K]
    (z : (AdeleRing (𝓞 K) K)ˣ) (u v t : ℝ) :
    ideleNorm K z ^ 2 * Real.exp t ∈ Set.Icc (Real.exp (2 * u)) (Real.exp (2 * v)) ↔
      Real.log (ideleNorm K z) ∈ Set.Icc (u - t / 2) (v - t / 2) := by
  have hz : 0 < ideleNorm K z := ideleNorm_pos z
  have h1 : Real.exp (2 * Real.log (ideleNorm K z)) = ideleNorm K z ^ 2 := by
    rw [show (2 : ℝ) * Real.log (ideleNorm K z) = Real.log (ideleNorm K z) + Real.log (ideleNorm K z) by ring,
      Real.exp_add, Real.exp_log hz, sq]
  simp only [Set.mem_Icc]
  rw [← h1, ← Real.exp_add, Real.exp_le_exp, Real.exp_le_exp]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

private theorem setOf_sq_mul_exp_mem_Icc {K : Type} [Field K] [NumberField K] (u v t : ℝ) :
    {z : (AdeleRing (𝓞 K) K)ˣ | ideleNorm K z ^ 2 * Real.exp t ∈ Set.Icc (Real.exp (2 * u)) (Real.exp (2 * v))} =
      {z | Real.log (ideleNorm K z) ∈ Set.Icc (u - t / 2) (v - t / 2)} :=
  Set.ext fun z => sq_mul_exp_mem_Icc_iff z u v t

private theorem measure_window_sub_eq (K : Type) [Field K] [NumberField K]
    (D : Set (AdeleRing (𝓞 K) K)ˣ) (hD : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K))
    {u v : ℝ} (huv : u < v) (t : ℝ) :
    NumberField.Idele.idelicHaar K (D ∩ {z | Real.log (ideleNorm K z) ∈ Set.Icc (u - t / 2) (v - t / 2)}) =
      NumberField.Idele.idelicHaar K (D ∩ {z | Real.log (ideleNorm K z) ∈ Set.Icc u v}) := by
  obtain ⟨C, -, -, hC⟩ := NumberField.Idele.exists_setLIntegral_indicator_ideleNorm_sq_mul_mem_Icc_eq_const K D hD
    hDF (Real.exp (2 * u)) (Real.exp (2 * v)) (Real.exp_pos _) (Real.exp_lt_exp.2 (by linarith))
  have h₁ := hC (Real.exp t) (Real.exp_pos t)
  have h₂ := hC (Real.exp 0) (Real.exp_pos 0)
  rw [setOf_sq_mul_exp_mem_Icc] at h₁ h₂
  simp only [zero_div, sub_zero] at h₂
  rw [h₁, h₂]

private theorem measure_window_ne_zero_and_ne_top (K : Type) [Field K] [NumberField K]
    (D : Set (AdeleRing (𝓞 K) K)ˣ) (hD : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K))
    {u v : ℝ} (huv : u < v) :
    NumberField.Idele.idelicHaar K (D ∩ {z | Real.log (ideleNorm K z) ∈ Set.Icc u v}) ≠ 0 ∧
      NumberField.Idele.idelicHaar K (D ∩ {z | Real.log (ideleNorm K z) ∈ Set.Icc u v}) ≠ ∞ := by
  obtain ⟨C, hC0, hCtop, hC⟩ := NumberField.Idele.exists_setLIntegral_indicator_ideleNorm_sq_mul_mem_Icc_eq_const K D
    hD hDF (Real.exp (2 * u)) (Real.exp (2 * v)) (Real.exp_pos _) (Real.exp_lt_exp.2 (by linarith))
  have h₂ := hC (Real.exp 0) (Real.exp_pos 0)
  rw [setOf_sq_mul_exp_mem_Icc] at h₂
  simp only [zero_div, sub_zero] at h₂
  rw [h₂]
  exact ⟨hC0, hCtop⟩

private theorem measurable_log_ideleNorm (K : Type) [Field K] [NumberField K] :
    Measurable fun z : (AdeleRing (𝓞 K) K)ˣ => Real.log (ideleNorm K z) :=
  Real.measurable_log.comp (NumberField.TateGlobal.continuous_ideleNorm K).measurable

private noncomputable def logNormMeasure (K : Type) [Field K] [NumberField K] (D : Set (AdeleRing (𝓞 K) K)ˣ) :
    Measure ℝ :=
  Measure.map (fun z => Real.log (ideleNorm K z)) ((NumberField.Idele.idelicHaar K).restrict D)

private theorem logNormMeasure_Icc (K : Type) [Field K] [NumberField K] (D : Set (AdeleRing (𝓞 K) K)ˣ) (u v : ℝ) :
    logNormMeasure K D (Set.Icc u v) =
      NumberField.Idele.idelicHaar K (D ∩ {z | Real.log (ideleNorm K z) ∈ Set.Icc u v}) := by
  rw [logNormMeasure, Measure.map_apply (measurable_log_ideleNorm K) measurableSet_Icc,
    Measure.restrict_apply (measurable_log_ideleNorm K measurableSet_Icc), Set.inter_comm]
  rfl

private theorem logNormMeasure_Icc_sub (K : Type) [Field K] [NumberField K]
    (D : Set (AdeleRing (𝓞 K) K)ˣ) (hD : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K))
    {u v : ℝ} (huv : u < v) (a : ℝ) :
    logNormMeasure K D (Set.Icc (u - a) (v - a)) = logNormMeasure K D (Set.Icc u v) := by
  rw [logNormMeasure_Icc, logNormMeasure_Icc]
  have h := measure_window_sub_eq K D hD hDF huv (2 * a)
  rwa [show 2 * a / 2 = a by ring] at h

private theorem Ioc_eq_iUnion_Icc {u v : ℝ} (huv : u < v) :
    Set.Ioc u v = ⋃ n : ℕ, Set.Icc (u + (v - u) / (n + 2)) v := by
  ext x
  simp only [Set.mem_Ioc, Set.mem_iUnion, Set.mem_Icc]
  constructor
  · rintro ⟨hux, hxv⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < (x - u) / (v - u) from div_pos (by linarith) (by linarith))
    refine ⟨n, ?_, hxv⟩
    have h1 : (v - u) / (n + 2) ≤ (v - u) / (n + 1) :=
      div_le_div_of_nonneg_left (by linarith) (by positivity) (by linarith)
    have h2 : (v - u) / (n + 1) < x - u := by
      have hvu : 0 < v - u := by linarith
      calc (v - u) / (n + 1) = (v - u) * (1 / (n + 1)) := by ring
        _ < (v - u) * ((x - u) / (v - u)) := mul_lt_mul_of_pos_left hn hvu
        _ = x - u := by field_simp
    linarith
  · rintro ⟨n, h1, h2⟩
    have : 0 < (v - u) / (n + 2) := div_pos (by linarith) (by positivity)
    exact ⟨by linarith, h2⟩

private theorem monotone_Icc_shrink {u v : ℝ} (huv : u < v) :
    Monotone fun n : ℕ => Set.Icc (u + (v - u) / (n + 2)) v := by
  intro n m hnm
  have hnm' : (n : ℝ) + 2 ≤ (m : ℝ) + 2 := by
    have : (n : ℝ) ≤ m := by exact_mod_cast hnm
    linarith
  have hdiv : (v - u) / (m + 2) ≤ (v - u) / (n + 2) := div_le_div_of_nonneg_left (by linarith) (by positivity) hnm'
  exact Set.Icc_subset_Icc (by linarith) le_rfl

private theorem logNormMeasure_Ioc_sub (K : Type) [Field K] [NumberField K]
    (D : Set (AdeleRing (𝓞 K) K)ˣ) (hD : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K))
    {u v : ℝ} (huv : u < v) (a : ℝ) :
    logNormMeasure K D (Set.Ioc (u - a) (v - a)) = logNormMeasure K D (Set.Ioc u v) := by
  have huv' : u - a < v - a := by linarith
  rw [Ioc_eq_iUnion_Icc huv', Ioc_eq_iUnion_Icc huv]
  have t₁ := tendsto_measure_iUnion_atTop (μ := logNormMeasure K D) (monotone_Icc_shrink huv')
  have t₂ := tendsto_measure_iUnion_atTop (μ := logNormMeasure K D) (monotone_Icc_shrink huv)
  refine tendsto_nhds_unique t₁ (t₂.congr fun n => ?_)
  simp only [Function.comp]
  have hn : u + (v - u) / (n + 2) < v := by
    have h0 : 0 < (v - u) / (n + 2) := div_pos (by linarith) (by positivity)
    have h1 : (v - u) / (n + 2) < v - u := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  have h := logNormMeasure_Icc_sub K D hD hDF hn a
  rw [show u - a + (v - a - (u - a)) / (n + 2) = u + (v - u) / (n + 2) - a by ring]
  exact h.symm

theorem solution
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdeleRing (𝓞 K) K)ˣ) (_hD : MeasurableSet D)
    (_hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K)) :
    ∃ V : ℝ≥0∞, V ≠ 0 ∧ V ≠ ∞ ∧ ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (ideleNorm K z) ∂(NumberField.Idele.idelicHaar K) =
        V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹ := by
  haveI : IsFiniteMeasureOnCompacts (logNormMeasure K D) := by
    refine ⟨fun {S} hS => ?_⟩
    obtain ⟨R, hR⟩ := hS.isBounded.subset_closedBall (0 : ℝ)
    rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at hR
    have hsub : S ⊆ Set.Icc (-(|R| + 1)) (|R| + 1) :=
      hR.trans (Set.Icc_subset_Icc (by linarith [le_abs_self R, neg_abs_le R]) (by linarith [le_abs_self R]))
    calc logNormMeasure K D S ≤ logNormMeasure K D (Set.Icc (-(|R| + 1)) (|R| + 1)) := measure_mono hsub
      _ < ∞ := by
        rw [logNormMeasure_Icc]
        exact lt_top_iff_ne_top.2
          (measure_window_ne_zero_and_ne_top K D _hD _hDF (by linarith [abs_nonneg R])).2
  haveI : (logNormMeasure K D).IsAddLeftInvariant := by
    refine ⟨fun a => ?_⟩
    symm
    refine Measure.ext_of_Ioc (logNormMeasure K D) _ fun u v huv => ?_
    rw [Measure.map_apply (measurable_const_add a) measurableSet_Ioc]
    have hpre : (fun x => a + x) ⁻¹' Set.Ioc u v = Set.Ioc (u - a) (v - a) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Ioc]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
    rw [hpre, logNormMeasure_Ioc_sub K D _hD _hDF huv a]
  have hΛ : logNormMeasure K D = Measure.addHaarScalarFactor (logNormMeasure K D) (volume : Measure ℝ) • volume :=
    Measure.isAddLeftInvariant_eq_smul (logNormMeasure K D) volume
  refine ⟨Measure.addHaarScalarFactor (logNormMeasure K D) (volume : Measure ℝ), ?_, ENNReal.coe_ne_top, ?_⟩
  · intro h0
    have hne := (measure_window_ne_zero_and_ne_top K D _hD _hDF (zero_lt_one' ℝ)).1
    apply hne
    rw [← logNormMeasure_Icc, hΛ, ENNReal.coe_eq_zero.1 h0, zero_smul, Measure.coe_zero, Pi.zero_apply]
  · intro f hf
    calc ∫⁻ z in D, f (ideleNorm K z) ∂(NumberField.Idele.idelicHaar K)
        = ∫⁻ z in D, f (Real.exp (Real.log (ideleNorm K z))) ∂(NumberField.Idele.idelicHaar K) :=
          lintegral_congr fun z => by rw [Real.exp_log (ideleNorm_pos z)]
      _ = ∫⁻ t, f (Real.exp t) ∂(logNormMeasure K D) := by
          exact (lintegral_map (f := fun t => f (Real.exp t)) (hf.comp Real.measurable_exp)
            (measurable_log_ideleNorm K)).symm
      _ = ((Measure.addHaarScalarFactor (logNormMeasure K D) (volume : Measure ℝ) : NNReal) : ℝ≥0∞) *
            ∫⁻ t, f (Real.exp t) := by
          conv_lhs => rw [hΛ]
          rw [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
      _ = ((Measure.addHaarScalarFactor (logNormMeasure K D) (volume : Measure ℝ) : NNReal) : ℝ≥0∞) *
            ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹ := by
          congr 1
          have hJ := lintegral_image_eq_lintegral_abs_deriv_mul (s := Set.univ) (f := Real.exp) (f' := Real.exp)
            MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
            (fun y => f y * ENNReal.ofReal y⁻¹)
          rw [Set.image_univ, Real.range_exp, Measure.restrict_univ] at hJ
          rw [hJ]
          refine lintegral_congr fun x => ?_
          have hx : 0 < Real.exp x := Real.exp_pos x
          rw [abs_of_pos hx, ENNReal.ofReal_inv_of_pos hx, mul_comm (f _), ← mul_assoc,
            ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.2 hx).ne' ENNReal.ofReal_ne_top, one_mul]

end S_NumberField_Idele_exists_setLIntegral_comp_ideleNorm_eq_mul_lintegral_Ioi
end P2MW
export P2MW.S_NumberField_Idele_exists_setLIntegral_comp_ideleNorm_eq_mul_lintegral_Ioi (solution)
