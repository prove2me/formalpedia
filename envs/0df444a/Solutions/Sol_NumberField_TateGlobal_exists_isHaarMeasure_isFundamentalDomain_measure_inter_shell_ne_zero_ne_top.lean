-- Prove2me | solution 1 for NumberField.TateGlobal.exists_isHaarMeasure_isFundamentalDomain_measure_inter_shell_ne_zero_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/d3107392-461d-58db-b171-227997ec239d

import Theorems.Thm_NumberField_TateGlobal_exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow
import Theorems.Thm_NumberField_TateGlobal_exists_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_mul_log
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_exists_isHaarMeasure_isFundamentalDomain_measure_inter_shell_ne_zero_ne_top
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg"
p2m_attr_erase "simp" "RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

namespace P2mSolIdeleShellMass

theorem one_le_exp_one : (1 : ℝ) ≤ Real.exp 1 := by
  have h := Real.add_one_le_exp (1 : ℝ)
  linarith

theorem main (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] :
    ∃ (νK : Measure (AdeleRing (𝓞 K) K)ˣ) (ΩK : Set (AdeleRing (𝓞 K) K)ˣ), νK.IsHaarMeasure ∧
      IsFundamentalDomain (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νK ∧
      νK (ΩK ∩ {y | 1 ≤ NumberField.TateGlobal.ideleNorm K y ∧
        NumberField.TateGlobal.ideleNorm K y ≤ Real.exp 1}) ≠ 0 ∧
      νK (ΩK ∩ {y | 1 ≤ NumberField.TateGlobal.ideleNorm K y ∧
        NumberField.TateGlobal.ideleNorm K y ≤ Real.exp 1}) ≠ ⊤ := by
  haveI : LocallyCompactSpace (AdeleRing (𝓞 K) K)ˣ :=
    Units.instLocallyCompactSpaceOfT1SpaceOfContinuousMul

  set ν : Measure (AdeleRing (𝓞 K) K)ˣ := Measure.haar with hν
  haveI hνH : ν.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _

  obtain ⟨D, -, hD, -⟩ :=
    NumberField.TateGlobal.exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow
      K ν
  have hD' : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range D ν := hD

  obtain ⟨C, hC0, hCtop, hCΩ⟩ :=
    NumberField.TateGlobal.exists_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_mul_log K ν
  have key := hCΩ D hD' 1 (Real.exp 1) one_pos one_le_exp_one
  have hlog : Real.log (Real.exp 1 / 1) = 1 := by rw [div_one, Real.log_exp]
  rw [hlog, ENNReal.ofReal_one, mul_one] at key
  have key' : ν (D ∩ {y | 1 ≤ NumberField.TateGlobal.ideleNorm K y ∧
      NumberField.TateGlobal.ideleNorm K y ≤ Real.exp 1}) = C := key
  refine ⟨ν, D, hνH, hD', ?_, ?_⟩
  · rw [key']; exact hC0
  · rw [key']; exact hCtop

end P2mSolIdeleShellMass

theorem solution (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] :
    ∃ (νK : Measure (AdeleRing (𝓞 K) K)ˣ) (ΩK : Set (AdeleRing (𝓞 K) K)ˣ), νK.IsHaarMeasure ∧
      IsFundamentalDomain (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νK ∧
      νK (ΩK ∩ {y | 1 ≤ NumberField.TateGlobal.ideleNorm K y ∧ NumberField.TateGlobal.ideleNorm K y ≤ Real.exp 1}) ≠ 0 ∧
      νK (ΩK ∩ {y | 1 ≤ NumberField.TateGlobal.ideleNorm K y ∧ NumberField.TateGlobal.ideleNorm K y ≤ Real.exp 1}) ≠ ⊤ :=
  P2mSolIdeleShellMass.main K

end S_NumberField_TateGlobal_exists_isHaarMeasure_isFundamentalDomain_measure_inter_shell_ne_zero_ne_top
end P2MW
export P2MW.S_NumberField_TateGlobal_exists_isHaarMeasure_isFundamentalDomain_measure_inter_shell_ne_zero_ne_top (solution)
