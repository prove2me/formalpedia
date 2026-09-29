-- Prove2me | solution 1 for NumberField.Idele.exists_setLIntegral_indicator_ideleNorm_sq_mul_mem_Icc_eq_const
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/f6138001-8c6d-550b-bdfd-9364d3c511b4

import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Group.FundamentalDomain

import Theorems.Thm_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one
import Theorems.Thm_NumberField_Idele_idelicHaar_inter_setOf_ideleNorm_mem_Icc_pos_and_lt_top
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_Idele_exists_setLIntegral_indicator_ideleNorm_sq_mul_mem_Icc_eq_const
p2m_attr_erase "instance" "FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.TateGlobal
open scoped ENNReal

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

namespace RS11CS

variable (K : Type) [Field K] [NumberField K]

private theorem ideleNorm_eq_one_of_mem_principalIdeles {γ : (AdeleRing (𝓞 K) K)ˣ}
    (hγ : γ ∈ M4aHerbrand.principalIdeles (𝓞 K) K) : ideleNorm K γ = 1 := by
  obtain ⟨a, rfl⟩ := hγ
  unfold ideleNorm
  rw [NNReal.coe_eq_one]
  convert @NumberField.AdeleRing.distribHaarChar_algebraMap K _ _ (NumberField.AdelicHaar.adeleBorel (𝓞 K) K)
    (NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 K) K) a using 2 <;> try first | with_reducible_and_instances rfl | rfl

end RS11CS

open RS11CS in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdeleRing (𝓞 K) K)ˣ) (hD : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K))
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂) :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ∞ ∧ ∀ r : ℝ, 0 < r →
      (NumberField.Idele.idelicHaar K) (D ∩ {z | ideleNorm K z ^ 2 * r ∈ Set.Icc e₁ e₂}) = C := by
  haveI := NumberField.Idele.isHaarMeasure_idelicHaar K
  haveI : Countable K := (Module.finBasis ℚ K).equivFun.toEquiv.injective.countable
  haveI : Countable Kˣ := Units.val_injective.countable
  haveI : Countable (M4aHerbrand.principalIdeles (𝓞 K) K) := by
    have h : Countable (Set.range (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K))) :=
      (Set.countable_range _).to_subtype
    exact h
  set μ := NumberField.Idele.idelicHaar K with hμ
  have hcont : Continuous (ideleNorm K) := NumberField.TateGlobal.continuous_ideleNorm K

  set S : ℝ → Set (AdeleRing (𝓞 K) K)ˣ := fun r => {z | ideleNorm K z ^ 2 * r ∈ Set.Icc e₁ e₂} with hS
  have hSm : ∀ r, MeasurableSet (S r) := fun r =>
    (isClosed_Icc.preimage ((hcont.pow 2).mul continuous_const)).measurableSet

  have he₂ : 0 < e₂ := he₁.trans he
  have hS1 : S 1 = {z | ideleNorm K z ∈ Set.Icc (Real.sqrt e₁) (Real.sqrt e₂)} := by
    ext z
    simp only [hS, Set.mem_setOf_eq, mul_one, Set.mem_Icc]
    have hz : 0 ≤ ideleNorm K z := (ideleNorm_pos z).le
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · have := Real.sqrt_le_sqrt h1; rwa [Real.sqrt_sq hz] at this
      · have := Real.sqrt_le_sqrt h2; rwa [Real.sqrt_sq hz] at this
    · rintro ⟨h1, h2⟩
      constructor
      · nlinarith [Real.sq_sqrt he₁.le, Real.sqrt_nonneg e₁]
      · nlinarith [Real.sq_sqrt he₂.le, Real.sqrt_nonneg e₂]
  obtain ⟨hpos, hfin⟩ := NumberField.Idele.idelicHaar_inter_setOf_ideleNorm_mem_Icc_pos_and_lt_top K D hD hDF
    (Real.sqrt e₁) (Real.sqrt e₂) (Real.sqrt_pos.mpr he₁) (Real.sqrt_lt_sqrt he₁.le he)
  rw [← hS1] at hpos hfin
  refine ⟨μ (D ∩ S 1), hpos.ne', hfin.ne, fun r hr => ?_⟩

  obtain ⟨s, -, hs⟩ := NumberField.TateGlobal.exists_ideleNorm_eq_and_snd_eq_one K (Real.sqrt r) (Real.sqrt_pos.mpr hr)
  set f : (AdeleRing (𝓞 K) K)ˣ → (AdeleRing (𝓞 K) K)ˣ := fun z => s * z with hf
  have hSr : S r = f ⁻¹' (S 1) := by
    ext z
    simp only [hS, hf, Set.mem_preimage, Set.mem_setOf_eq, ideleNorm_mul, hs, mul_one, mul_pow, Real.sq_sqrt hr.le]
    rw [mul_comm]

  have hpre : D ∩ f ⁻¹' (S 1) = f ⁻¹' (f '' D ∩ S 1) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨hz, h1⟩; exact ⟨⟨z, hz, rfl⟩, h1⟩
    · rintro ⟨⟨w, hw, hwz⟩, h1⟩
      have : w = z := mul_left_cancel (hwz : s * w = s * z)
      exact ⟨this ▸ hw, h1⟩
  have hsD : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) (f '' D) μ := by
    have h := hDF.image_of_equiv (ν := μ) (Equiv.mulLeft s)
      (by exact (measurePreserving_mul_left μ s⁻¹).quasiMeasurePreserving) (Equiv.refl _) (fun γ z => by
        show s * ((γ : (AdeleRing (𝓞 K) K)ˣ) * z) = (γ : (AdeleRing (𝓞 K) K)ˣ) * (s * z)
        rw [mul_left_comm])
    exact h

  have hinv : ∀ γ : M4aHerbrand.principalIdeles (𝓞 K) K, (fun z => γ • z) ⁻¹' (S 1) = S 1 := by
    intro γ
    ext z
    simp only [Set.mem_preimage, hS, Set.mem_setOf_eq, Subgroup.smul_def, smul_eq_mul, ideleNorm_mul,
      RS11CS.ideleNorm_eq_one_of_mem_principalIdeles K γ.2, one_mul]
  show μ (D ∩ S r) = μ (D ∩ S 1)
  rw [hSr, hpre, measure_preimage_mul, Set.inter_comm, hsD.measure_set_eq hDF (hSm 1) hinv, Set.inter_comm]

end S_NumberField_Idele_exists_setLIntegral_indicator_ideleNorm_sq_mul_mem_Icc_eq_const
end P2MW
export P2MW.S_NumberField_Idele_exists_setLIntegral_indicator_ideleNorm_sq_mul_mem_Icc_eq_const (solution)
