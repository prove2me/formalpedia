-- Prove2me | solution 1 for NumberField.Idele.idelicHaar_inter_setOf_mul_ideleNorm_sq_mem_Icc_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/1b5d60d1-f7a3-5db9-b49f-193a859841e5

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one
import Theorems.Thm_NumberField_TateGlobal_exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow
import Theorems.Thm_NumberField_Idele_idelicHaar_inter_setOf_ideleNorm_mem_Icc_pos_and_lt_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_Idele_idelicHaar_inter_setOf_mul_ideleNorm_sq_mem_Icc_eq
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

noncomputable section

namespace G3vAux

open NumberField.TateGlobal
open scoped ENNReal Pointwise

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

variable (K : Type) [Field K] [NumberField K]

scoped instance countableK : Countable K := (Module.finBasis ℚ K).equivFun.toEquiv.injective.countable

scoped instance countableKunits : Countable Kˣ := Function.Injective.countable fun _ _ h => Units.ext h

scoped instance countablePrincipalIdeles : Countable ↥(M4aHerbrand.principalIdeles (𝓞 K) K) := by
  unfold M4aHerbrand.principalIdeles
  exact Function.Surjective.countable (MonoidHom.rangeRestrict_surjective _)

theorem ideleNorm_eq_one_of_mem {γ : (AdeleRing (𝓞 K) K)ˣ}
    (hγ : γ ∈ M4aHerbrand.principalIdeles (𝓞 K) K) : ideleNorm K γ = 1 := by
  obtain ⟨u, rfl⟩ := hγ
  unfold ideleNorm
  rw [NNReal.coe_eq_one]
  convert @NumberField.AdeleRing.distribHaarChar_algebraMap K _ _ (NumberField.AdelicHaar.adeleBorel (𝓞 K) K)
    (NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 K) K) u using 2 <;> rfl

theorem preimage_slab_eq (S : Set ℝ) (γ : ↥(M4aHerbrand.principalIdeles (𝓞 K) K)) :
    (fun z : (AdeleRing (𝓞 K) K)ˣ => γ • z) ⁻¹' {z | ideleNorm K z ∈ S} = {z | ideleNorm K z ∈ S} := by
  ext z
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Subgroup.smul_def, smul_eq_mul, ideleNorm_mul,
    ideleNorm_eq_one_of_mem K γ.2, one_mul]

theorem measurableSet_slab {S : Set ℝ} (hS : MeasurableSet S) :
    MeasurableSet {z : (AdeleRing (𝓞 K) K)ˣ | ideleNorm K z ∈ S} :=
  (NumberField.TateGlobal.continuous_ideleNorm K).measurable hS

theorem measurableSet_shell (c α β : ℝ) :
    MeasurableSet {u : (AdeleRing (𝓞 K) K)ˣ | c * ideleNorm K u ^ 2 ∈ Set.Icc α β} := by
  have h : Continuous fun u : (AdeleRing (𝓞 K) K)ˣ => c * ideleNorm K u ^ 2 :=
    continuous_const.mul ((NumberField.TateGlobal.continuous_ideleNorm K).pow 2)
  exact h.measurable measurableSet_Icc

theorem preimage_shell_eq (c α β : ℝ) (γ : ↥(M4aHerbrand.principalIdeles (𝓞 K) K)) :
    (fun z : (AdeleRing (𝓞 K) K)ˣ => γ • z) ⁻¹' {u | c * ideleNorm K u ^ 2 ∈ Set.Icc α β} =
      {u | c * ideleNorm K u ^ 2 ∈ Set.Icc α β} := by
  ext z
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Subgroup.smul_def, smul_eq_mul, ideleNorm_mul,
    ideleNorm_eq_one_of_mem K γ.2, one_mul]

theorem preimage_mulRight_shell (c α β : ℝ) (u₀ : (AdeleRing (𝓞 K) K)ˣ) (hu₀ : ideleNorm K u₀ ^ 2 = c) :
    (fun u : (AdeleRing (𝓞 K) K)ˣ => u * u₀) ⁻¹' {u | ideleNorm K u ^ 2 ∈ Set.Icc α β} =
      {u | c * ideleNorm K u ^ 2 ∈ Set.Icc α β} := by
  ext z
  simp only [Set.mem_preimage, Set.mem_setOf_eq, ideleNorm_mul, mul_pow, hu₀]
  rw [mul_comm]

theorem isFundamentalDomain_preimage_mulRight (Ω : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩ : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) Ω (NumberField.Idele.idelicHaar K))
    (u₀ : (AdeleRing (𝓞 K) K)ˣ) :
    IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) ((fun u : (AdeleRing (𝓞 K) K)ˣ => u * u₀) ⁻¹' Ω)
      (NumberField.Idele.idelicHaar K) :=
  hΩ.preimage_of_equiv
    (measurePreserving_mul_right (NumberField.Idele.idelicHaar K) u₀).quasiMeasurePreserving
    Function.bijective_id
    (fun γ x => by simp only [id_eq, Subgroup.smul_def, smul_eq_mul, mul_assoc])

theorem main (Ω₁ : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩ₁ : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) Ω₁ (NumberField.Idele.idelicHaar K))
    (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β) (c : ℝ) (hc : 0 < c) :
    NumberField.Idele.idelicHaar K (Ω₁ ∩ {u | c * ideleNorm K u ^ 2 ∈ Set.Icc α β}) =
        NumberField.Idele.idelicHaar K (Ω₁ ∩ {u | ideleNorm K u ^ 2 ∈ Set.Icc α β}) ∧
      NumberField.Idele.idelicHaar K (Ω₁ ∩ {u | ideleNorm K u ^ 2 ∈ Set.Icc α β}) ≠ ⊤ := by

  obtain ⟨u₀, -, hu₀⟩ :=
    NumberField.TateGlobal.exists_ideleNorm_eq_and_snd_eq_one K (Real.sqrt c) (Real.sqrt_pos.2 hc)
  have hu₀2 : ideleNorm K u₀ ^ 2 = c := by rw [hu₀, Real.sq_sqrt hc.le]
  refine ⟨?_, ?_⟩
  ·
    have hΩ₁' := isFundamentalDomain_preimage_mulRight K Ω₁ hΩ₁ u₀
    calc NumberField.Idele.idelicHaar K (Ω₁ ∩ {u | c * ideleNorm K u ^ 2 ∈ Set.Icc α β})
        = NumberField.Idele.idelicHaar K ({u | c * ideleNorm K u ^ 2 ∈ Set.Icc α β} ∩ Ω₁) := by
          rw [Set.inter_comm]
      _ = NumberField.Idele.idelicHaar K
            ({u | c * ideleNorm K u ^ 2 ∈ Set.Icc α β} ∩ (fun u : (AdeleRing (𝓞 K) K)ˣ => u * u₀) ⁻¹' Ω₁) :=
          hΩ₁.measure_set_eq hΩ₁' (measurableSet_shell K c α β) (preimage_shell_eq K c α β)
      _ = NumberField.Idele.idelicHaar K
            ((fun u : (AdeleRing (𝓞 K) K)ˣ => u * u₀) ⁻¹' ({u | ideleNorm K u ^ 2 ∈ Set.Icc α β} ∩ Ω₁)) := by
          rw [Set.preimage_inter, preimage_mulRight_shell K c α β u₀ hu₀2]
      _ = NumberField.Idele.idelicHaar K ({u | ideleNorm K u ^ 2 ∈ Set.Icc α β} ∩ Ω₁) :=
          measure_preimage_mul_right _ u₀ _
      _ = NumberField.Idele.idelicHaar K (Ω₁ ∩ {u | ideleNorm K u ^ 2 ∈ Set.Icc α β}) := by
          rw [Set.inter_comm]
  ·
    obtain ⟨D₀, hD₀m, hD₀F, -⟩ :=
      NumberField.TateGlobal.exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow
        K (NumberField.Idele.idelicHaar K)
    have hsub : {u : (AdeleRing (𝓞 K) K)ˣ | ideleNorm K u ^ 2 ∈ Set.Icc α β} ⊆
        {z | ideleNorm K z ∈ Set.Icc (Real.sqrt α) (Real.sqrt β + 1)} := by
      intro u hu
      obtain ⟨h1, h2⟩ := hu
      have hpos : 0 ≤ ideleNorm K u := (ideleNorm_pos u).le
      refine ⟨?_, ?_⟩
      · exact (Real.sqrt_le_sqrt h1).trans_eq (Real.sqrt_sq hpos)
      · exact ((Real.sqrt_sq hpos).symm.trans_le (Real.sqrt_le_sqrt h2)).trans
          (le_add_of_nonneg_right zero_le_one)
    have hfin := (NumberField.Idele.idelicHaar_inter_setOf_ideleNorm_mem_Icc_pos_and_lt_top K D₀ hD₀m hD₀F
      (Real.sqrt α) (Real.sqrt β + 1) (Real.sqrt_pos.2 hα)
      ((Real.sqrt_le_sqrt hαβ).trans_lt (lt_add_one _))).2
    have heq : NumberField.Idele.idelicHaar K
          ({z | ideleNorm K z ∈ Set.Icc (Real.sqrt α) (Real.sqrt β + 1)} ∩ D₀) =
        NumberField.Idele.idelicHaar K
          ({z | ideleNorm K z ∈ Set.Icc (Real.sqrt α) (Real.sqrt β + 1)} ∩ Ω₁) :=
      hD₀F.measure_set_eq hΩ₁ (measurableSet_slab K measurableSet_Icc) (preimage_slab_eq K _)
    refine ne_top_of_le_ne_top ?_ (measure_mono (Set.inter_subset_inter_right Ω₁ hsub))
    rw [Set.inter_comm, ← heq, Set.inter_comm]
    exact hfin.ne

end G3vAux
p2m_reactivate "P2MW.S_NumberField_Idele_idelicHaar_inter_setOf_mul_ideleNorm_sq_mem_Icc_eq.G3vAux"

end
p2m_reactivate "P2MW.S_NumberField_Idele_idelicHaar_inter_setOf_mul_ideleNorm_sq_mem_Icc_eq.G3vAux"

theorem solution
    (L : Type) [Field L] [NumberField L]
    (Ω₁ : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩ₁ : @IsFundamentalDomain (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range _ _ _
      (NumberField.Idele.ideleBorel L) Ω₁ (NumberField.Idele.idelicHaar L))
    (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β) (c : ℝ) (hc : 0 < c) :
    NumberField.Idele.idelicHaar L (Ω₁ ∩ {u | c * NumberField.TateGlobal.ideleNorm L u ^ 2 ∈ Set.Icc α β}) =
        NumberField.Idele.idelicHaar L (Ω₁ ∩ {u | NumberField.TateGlobal.ideleNorm L u ^ 2 ∈ Set.Icc α β}) ∧
      NumberField.Idele.idelicHaar L (Ω₁ ∩ {u | NumberField.TateGlobal.ideleNorm L u ^ 2 ∈ Set.Icc α β}) ≠ ⊤ :=
  G3vAux.main L Ω₁ hΩ₁ α β hα hαβ c hc

end S_NumberField_Idele_idelicHaar_inter_setOf_mul_ideleNorm_sq_mem_Icc_eq
end P2MW
export P2MW.S_NumberField_Idele_idelicHaar_inter_setOf_mul_ideleNorm_sq_mem_Icc_eq (solution)
