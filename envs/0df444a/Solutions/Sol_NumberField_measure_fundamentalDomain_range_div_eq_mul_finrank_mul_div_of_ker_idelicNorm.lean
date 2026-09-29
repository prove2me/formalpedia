-- Prove2me | solution 1 for NumberField.measure_fundamentalDomain_range_div_eq_mul_finrank_mul_div_of_ker_idelicNorm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/11840173-14a7-5f3a-aeed-424510fd7980

import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Theorems.Thm_NumberField_ae_exists_mk_mul_out_mem_and_measure_inter_eq_zero_preimage_unitsAct_mul_inv_of_isFundamentalDomain_subgroupOf
import Theorems.Thm_NumberField_haarQuotient_measure_eq_ofReal_finrank_mul_div_of_ae_exists_mk_mul_out_mem_of_measure_inter_eq_zero
import Theorems.Thm_NumberField_AdelicHeight_exists_forall_measureReal_inter_ideleNorm_mem_Icc_eq_mul_log_and_setIntegral_weight_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_measure_fundamentalDomain_range_div_eq_mul_finrank_mul_div_of_ker_idelicNorm
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D FLT.SmoothVectors.RightTranslationFn.toFun_smul"
p2m_attr_erase "simp" "FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add AutomorphicForm.mem_sigmaCentralizer_iff NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.preimage_mulLeft_smul"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal

namespace CovolSol

theorem integral_indicator_one_complex {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    (hs : NullMeasurableSet s μ) :
    ∫ x, s.indicator (fun _ => (1 : ℂ)) x ∂μ = ((μ s).toReal : ℂ) := by
  obtain ⟨t, -, htm, hae⟩ := hs.exists_measurable_superset_ae_eq
  rw [integral_congr_ae (indicator_ae_eq_of_ae_eq_set hae.symm), integral_indicator_const _ htm,
    measureReal_def, measure_congr hae, Complex.real_smul, mul_one]

end CovolSol

open CovolSol in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] (νZK : Measure (AdeleRing (𝓞 K) K)ˣ)
    [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)

    (AK : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hAKc : IsClosed (AK : Set (AdeleRing (𝓞 L) L)ˣ))
    (hAK : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ AK ↔ ∃ a : (AdeleRing (𝓞 K) K)ˣ,
      z = Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a)
    (μAK : Measure AK) [μAK.IsHaarMeasure]
    (hμAK : ∀ g : (AdeleRing (𝓞 L) L)ˣ → ℂ,
      ∫ a : AK, g (a : (AdeleRing (𝓞 L) L)ˣ) ∂μAK =
        ∫ a, g (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a) ∂νZK)

    (N1 : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hN1c : IsClosed (N1 : Set (AdeleRing (𝓞 L) L)ˣ))
    (hN1 : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ N1 ↔
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z = 1)
    (μN : Measure N1) [μN.IsHaarMeasure]
    (cN : ℝ) (hcN : 0 < cN)
    (hNc : ∀ g : (AdeleRing (𝓞 L) L)ˣ → ℂ,
      ∫ n : N1, g (n : (AdeleRing (𝓞 L) L)ˣ) ∂μN =
        cN * ∫ q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ,
          g (D.unitsAct σ q.out * (q.out)⁻¹) ∂(HaarQuotient.measure νZL AK μAK))

    (Θ₁ : Set N1)
    (hΘ₁ : IsFundamentalDomain
      ((((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
        (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range).subgroupOf N1) Θ₁ μN) :
    μN Θ₁ = ENNReal.ofReal (cN * (Module.finrank K L : ℝ) *
      (νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc 1 (Real.exp 1)})).toReal /
      (νZK (ΩK ∩ {a | NumberField.TateGlobal.ideleNorm K a ∈ Set.Icc 1 (Real.exp 1)})).toReal) := by
  classical

  obtain ⟨hFm, hFcov, hFdisj⟩ :=
    NumberField.ae_exists_mk_mul_out_mem_and_measure_inter_eq_zero_preimage_unitsAct_mul_inv_of_isFundamentalDomain_subgroupOf
      K L D σ hgen νZL AK hAKc hAK μAK N1 hN1c hN1 μN cN hcN hNc Θ₁ hΘ₁

  have hQF :=
    NumberField.haarQuotient_measure_eq_ofReal_finrank_mul_div_of_ae_exists_mk_mul_out_mem_of_measure_inter_eq_zero
      K L νZL ΩL hΩL νZK ΩK hΩK AK hAKc hAK μAK hμAK _ hFm hFcov hFdisj

  obtain ⟨VL, hVLpos, hVL, -⟩ :=
    NumberField.AdelicHeight.exists_forall_measureReal_inter_ideleNorm_mem_Icc_eq_mul_log_and_setIntegral_weight_comp_eq
      L L νZL ΩL hΩL (MonoidHom.id _) continuous_id 1 one_pos (fun y => by simp)
  obtain ⟨VK, hVKpos, hVK, -⟩ :=
    NumberField.AdelicHeight.exists_forall_measureReal_inter_ideleNorm_mem_Icc_eq_mul_log_and_setIntegral_weight_comp_eq
      K K νZK ΩK hΩK (MonoidHom.id _) continuous_id 1 one_pos (fun y => by simp)
  have he : (1 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have hVLeq : (νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc 1 (Real.exp 1)})).toReal = VL := by
    have h := hVL 1 (Real.exp 1) one_pos he
    rw [Real.log_exp, Real.log_one, sub_zero, mul_one, measureReal_def] at h
    exact h
  have hVKeq : (νZK (ΩK ∩ {a | NumberField.TateGlobal.ideleNorm K a ∈ Set.Icc 1 (Real.exp 1)})).toReal = VK := by
    have h := hVK 1 (Real.exp 1) one_pos he
    rw [Real.log_exp, Real.log_one, sub_zero, mul_one, measureReal_def] at h
    exact h
  rw [hVLeq, hVKeq] at hQF ⊢

  have hind := hNc ((Subtype.val '' Θ₁).indicator fun _ => (1 : ℂ))
  have hL : (fun n : N1 => (Subtype.val '' Θ₁).indicator (fun _ => (1 : ℂ)) (n : (AdeleRing (𝓞 L) L)ˣ)) =
      Θ₁.indicator fun _ => (1 : ℂ) := by
    funext n
    simp only [Set.indicator, Subtype.val_injective.mem_set_image]
  have hR : (fun q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ =>
      (Subtype.val '' Θ₁).indicator (fun _ => (1 : ℂ)) (D.unitsAct σ q.out * (q.out)⁻¹)) =
      {q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ |
          D.unitsAct σ q.out * (q.out)⁻¹ ∈ (Subtype.val '' Θ₁ : Set (AdeleRing (𝓞 L) L)ˣ)}.indicator
        fun _ => (1 : ℂ) := by
    funext q
    rfl
  rw [show (∫ n : N1, (Subtype.val '' Θ₁).indicator (fun _ => (1 : ℂ)) (n : (AdeleRing (𝓞 L) L)ˣ) ∂μN) =
      ∫ n : N1, Θ₁.indicator (fun _ => (1 : ℂ)) n ∂μN from by rw [hL]] at hind
  rw [show (∫ q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ,
        (Subtype.val '' Θ₁).indicator (fun _ => (1 : ℂ)) (D.unitsAct σ q.out * (q.out)⁻¹)
          ∂(HaarQuotient.measure νZL AK μAK)) =
      ∫ q, {q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ |
          D.unitsAct σ q.out * (q.out)⁻¹ ∈ (Subtype.val '' Θ₁ : Set (AdeleRing (𝓞 L) L)ˣ)}.indicator
        (fun _ => (1 : ℂ)) q ∂(HaarQuotient.measure νZL AK μAK) from by rw [hR]] at hind
  rw [integral_indicator_one_complex hΘ₁.nullMeasurableSet, integral_indicator_one_complex hFm, hQF] at hind

  have hnonneg : 0 ≤ (Module.finrank K L : ℝ) * VL / VK := by positivity
  rw [ENNReal.toReal_ofReal hnonneg] at hind
  have hreal : (μN Θ₁).toReal = cN * ((Module.finrank K L : ℝ) * VL / VK) := by exact_mod_cast hind
  have hpos : 0 < cN * ((Module.finrank K L : ℝ) * VL / VK) := by
    have : 0 < (Module.finrank K L : ℝ) := by exact_mod_cast Module.finrank_pos
    positivity
  have hne : μN Θ₁ ≠ ∞ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at hreal
    linarith
  rw [← ENNReal.ofReal_toReal hne, hreal]
  congr 1
  ring

end S_NumberField_measure_fundamentalDomain_range_div_eq_mul_finrank_mul_div_of_ker_idelicNorm
end P2MW
export P2MW.S_NumberField_measure_fundamentalDomain_range_div_eq_mul_finrank_mul_div_of_ker_idelicNorm (solution)
