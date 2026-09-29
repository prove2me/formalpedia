-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_hasConductorExponentAt_le_finsum_pinnedExp_of_eulerCoeff_eq_inducedE3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/19f248a6-47c2-5996-9d69-95c8153235c8

import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Theorems.Thm_NumberField_TateGlobal_exists_finset_forall_isUnramifiedCharAt_of_continuous
import Theorems.Thm_NumberField_TateGlobal_finprod_localChar_extension_algebraMap_eq_finprod_apply_uniformizerIdele_zpow_of_ramificationIdx_eq_one_of_isUnramifiedCharAt
import Theorems.Thm_LanglandsTunnell_RankinSelberg_inducedE3_eq_neg_one_pow_mul_finprod_of_not_isRamifiedIn_of_finrank_eq_three
import Theorems.Thm_NumberField_TateGlobal_exists_isIdeleClassChar_continuous_localChar_eq_finprod_localChar_extension_algebraMap
import Theorems.Thm_NumberField_TateGlobal_eq_one_of_isIdeleClassChar_of_continuous_of_forall_localChar_eq_one
import Theorems.Thm_LanglandsTunnell_CubicInduction_finite_setOf_isRamifiedIn
import Theorems.Thm_NumberField_TateGlobal_continuous_localChar
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_of_continuous
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_eq_count_differentIdeal
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_hasConductorExponentAt_le_inducedLevelAt_of_eulerCoeff_eq_inducedE3
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_hasConductorExponentAt_le_finsum_addCharLevel_of_eulerCoeff_eq_inducedE3_one_cofinite_of_isRamifiedIn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_hasConductorExponentAt_le_finsum_pinnedExp_of_eulerCoeff_eq_inducedE3
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal ValuationSubring.lowerRamificationGroup_normal IsLocalRing.lowerRamificationGroup_normal FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype"
p2m_attr_erase "simp" "M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of"
p2m_attr_erase "simp" "IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply"
p2m_attr_erase "simp" "Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk IsLocalRing.principalUnits_zero M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr"
p2m_attr_erase "simp" "NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add ArtinL.Abelian.coeff_zero IsLocalRing.upperRamificationGroup_zero IsLocalRing.upperRamificationIndex_zero IsLocalRing.herbrandPhi_zero ValuationSubring.herbrandPhi_zero IsLocalRing.mem_upperRamificationGroup Ideal.inertia_top ValuationSubring.mem_lowerRamificationGroup IsLocalRing.pointwise_smul_maximalIdeal IsLocalRing.pointwise_smul_maximalIdeal_pow IsLocalRing.mem_lowerRamificationGroup IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf"

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField NumberField.TateGlobal NumberField.AdelicLevel AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_hasConductorExponentAt_le_finsum_pinnedExp_of_eulerCoeff_eq_inducedE3.LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda LanglandsTunnell.TateLocal"

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp TateLocal.addCharLevel TateLocal.HasConductorExponentAt RankinSelberg.inducedE3_eq_neg_one_pow_mul_finprod_of_not_isRamifiedIn_of_finrank_eq_three CubicInduction.finite_setOf_isRamifiedIn TateLocal.exists_hasConductorExponentAt_of_continuous TateLocal.addCharLevel_psiLocal_eq_count_differentIdeal CubicInduction.exists_hasConductorExponentAt_le_inducedLevelAt_of_eulerCoeff_eq_inducedE3 CubicInduction.exists_hasConductorExponentAt_le_finsum_addCharLevel_of_eulerCoeff_eq_inducedE3_one_cofinite_of_isRamifiedIn"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "IsRamifiedIn IsBadPlace inducedLevelAt inducedCoeff finite_setOf_isRamifiedIn exists_hasConductorExponentAt_le_inducedLevelAt_of_eulerCoeff_eq_inducedE3 exists_hasConductorExponentAt_le_finsum_addCharLevel_of_eulerCoeff_eq_inducedE3_one_cofinite_of_isRamifiedIn"
namespace CondExpLeFinsum
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

theorem ringHom_ext {A : Type*} [NonAssocRing A] (f g : 𝓞 ℚ →+* A) : f = g := by
  have h : f.comp Rat.ringOfIntegersEquiv.symm.toRingHom =
      g.comp Rat.ringOfIntegersEquiv.symm.toRingHom := RingHom.ext_int _ _
  refine RingHom.ext fun r => ?_
  have h1 := congrArg (fun φ : ℤ →+* A => φ (Rat.ringOfIntegersEquiv r)) h
  change f (Rat.ringOfIntegersEquiv.symm (Rat.ringOfIntegersEquiv r)) =
    g (Rat.ringOfIntegersEquiv.symm (Rat.ringOfIntegersEquiv r)) at h1
  rwa [RingEquiv.symm_apply_apply] at h1

theorem algebra_subsingleton {A : Type*} [Ring A] : Subsingleton (Algebra (𝓞 ℚ) A) :=
  ⟨fun P Q => Algebra.algebra_ext P Q fun r => by
    have := ringHom_ext (@algebraMap (𝓞 ℚ) A _ _ P) (@algebraMap (𝓞 ℚ) A _ _ Q)
    exact congrArg (fun φ : 𝓞 ℚ →+* A => φ r) this⟩

section LocalTriv

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem valued_coe_units_ne_zero (x : (v.adicCompletion F)ˣ) : Valued.v (x : v.adicCompletion F) ≠ 0 :=
  Valuation.ne_zero_of_unit Valued.v x

theorem mem_integers_and_inv_mem_of_valued_eq_one (u : (v.adicCompletion F)ˣ)
    (hu : Valued.v (u : v.adicCompletion F) = 1) :
    (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F ∧
      ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
  refine ⟨?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hu]
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]

theorem valued_eq_one_of_mem_integers_of_inv_mem (u : (v.adicCompletion F)ˣ)
    (h₁ : (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F)
    (h₂ : ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F) :
    Valued.v (u : v.adicCompletion F) = 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h₁ h₂
  refine le_antisymm h₁ ?_
  have hprod : Valued.v (u : v.adicCompletion F) * Valued.v ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      = 1 := by
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  calc (1 : WithZero (Multiplicative ℤ))
      = Valued.v (u : v.adicCompletion F) * Valued.v ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) :=
        hprod.symm
    _ ≤ Valued.v (u : v.adicCompletion F) * 1 := by gcongr
    _ = Valued.v (u : v.adicCompletion F) := mul_one _

end LocalTriv

section Transport

theorem units_map_mem_higherUnitsAt
    (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [NumberField K] [Algebra E K]
    (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 K)) (k : ℕ)
    (x : (v.adicCompletion E)ˣ) (hx : x ∈ higherUnitsAt E v k) :
    Units.map (algebraMap (v.adicCompletion E) (w.1.adicCompletion K)).toMonoidHom x ∈
      higherUnitsAt K w.1 (Ideal.ramificationIdx' v.asIdeal w.1.asIdeal * k) := by
  obtain ⟨hval, hball⟩ := hx
  have hv : ∀ y : v.adicCompletion E,
      Valued.v (algebraMap (v.adicCompletion E) (w.1.adicCompletion K) y) =
        Valued.v y ^ Ideal.ramificationIdx' v.asIdeal w.1.asIdeal := by
    intro y
    have := HeightOneSpectrum.Extension.valued_adicCompletionSemialgHom E K w y
    rw [w.2] at this
    exact this
  refine ⟨?_, ?_⟩
  · show Valued.v (algebraMap (v.adicCompletion E) (w.1.adicCompletion K) (x : v.adicCompletion E)) = 1
    rw [hv, hval, one_pow]
  · rcases Nat.eq_zero_or_pos k with hk | hk
    · left
      rw [hk, mul_zero]
    · right
      rcases hball with h0 | hle
      · omega
      show Valued.v (algebraMap (v.adicCompletion E) (w.1.adicCompletion K) (x : v.adicCompletion E) - 1) ≤ _
      rw [← map_one (algebraMap (v.adicCompletion E) (w.1.adicCompletion K)), ← map_sub, hv]
      calc Valued.v ((x : v.adicCompletion E) - 1) ^ Ideal.ramificationIdx' v.asIdeal w.1.asIdeal
          ≤ WithZero.exp (-(k : ℤ)) ^ Ideal.ramificationIdx' v.asIdeal w.1.asIdeal := pow_le_pow_left' hle _
        _ = WithZero.exp (-((Ideal.ramificationIdx' v.asIdeal w.1.asIdeal * k : ℕ) : ℤ)) := by
          rw [← WithZero.exp_nsmul, nsmul_eq_mul]; push_cast; congr 1; ring

end Transport

section Unitary

def normUnitHom : ℂˣ →* ℂˣ :=
  (Units.map (Complex.ofRealHom : ℝ →+* ℂ).toMonoidHom).comp (Units.map (normHom : ℂ →*₀ ℝ).toMonoidHom)

theorem val_normUnitHom (z : ℂˣ) : ((normUnitHom z : ℂˣ) : ℂ) = ((‖(z : ℂ)‖ : ℝ) : ℂ) := rfl

theorem continuous_normUnitHom : Continuous normUnitHom :=
  (Continuous.units_map _ Complex.continuous_ofReal).comp (Continuous.units_map _ continuous_norm)

theorem isUnitaryChar_of_forall_norm_localChar_eq_one
    (F : Type) [Field F] [NumberField F] (ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hcl : IsIdeleClassChar (𝓞 F) F ν) (hc : Continuous ν)
    (hloc : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ), ‖((localChar ν v x : ℂˣ) : ℂ)‖ = 1) :
    IsUnitaryChar (𝓞 F) F ν := by
  set ν' : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ := normUnitHom.comp ν with hν'def
  have hcl' : IsIdeleClassChar (𝓞 F) F ν' := by
    intro u
    rw [hν'def, MonoidHom.comp_apply, hcl u, map_one]
  have hc' : Continuous ν' := continuous_normUnitHom.comp hc
  have hloc' : ∀ v : HeightOneSpectrum (𝓞 F), localChar ν' v = 1 := by
    intro v
    ext x
    have h1 : localChar ν' v x = normUnitHom (localChar ν v x) := rfl
    rw [h1, val_normUnitHom, hloc v x, Complex.ofReal_one, MonoidHom.one_apply, Units.val_one]
  have h1 : ν' = 1 :=
    NumberField.TateGlobal.eq_one_of_isIdeleClassChar_of_continuous_of_forall_localChar_eq_one F ν' hcl' hc' ∅
      (fun v _ => hloc' v)
  intro z
  have hz : ν' z = 1 := by rw [h1, MonoidHom.one_apply]
  have hz' : ((normUnitHom (ν z) : ℂˣ) : ℂ) = 1 := by
    rw [hν'def, MonoidHom.comp_apply] at hz
    rw [hz, Units.val_one]
  rw [val_normUnitHom] at hz'
  exact Complex.ofReal_eq_one.mp hz'

end Unitary

section Fibre

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 ℚ))

theorem under_eq_of_mem_primeFibre (𝔓 : HeightOneSpectrum (𝓞 K)) (h𝔓 : 𝔓 ∈ primeFibre ℚ K v) :
    𝔓.asIdeal.under (𝓞 ℚ) = v.asIdeal := by
  rw [mem_primeFibre] at h𝔓; rw [← h𝔓]; rfl

theorem asIdeal_mem_primesOverFinset (𝔓 : HeightOneSpectrum (𝓞 K)) (h𝔓 : 𝔓 ∈ primeFibre ℚ K v) :
    𝔓.asIdeal ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 K) := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  rw [IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot]
  exact ⟨𝔓.isPrime, (Ideal.liesOver_iff _ _).mpr (under_eq_of_mem_primeFibre K v 𝔓 h𝔓).symm⟩

theorem finite_primeFibre : (primeFibre ℚ K v).Finite :=
  ((IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 K)).finite_toSet.preimage
    (f := fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.asIdeal) (fun a _ b _ h => HeightOneSpectrum.ext h)).subset
    (fun 𝔓 h𝔓 => asIdeal_mem_primesOverFinset K v 𝔓 h𝔓)

theorem one_le_inertiaDeg (𝔓 : HeightOneSpectrum (𝓞 K)) (h𝔓 : 𝔓 ∈ primeFibre ℚ K v) :
    1 ≤ v.asIdeal.inertiaDeg' 𝔓.asIdeal := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI : 𝔓.asIdeal.LiesOver v.asIdeal := (Ideal.liesOver_iff _ _).mpr (under_eq_of_mem_primeFibre K v 𝔓 h𝔓).symm
  exact Ideal.inertiaDeg'_pos v.asIdeal 𝔓.asIdeal

private theorem _root_.LanglandsTunnell.CubicInduction.CondExpLeFinsum.ramificationIdx_ne_zero (𝔓 : HeightOneSpectrum (𝓞 K)) (h𝔓 : 𝔓 ∈ primeFibre ℚ K v) :
    Ideal.ramificationIdx' v.asIdeal 𝔓.asIdeal ≠ 0 := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  have hP' := (IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot (𝓞 K)).mp
    (asIdeal_mem_primesOverFinset K v 𝔓 h𝔓)
  exact Ideal.IsDedekindDomain.ramificationIdx_ne_zero
    ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 ℚ) (𝓞 K))).not.mpr v.ne_bot) hP'.1
    (Ideal.map_le_iff_le_comap.mpr (le_of_eq ((Ideal.liesOver_iff _ _).mp hP'.2)))

p2m_export "LanglandsTunnell.CubicInduction.CondExpLeFinsum" "ramificationIdx_ne_zero"

theorem addCharLevel_psiLocal_nonneg (w : HeightOneSpectrum (𝓞 K)) :
    (0 : ℤ) ≤ LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) := by
  rw [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_eq_count_differentIdeal]
  exact FractionalIdeal.count_coe_nonneg K w _

end Fibre

end LanglandsTunnell.CubicInduction.CondExpLeFinsum

end

open LanglandsTunnell.CubicInduction.CondExpLeFinsum in

theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hμ : IsAdmissibleTwist K μ)
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hω : IsAdmissibleTwist ℚ ω)
    (_hωμ : ∀ p : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ p →
      IsUnramifiedCharAt ω p ∧ eulerCoeff ℚ ω p = inducedE3 ℚ (inducedCoeff K μ) p)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ t : ℕ, LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (localChar ω v) t ∧
      (t : ℤ) ≤ ∑ᶠ w ∈ primeFibre ℚ K v,
        (v.asIdeal.inertiaDeg' w.asIdeal : ℤ) * LanglandsTunnell.Converse.pinnedExp K μ w := by
  rename_i inst _
  haveI := algebra_subsingleton (A := 𝓞 K)
  obtain rfl : inst = NumberField.inst_ringOfIntegersAlgebra ℚ K := Subsingleton.elim _ _
  classical

  obtain ⟨Sμ, hSμ⟩ := NumberField.TateGlobal.exists_finset_forall_isUnramifiedCharAt_of_continuous K μ _hμ.2.1
  have hfinram := LanglandsTunnell.CubicInduction.finite_setOf_isRamifiedIn K
  let T₀ : Finset (HeightOneSpectrum (𝓞 ℚ)) :=
    hfinram.toFinset ∪ Sμ.image (fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.under (𝓞 ℚ))
  have hT₀ : ∀ p, IsBadPlace K μ p → p ∈ T₀ := by
    intro p hp
    rcases hp with hp | hp
    · exact Finset.mem_union_left _ (hfinram.mem_toFinset.mpr hp)
    · obtain ⟨𝔓, h𝔓, hnot⟩ := hp
      refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨𝔓, ?_, (mem_primeFibre ℚ p 𝔓).mp h𝔓⟩)
      by_contra h𝔓S
      exact hnot (hSμ 𝔓 h𝔓S)

  obtain ⟨ν, hνcl, hνc, hνloc⟩ :=
    NumberField.TateGlobal.exists_isIdeleClassChar_continuous_localChar_eq_finprod_localChar_extension_algebraMap
      ℚ K μ _hμ.1 _hμ.2.1
  have hνu : IsUnitaryChar (𝓞 ℚ) ℚ ν := by
    refine isUnitaryChar_of_forall_norm_localChar_eq_one ℚ ν hνcl hνc fun p x => ?_
    rw [hνloc p x]
    refine finprod_induction (fun z : ℂ => ‖z‖ = 1) norm_one
      (fun a b (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) => show ‖a * b‖ = 1 by rw [norm_mul, ha, hb, mul_one]) fun w => ?_
    show ‖_‖ = 1
    rw [localChar_apply]
    exact _hμ.2.2 _

  set χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ := ω * ν⁻¹ with hχdef
  have hχapp : ∀ z, χ z = ω z * (ν z)⁻¹ := fun z => by
    simp [hχdef, MonoidHom.mul_apply, MonoidHom.inv_apply]
  have hχloc : ∀ (p : HeightOneSpectrum (𝓞 ℚ)) (x : (p.adicCompletion ℚ)ˣ),
      localChar χ p x = localChar ω p x * (localChar ν p x)⁻¹ := by
    intro p x
    simp only [localChar_apply, hχapp]
  have hχcl : IsIdeleClassChar (𝓞 ℚ) ℚ χ := by
    intro u
    rw [hχapp, hνcl u, _hω.1 u]
    simp
  have hχfun : (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℂˣ) = fun z => ω z * (ν z)⁻¹ := funext hχapp
  have hχc : Continuous χ := by
    rw [hχfun]
    exact _hω.2.1.mul hνc.inv
  have hχu : IsUnitaryChar (𝓞 ℚ) ℚ χ := by
    intro z
    rw [hχapp, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv, _hω.2.2 z, hνu z, inv_one, mul_one]
  have hχadm : IsAdmissibleTwist ℚ χ := ⟨hχcl, hχc, hχu⟩
  have hgood : ∀ p : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ p →
      IsUnramifiedCharAt χ p ∧
        eulerCoeff ℚ χ p = inducedE3 ℚ (inducedCoeff K (1 : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)) p := by
    intro p hp
    have hpK : ¬ IsRamifiedIn K p := fun h => hp (Or.inl h)
    have hpμ : ∀ 𝔓 ∈ primeFibre ℚ K p, IsUnramifiedCharAt μ 𝔓 := by
      intro 𝔓 h𝔓
      by_contra hn
      exact hp (Or.inr ⟨𝔓, h𝔓, hn⟩)
    have he : ∀ w : p.Extension (𝓞 K), Ideal.ramificationIdx' p.asIdeal w.1.asIdeal = 1 := by
      intro w
      by_contra hne
      exact hpK ⟨w.1, (mem_primeFibre ℚ p w.1).mpr w.2, hne⟩
    have hμw : ∀ w : p.Extension (𝓞 K), IsUnramifiedCharAt μ w.1 :=
      fun w => hpμ w.1 ((mem_primeFibre ℚ p w.1).mpr w.2)

    obtain ⟨hωunr, hωe⟩ := _hωμ p hp

    have he3 :=
      LanglandsTunnell.RankinSelberg.inducedE3_eq_neg_one_pow_mul_finprod_of_not_isRamifiedIn_of_finrank_eq_three
        K _hdeg (inducedCoeff K μ) p hpK
    have he3one :=
      LanglandsTunnell.RankinSelberg.inducedE3_eq_neg_one_pow_mul_finprod_of_not_isRamifiedIn_of_finrank_eq_three
        K _hdeg (inducedCoeff K (1 : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)) p hpK

    have htr := fun (x : (p.adicCompletion ℚ)ˣ) (n : ℤ) (hx : Valued.v (x : p.adicCompletion ℚ) = WithZero.exp n) =>
      NumberField.TateGlobal.finprod_localChar_extension_algebraMap_eq_finprod_apply_uniformizerIdele_zpow_of_ramificationIdx_eq_one_of_isUnramifiedCharAt
        ℚ K μ p he hμw x n hx

    set P : ℂ := ∏ᶠ w : p.Extension (𝓞 K), ((μ (uniformizerIdele K w.1) : ℂˣ) : ℂ) with hPdef
    have hPfibre : (∏ᶠ w ∈ primeFibre ℚ K p, inducedCoeff K μ w) = P := by
      have h1 : (∏ᶠ w ∈ primeFibre ℚ K p, inducedCoeff K μ w) =
          ∏ᶠ w ∈ primeFibre ℚ K p, ((μ (uniformizerIdele K w) : ℂˣ) : ℂ) := by
        refine finprod_mem_congr rfl fun w hw => ?_
        simp only [inducedCoeff, if_pos (hpμ w hw)]
      rw [h1, hPdef]
      change _ = ∏ᶠ w : ↥(primeFibre ℚ K p), ((μ (uniformizerIdele K w.1) : ℂˣ) : ℂ)
      exact (finprod_set_coe_eq_finprod_mem (primeFibre ℚ K p)).symm

    have hone : (∏ᶠ w ∈ primeFibre ℚ K p, inducedCoeff K (1 : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) w) = 1 := by
      refine finprod_mem_of_eqOn_one fun w _ => ?_
      have hunr1 : IsUnramifiedCharAt (1 : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) w := by
        intro t _ _
        rw [localChar_apply, MonoidHom.one_apply]
      show inducedCoeff K (1 : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) w = 1
      simp only [inducedCoeff, if_pos hunr1, MonoidHom.one_apply, Units.val_one]

    have hν1 : ∀ u : (p.adicCompletion ℚ)ˣ, Valued.v (u : p.adicCompletion ℚ) = 1 → localChar ν p u = 1 := by
      intro u hu
      apply Units.val_injective
      rw [hνloc p u, htr u 0 (by rw [hu, WithZero.exp_zero]), neg_zero, zpow_zero, Units.val_one]
    have hνϖ : ((localChar ν p (uniformizerUnit ℚ p) : ℂˣ) : ℂ) = P := by
      rw [hνloc p, htr (uniformizerUnit ℚ p) (-1) (valued_uniformizerUnit ℚ p), neg_neg, zpow_one]
    have hP0 : P ≠ 0 := by
      rw [← hνϖ]
      exact Units.ne_zero _
    have hωϖ : ((localChar ω p (uniformizerUnit ℚ p) : ℂˣ) : ℂ) =
        (-1) ^ (Nat.card (primeFibre ℚ K p) + 1) * P := by
      rw [localChar_apply]
      change ((ω (uniformizerIdele ℚ p) : ℂˣ) : ℂ) = _
      have hec : eulerCoeff ℚ ω p = ((ω (uniformizerIdele ℚ p) : ℂˣ) : ℂ) := by
        simp only [eulerCoeff, if_pos hωunr]
      rw [← hec, hωe, he3, hPfibre]

    have hχunr : IsUnramifiedCharAt χ p := by
      intro t h₁ h₂
      have ht : Valued.v (t : p.adicCompletion ℚ) = 1 := valued_eq_one_of_mem_integers_of_inv_mem ℚ p t h₁ h₂
      rw [hχloc, hωunr t h₁ h₂, hν1 t ht, inv_one, mul_one]
    refine ⟨hχunr, ?_⟩

    have hec : eulerCoeff ℚ χ p = ((localChar χ p (uniformizerUnit ℚ p) : ℂˣ) : ℂ) := by
      simp only [eulerCoeff, if_pos hχunr]
      rfl
    rw [hec, hχloc, Units.val_mul, Units.val_inv_eq_inv_val, hωϖ, hνϖ, mul_inv_cancel_right₀ hP0, he3one, hone,
      mul_one]

  have hfin := finite_primeFibre K v
  set A : ℕ := inducedLevelAt K μ v with hAdef
  have hAsum : A = ∑ w ∈ hfin.toFinset,
      v.asIdeal.inertiaDeg' w.asIdeal * conductorExponentAt K w (localChar μ w) := by
    rw [hAdef]
    unfold inducedLevelAt
    exact finsum_mem_eq_finite_toFinset_sum _ hfin
  have hterm : ∀ w ∈ primeFibre ℚ K v, conductorExponentAt K w (localChar μ w) ≤
      Ideal.ramificationIdx' v.asIdeal w.asIdeal * A := by
    intro w hw
    have h1 : conductorExponentAt K w (localChar μ w) ≤
        v.asIdeal.inertiaDeg' w.asIdeal * conductorExponentAt K w (localChar μ w) :=
      Nat.le_mul_of_pos_left _ (one_le_inertiaDeg K v w hw)
    have h2 : v.asIdeal.inertiaDeg' w.asIdeal * conductorExponentAt K w (localChar μ w) ≤ A := by
      rw [hAsum]
      exact Finset.single_le_sum (f := fun w => v.asIdeal.inertiaDeg' w.asIdeal * conductorExponentAt K w (localChar μ w))
        (fun _ _ => Nat.zero_le _) (hfin.mem_toFinset.mpr hw)
    have h3 : A ≤ Ideal.ramificationIdx' v.asIdeal w.asIdeal * A :=
      Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (ramificationIdx_ne_zero K v w hw))
    exact h1.trans (h2.trans h3)
  have hνA : ∀ u ∈ higherUnitsAt ℚ v A, localChar ν v u = 1 := by
    intro u hu
    apply Units.val_injective
    rw [hνloc v u, Units.val_one]
    refine finprod_eq_one_of_forall_eq_one fun w => ?_
    obtain ⟨c, hc⟩ := LanglandsTunnell.TateLocal.exists_hasConductorExponentAt_of_continuous K w.1 (localChar μ w.1)
      (NumberField.TateGlobal.continuous_localChar μ _hμ.2.1 w.1)
    have hcle : c ≤ Ideal.ramificationIdx' v.asIdeal w.1.asIdeal * A := by
      have := hterm w.1 ((mem_primeFibre ℚ v w.1).mpr w.2)
      rwa [conductorExponentAt_eq_of_hasConductorExponentAt K w.1 hc] at this
    have hmem := units_map_mem_higherUnitsAt ℚ K v w A u hu
    have h1 : localChar μ w.1
        (Units.map (algebraMap (v.adicCompletion ℚ) (w.1.adicCompletion K)).toMonoidHom u) = 1 :=
      hc.1 _ (higherUnitsAt_antitone K w.1 hcle hmem)
    rw [h1, Units.val_one]

  set N : ℤ := ∑ᶠ w ∈ primeFibre ℚ K v,
      (v.asIdeal.inertiaDeg' w.asIdeal : ℤ) *
        LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) with hNdef
  have hN0 : 0 ≤ N := by
    rw [hNdef, finsum_mem_eq_finite_toFinset_sum _ hfin]
    exact Finset.sum_nonneg fun w _ =>
      mul_nonneg (by exact_mod_cast Nat.zero_le _) (addCharLevel_psiLocal_nonneg K w)
  have hsplit : (∑ᶠ w ∈ primeFibre ℚ K v,
      (v.asIdeal.inertiaDeg' w.asIdeal : ℤ) * LanglandsTunnell.Converse.pinnedExp K μ w) = (A : ℤ) + N := by
    rw [hNdef, hAsum, finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
    push_cast
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    unfold LanglandsTunnell.Converse.pinnedExp
    ring
  have hA0 : (0 : ℤ) ≤ (A : ℤ) := by exact_mod_cast Nat.zero_le _

  by_cases hram : IsRamifiedIn K v
  ·
    obtain ⟨tχ, htχ, htχle⟩ :=
      LanglandsTunnell.CubicInduction.exists_hasConductorExponentAt_le_finsum_addCharLevel_of_eulerCoeff_eq_inducedE3_one_cofinite_of_isRamifiedIn
        K _hdeg χ hχadm T₀ (fun p hpT _ => hgood p (fun hb => hpT (hT₀ p hb))) v hram
    have htriv : ∀ u ∈ higherUnitsAt ℚ v (max tχ A), localChar ω v u = 1 := by
      intro u hu
      have h3 := htχ.1 u (higherUnitsAt_antitone ℚ v (le_max_left tχ A) hu)
      have hk' := hνA u (higherUnitsAt_antitone ℚ v (le_max_right tχ A) hu)
      have := hχloc v u
      rw [h3, hk', inv_one, mul_one] at this
      exact this.symm
    obtain ⟨t, ht⟩ := LanglandsTunnell.TateLocal.exists_hasConductorExponentAt_of_continuous ℚ v (localChar ω v)
      (NumberField.TateGlobal.continuous_localChar ω _hω.2.1 v)
    refine ⟨t, ht, ?_⟩
    have htle : t ≤ max tχ A := by
      by_contra hlt
      rw [not_le] at hlt
      obtain ⟨u, hu, hne⟩ := ht.2 (max tχ A) hlt
      exact hne (htriv u hu)
    have htle' : t ≤ tχ + A := htle.trans (max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _))
    have htle'' : (t : ℤ) ≤ (tχ : ℤ) + (A : ℤ) := by exact_mod_cast htle'
    rw [← hNdef] at htχle
    rw [hsplit]
    linarith
  ·
    obtain ⟨a, hale, ha⟩ :=
      LanglandsTunnell.CubicInduction.exists_hasConductorExponentAt_le_inducedLevelAt_of_eulerCoeff_eq_inducedE3
        K _hdeg μ _hμ ω _hω _hωμ v hram
    refine ⟨a, ha, ?_⟩
    have hale' : (a : ℤ) ≤ (A : ℤ) := by rw [hAdef]; exact_mod_cast hale
    rw [hsplit]
    linarith

end S_LanglandsTunnell_CubicInduction_exists_hasConductorExponentAt_le_finsum_pinnedExp_of_eulerCoeff_eq_inducedE3
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_hasConductorExponentAt_le_finsum_pinnedExp_of_eulerCoeff_eq_inducedE3 (solution)
