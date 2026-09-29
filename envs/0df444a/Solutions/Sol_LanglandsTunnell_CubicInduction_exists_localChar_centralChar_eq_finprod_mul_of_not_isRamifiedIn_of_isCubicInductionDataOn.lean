-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_localChar_centralChar_eq_finprod_mul_of_not_isRamifiedIn_of_isCubicInductionDataOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/bd35b8f7-6e07-5bde-8d1a-5cdad340ad18

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Theorems.Thm_NumberField_TateGlobal_exists_finset_forall_isUnramifiedCharAt_of_continuous
import Theorems.Thm_LanglandsTunnell_CubicInduction_localChar_centralChar_eq_one_and_apply_uniformizerUnit_eq_inducedE3_of_not_isBadPlace_of_isCubicInductionDataOn
import Theorems.Thm_NumberField_TateGlobal_finprod_localChar_extension_algebraMap_eq_finprod_apply_uniformizerIdele_zpow_of_ramificationIdx_eq_one_of_isUnramifiedCharAt
import Theorems.Thm_LanglandsTunnell_RankinSelberg_inducedE3_eq_neg_one_pow_mul_finprod_of_not_isRamifiedIn_of_finrank_eq_three
import Theorems.Thm_NumberField_TateGlobal_exists_isIdeleClassChar_continuous_localChar_eq_finprod_localChar_extension_algebraMap
import Theorems.Thm_NumberField_exists_isAdmissibleTwist_mul_self_eq_one_and_isUnramifiedCharAt_and_apply_uniformizerIdele_eq_neg_one_pow_of_not_isRamifiedIn
import Theorems.Thm_NumberField_TateGlobal_eq_one_of_isIdeleClassChar_of_continuous_of_forall_localChar_eq_one
import Theorems.Thm_LanglandsTunnell_CubicInduction_finite_setOf_isRamifiedIn
import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_localChar_centralChar_eq_finprod_mul_of_not_isRamifiedIn_of_isCubicInductionDataOn
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply LanglandsTunnell.CubicLambda.ResolventDatum.s3.injEq LanglandsTunnell.CubicLambda.ResolventDatum.s3.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of"
p2m_attr_erase "simp" "IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply"
p2m_attr_erase "simp" "Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add"

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal NumberField.AdelicLevel AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal MeasureTheory LanglandsTunnell.RankinSelberg

noncomputable section

namespace P2mCubicCentralChar

section LocalTriv

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem valued_coe_units_ne_zero (x : (v.adicCompletion F)ˣ) : Valued.v (x : v.adicCompletion F) ≠ 0 :=
  Valuation.ne_zero_of_unit Valued.v x

theorem exists_valued_eq_exp (x : (v.adicCompletion F)ˣ) :
    ∃ n : ℤ, Valued.v (x : v.adicCompletion F) = WithZero.exp n :=
  ⟨(Valued.v (x : v.adicCompletion F)).log, (WithZero.exp_log (valued_coe_units_ne_zero F v x)).symm⟩

theorem valued_uniformizerUnit_zpow (n : ℤ) :
    Valued.v (((uniformizerUnit F v) ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) = WithZero.exp (-n) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, valued_uniformizerUnit, ← WithZero.exp_zsmul]
  congr 1
  simp

theorem monoidHom_eq_one_of_forall_valued_eq_one_of_apply_uniformizerUnit
    (η : (v.adicCompletion F)ˣ →* ℂˣ)
    (h1 : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → η u = 1)
    (h2 : η (uniformizerUnit F v) = 1) : η = 1 := by
  ext x
  obtain ⟨n, hn⟩ := exists_valued_eq_exp F v x
  have hu : Valued.v ((x * (uniformizerUnit F v) ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    rw [Units.val_mul, map_mul, hn, valued_uniformizerUnit_zpow, ← WithZero.exp_add]
    simp
  have := h1 _ hu
  rw [map_mul, map_zpow, h2, one_zpow, mul_one] at this
  simpa using congrArg Units.val this

theorem mem_integers_and_inv_mem_of_valued_eq_one (u : (v.adicCompletion F)ˣ)
    (hu : Valued.v (u : v.adicCompletion F) = 1) :
    (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F ∧
      ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
  refine ⟨?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hu]
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]

theorem hasConductorExponentAt_zero_of_isUnramifiedCharAt (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (h : IsUnramifiedCharAt χ v) : HasConductorExponentAt F v (localChar χ v) 0 := by
  rw [hasConductorExponentAt_zero_iff]
  intro u hu
  obtain ⟨h₁, h₂⟩ := mem_integers_and_inv_mem_of_valued_eq_one F v u hu
  exact h u h₁ h₂

end LocalTriv

section CentralCont

theorem continuous_centralScalarGL :
    Continuous (centralScalarGL 3 (𝓞 ℚ) ℚ : (AdeleRing (𝓞 ℚ) ℚ)ˣ → AdelicGL 3 (𝓞 ℚ) ℚ) := by
  refine Continuous.units_map _ ?_
  show Continuous fun x : AdeleRing (𝓞 ℚ) ℚ => Matrix.scalar (Fin 3) x
  have : (fun x : AdeleRing (𝓞 ℚ) ℚ => Matrix.scalar (Fin 3) x) =
      fun x => Matrix.diagonal fun _ : Fin 3 => x := by
    funext x
    exact Matrix.scalar_apply x
  rw [this]
  exact (continuous_pi fun _ => continuous_id).matrix_diagonal

theorem continuous_centralChar (K : Type) [Field K] [NumberField K]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (pins : CarrierPins ℚ) (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K pins ψ μ {v | IsBadPlace K μ v} X) (hcont : Continuous X.form) (hF : X.form ≠ 0) :
    Continuous X.centralChar := by
  obtain ⟨g₁, hg₁⟩ : ∃ g, X.form g ≠ 0 := by
    by_contra h
    push Not at h
    exact hF (funext fun g => by simpa using h g)

  have hval : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      ((X.centralChar z : ℂˣ) : ℂ) = X.form (centralScalarGL 3 (𝓞 ℚ) ℚ z * g₁) * (X.form g₁)⁻¹ := by
    intro z
    rw [hX.central z g₁, mul_assoc, mul_inv_cancel₀ hg₁, mul_one]
  have hc1 : Continuous fun z : (AdeleRing (𝓞 ℚ) ℚ)ˣ => ((X.centralChar z : ℂˣ) : ℂ) := by
    simp_rw [hval]
    exact (hcont.comp (continuous_centralScalarGL.mul continuous_const)).mul continuous_const
  rw [Units.continuous_iff]
  refine ⟨hc1, ?_⟩
  have : (fun z : (AdeleRing (𝓞 ℚ) ℚ)ˣ => ((X.centralChar z)⁻¹ : ℂˣ).val) =
      fun z => ((X.centralChar z⁻¹ : ℂˣ) : ℂ) := by
    funext z
    rw [map_inv]
  rw [this]
  exact hc1.comp continuous_inv

end CentralCont

end P2mCubicCentralChar

end

open P2mCubicCentralChar in
theorem solution
    (K : Type) [Field K] [NumberField K] (hdeg : Module.finrank ℚ K = 3)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (pins : CarrierPins ℚ)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K pins ψ μ {v | IsBadPlace K μ v} X) (hcont : Continuous X.form) (hF : X.form ≠ 0)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hKv : ¬ IsRamifiedIn K v) :
    ∃ η : (v.adicCompletion ℚ)ˣ →* ℂˣ, HasConductorExponentAt ℚ v η 0 ∧ (∀ x, η x * η x = 1) ∧
      ∀ x : (v.adicCompletion ℚ)ˣ,
        ((localChar X.centralChar v x : ℂˣ) : ℂ) =
          (∏ᶠ w : v.Extension (𝓞 K), ((localChar μ w.1
            (Units.map (algebraMap (v.adicCompletion ℚ) (w.1.adicCompletion K)).toMonoidHom x) : ℂˣ) : ℂ)) *
            ((η x : ℂˣ) : ℂ) := by
  classical

  obtain ⟨Sμ, hSμ⟩ := NumberField.TateGlobal.exists_finset_forall_isUnramifiedCharAt_of_continuous K μ hμ.2.1
  have hfin := LanglandsTunnell.CubicInduction.finite_setOf_isRamifiedIn K
  let T₀ : Finset (HeightOneSpectrum (𝓞 ℚ)) :=
    hfin.toFinset ∪ Sμ.image (fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.under (𝓞 ℚ))
  have hT₀ : ∀ p, IsBadPlace K μ p → p ∈ T₀ := by
    intro p hp
    rcases hp with hp | hp
    · exact Finset.mem_union_left _ (hfin.mem_toFinset.mpr hp)
    · obtain ⟨𝔓, h𝔓, hnot⟩ := hp
      refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨𝔓, ?_, (mem_primeFibre ℚ p 𝔓).mp h𝔓⟩)
      by_contra h𝔓S
      exact hnot (hSμ 𝔓 h𝔓S)

  obtain ⟨ν, hνcl, hνc, hνloc⟩ :=
    NumberField.TateGlobal.exists_isIdeleClassChar_continuous_localChar_eq_finprod_localChar_extension_algebraMap
      ℚ K μ hμ.1 hμ.2.1
  obtain ⟨ω, hωadm, hω2, hωloc⟩ :=
    NumberField.exists_isAdmissibleTwist_mul_self_eq_one_and_isUnramifiedCharAt_and_apply_uniformizerIdele_eq_neg_one_pow_of_not_isRamifiedIn
      K

  set θ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ := X.centralChar * ν⁻¹ * ω⁻¹ with hθdef
  have hθapp : ∀ z, θ z = X.centralChar z * (ν z)⁻¹ * (ω z)⁻¹ := fun z => by
    simp [hθdef, MonoidHom.mul_apply, MonoidHom.inv_apply]
  have hθloc : ∀ (p : HeightOneSpectrum (𝓞 ℚ)) (x : (p.adicCompletion ℚ)ˣ),
      localChar θ p x = localChar X.centralChar p x * (localChar ν p x)⁻¹ * (localChar ω p x)⁻¹ := by
    intro p x
    simp only [localChar_apply, hθapp]
  have hgood : ∀ p : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ p → localChar θ p = 1 := by
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

    obtain ⟨hF1, hFϖ⟩ :=
      LanglandsTunnell.CubicInduction.localChar_centralChar_eq_one_and_apply_uniformizerUnit_eq_inducedE3_of_not_isBadPlace_of_isCubicInductionDataOn
        K ψ μ pins X hX hF T₀ hT₀ p hp

    have he3 :=
      LanglandsTunnell.RankinSelberg.inducedE3_eq_neg_one_pow_mul_finprod_of_not_isRamifiedIn_of_finrank_eq_three
        K hdeg (inducedCoeff K μ) p hpK

    have htr := fun (x : (p.adicCompletion ℚ)ˣ) (n : ℤ) (hx : Valued.v (x : p.adicCompletion ℚ) = WithZero.exp n) =>
      NumberField.TateGlobal.finprod_localChar_extension_algebraMap_eq_finprod_apply_uniformizerIdele_zpow_of_ramificationIdx_eq_one_of_isUnramifiedCharAt
        ℚ K μ p he hμw x n hx

    obtain ⟨hωunr, hωϖ⟩ := hωloc p hpK

    set P : ℂ := ∏ᶠ w : p.Extension (𝓞 K), ((μ (uniformizerIdele K w.1) : ℂˣ) : ℂ) with hPdef
    have hPfibre : (∏ᶠ w ∈ primeFibre ℚ K p, inducedCoeff K μ w) = P := by
      have h1 : (∏ᶠ w ∈ primeFibre ℚ K p, inducedCoeff K μ w) =
          ∏ᶠ w ∈ primeFibre ℚ K p, ((μ (uniformizerIdele K w) : ℂˣ) : ℂ) := by
        refine finprod_mem_congr rfl fun w hw => ?_
        simp only [inducedCoeff, if_pos (hpμ w hw)]
      rw [h1, hPdef]
      change _ = ∏ᶠ w : ↥(primeFibre ℚ K p), ((μ (uniformizerIdele K w.1) : ℂˣ) : ℂ)
      exact (finprod_set_coe_eq_finprod_mem (primeFibre ℚ K p)).symm
    have hcard : Nat.card (primeFibre ℚ K p) = Nat.card (p.Extension (𝓞 K)) := rfl

    have hunits : ∀ u : (p.adicCompletion ℚ)ˣ, Valued.v (u : p.adicCompletion ℚ) = 1 → localChar θ p u = 1 := by
      intro u hu
      have hν1 : localChar ν p u = 1 := by
        apply Units.val_injective
        rw [hνloc p u, htr u 0 (by rw [hu, WithZero.exp_zero]), neg_zero, zpow_zero, Units.val_one]
      have hω1 : localChar ω p u = 1 := by
        obtain ⟨h₁, h₂⟩ := mem_integers_and_inv_mem_of_valued_eq_one ℚ p u hu
        exact hωunr u h₁ h₂
      rw [hθloc, hF1 u hu, hν1, hω1]
      simp

    have hunif : localChar θ p (uniformizerUnit ℚ p) = 1 := by
      apply Units.val_injective
      have hνϖ : ((localChar ν p (uniformizerUnit ℚ p) : ℂˣ) : ℂ) = P := by
        rw [hνloc p, htr (uniformizerUnit ℚ p) (-1) (valued_uniformizerUnit ℚ p), neg_neg, zpow_one]
      have hP0 : P ≠ 0 := by
        rw [← hνϖ]
        exact Units.ne_zero _
      have hFϖ' : ((localChar X.centralChar p (uniformizerUnit ℚ p) : ℂˣ) : ℂ) =
          (-1) ^ (Nat.card (p.Extension (𝓞 K)) + 1) * P := by
        rw [hFϖ, he3, hPfibre, hcard]
      have hωϖ' : ((localChar ω p (uniformizerUnit ℚ p) : ℂˣ) : ℂ) =
          (-1) ^ (Nat.card (p.Extension (𝓞 K)) + 1) := by
        rw [localChar_apply]
        change ((ω (uniformizerIdele ℚ p) : ℂˣ) : ℂ) = _
        rw [hωϖ, hdeg, hcard, show 3 + Nat.card (p.Extension (𝓞 K)) = (Nat.card (p.Extension (𝓞 K)) + 1) + 2 by
          ring, pow_add, neg_one_sq, mul_one]
      rw [hθloc, Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, hFϖ', hνϖ,
        hωϖ', Units.val_one]
      have hs : ((-1 : ℂ) ^ (Nat.card (p.Extension (𝓞 K)) + 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp
    exact monoidHom_eq_one_of_forall_valued_eq_one_of_apply_uniformizerUnit ℚ p _ hunits hunif

  have hθcl : IsIdeleClassChar (𝓞 ℚ) ℚ θ := by
    intro u
    rw [hθapp, hX.centralChar_ideleClass u, hνcl u, hωadm.1 u]
    simp
  have hθc : Continuous θ := by
    have hFc := continuous_centralChar K ψ μ pins X hX hcont hF
    have : (θ : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℂˣ) = fun z => X.centralChar z * (ν z)⁻¹ * (ω z)⁻¹ := funext hθapp
    rw [this]
    exact (hFc.mul hνc.inv).mul hωadm.2.1.inv
  have hθ1 : θ = 1 :=
    NumberField.TateGlobal.eq_one_of_isIdeleClassChar_of_continuous_of_forall_localChar_eq_one ℚ θ hθcl hθc T₀
      (fun p hp => hgood p (fun hb => hp (hT₀ p hb)))

  have hsplit : ∀ x : (v.adicCompletion ℚ)ˣ,
      localChar X.centralChar v x = localChar ν v x * localChar ω v x := by
    intro x
    have h := hθloc v x
    rw [hθ1] at h
    simp only [localChar_apply, MonoidHom.one_apply] at h
    simp only [localChar_apply]

    have := h.symm
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
    rw [this, mul_comm]
  obtain ⟨hωunrv, -⟩ := hωloc v hKv
  refine ⟨localChar ω v, hasConductorExponentAt_zero_of_isUnramifiedCharAt ℚ v ω hωunrv, ?_, ?_⟩
  · intro x
    simp only [localChar_apply]
    exact hω2 _
  · intro x
    rw [hsplit x, Units.val_mul, hνloc v x]

end S_LanglandsTunnell_CubicInduction_exists_localChar_centralChar_eq_finprod_mul_of_not_isRamifiedIn_of_isCubicInductionDataOn
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_localChar_centralChar_eq_finprod_mul_of_not_isRamifiedIn_of_isCubicInductionDataOn (solution)
