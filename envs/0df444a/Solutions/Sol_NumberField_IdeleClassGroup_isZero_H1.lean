-- Prove2me | solution 1 for NumberField.IdeleClassGroup.isZero_H1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/f96c2ae5-9abd-568b-abda-468f14913bec

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Theorems.Thm_NumberField_IdeleClassGroup_isZero_H1_of_isPGroup
import Theorems.Thm_NumberField_IdeleClassGroup_nonempty_res_iso_fixedField_and_groupCohomology_iso
import Theorems.Thm_groupCohomology_exists_corestriction_comp_res_eq_index_nsmul
import Theorems.Thm_M4aHerbrand_nonempty_ideleGaloisDescent
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_exists_mulDistribMulAction_smul_eq_classAct
import Theorems.Thm_groupCohomology_nonempty_linearEquiv_of_iso_res_mulEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_IdeleClassGroup_isZero_H1
p2m_attr_erase "instance" "M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed"
p2m_attr_erase "instance" "RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul"
p2m_attr_erase "simp" "IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec"
p2m_attr_erase "simp" "LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero"

set_option autoImplicit false
open NumberField M4aHerbrand CategoryTheory CategoryTheory.Limits groupCohomology Rep

namespace Ws7IsZeroH1

private theorem eq_zero_of_isZero {M : ModuleCat ℤ} (hM : IsZero M) (x : M) : x = 0 := by
  have h : (𝟙 M : M ⟶ M) = 0 := hM.eq_of_src _ _
  have := congrArg (fun f : M ⟶ M => f.hom x) h
  simpa using this

private theorem isZero_of_forall_eq_zero {M : ModuleCat ℤ} (h : ∀ x : M, x = 0) : IsZero M :=
  @ModuleCat.isZero_of_subsingleton ℤ _ M ⟨fun a b => (h a).trans (h b).symm⟩

private theorem eq_zero_of_nsmul_of_forall_prime {A : Type} [AddCommGroup A] (a : A) (N : ℕ) (hN : N ≠ 0)
    (hNa : N • a = 0) (h : ∀ p : ℕ, p.Prime → p ∣ N → ∃ i : ℕ, ¬ p ∣ i ∧ i • a = 0) : a = 0 := by
  have hord : addOrderOf a ∣ N := addOrderOf_dvd_of_nsmul_eq_zero hNa
  have hne : addOrderOf a ≠ 0 := fun h0 => hN (Nat.eq_zero_of_zero_dvd (h0 ▸ hord))
  by_contra hne1
  have h1 : addOrderOf a ≠ 1 := fun h1 => hne1 (AddMonoid.addOrderOf_eq_one_iff.mp h1)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h1
  obtain ⟨i, hpi, hia⟩ := h p hp (hpd.trans hord)
  exact hpi (hpd.trans (addOrderOf_dvd_of_nsmul_eq_zero hia))

private theorem isZero_res_of_isZero_fixedField
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)
    (P : Subgroup (F ≃ₐ[E] F)) (n : ℕ)
    (htop : ∀ (D' : IdeleGaloisDescent (𝓞 F) (IntermediateField.fixedField P) F)
      [MulDistribMulAction (F ≃ₐ[IntermediateField.fixedField P] F) (IdeleClassGroup (𝓞 F) F)],
      (∀ (g : F ≃ₐ[IntermediateField.fixedField P] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D'.classAct g c) →
      IsZero (groupCohomology
        (Rep.ofMulDistribMulAction (F ≃ₐ[IntermediateField.fixedField P] F) (IdeleClassGroup (𝓞 F) F)) n)) :
    IsZero (groupCohomology (Rep.res P.subtype
      (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) n) := by
  classical
  haveI : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ E F
  obtain ⟨D'⟩ := M4aHerbrand.nonempty_ideleGaloisDescent (IntermediateField.fixedField P) F
  obtain ⟨inst', hact'⟩ :=
    M4aHerbrand.IdeleGaloisDescent.exists_mulDistribMulAction_smul_eq_classAct (IntermediateField.fixedField P) F D'
  letI := inst'
  let ι : P ≃* (F ≃ₐ[IntermediateField.fixedField P] F) := IntermediateField.subgroupEquivAlgEquiv P
  have hι : ∀ (s : P) (x : F), ι s x = (s : F ≃ₐ[E] F) x := fun s x => rfl
  obtain ⟨-, hiso⟩ :=
    NumberField.IdeleClassGroup.nonempty_res_iso_fixedField_and_groupCohomology_iso E F D hact P D' hact' ι hι
  obtain ⟨e⟩ := hiso n
  exact (htop D' hact').of_iso e

private theorem isZero_H1_top
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c) :
    IsZero (groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 1) := by
  classical
  haveI : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ E F
  refine isZero_of_forall_eq_zero fun y => ?_
  refine eq_zero_of_nsmul_of_forall_prime y (Nat.card (F ≃ₐ[E] F)) Nat.card_pos.ne' ?_ ?_
  ·
    obtain ⟨cor, hcor⟩ := groupCohomology.exists_corestriction_comp_res_eq_index_nsmul
      (⊥ : Subgroup (F ≃ₐ[E] F)) (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 1
    have h0 : IsZero (groupCohomology (Rep.res (⊥ : Subgroup (F ≃ₐ[E] F)).subtype
        (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 1) :=
      isZero_groupCohomology_succ_of_subsingleton _ 0
    have := hcor y
    rw [eq_zero_of_isZero h0 ((groupCohomology.map _ _ 1).hom y), map_zero, Subgroup.index_bot] at this
    exact this.symm
  · intro p hp hpd
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p (F ≃ₐ[E] F)))
    refine ⟨(P : Subgroup (F ≃ₐ[E] F)).index, Sylow.not_dvd_index P, ?_⟩
    obtain ⟨cor, hcor⟩ := groupCohomology.exists_corestriction_comp_res_eq_index_nsmul
      (P : Subgroup (F ≃ₐ[E] F)) (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 1

    have hP : IsZero (groupCohomology (Rep.res (P : Subgroup (F ≃ₐ[E] F)).subtype
        (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 1) := by
      refine isZero_res_of_isZero_fixedField E F D hact P 1 fun D' _ hact' => ?_
      have hG' : IsPGroup p (F ≃ₐ[IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))] F) :=
        P.isPGroup'.of_equiv (IntermediateField.subgroupEquivAlgEquiv (P : Subgroup (F ≃ₐ[E] F)))
      have htop := NumberField.IdeleClassGroup.isZero_H1_of_isPGroup (IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F
        p hG' D' hact' ⊤

      obtain ⟨ψ, -⟩ := groupCohomology.nonempty_linearEquiv_of_iso_res_mulEquiv
        (Subgroup.topEquiv : (⊤ : Subgroup (F ≃ₐ[IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))] F)) ≃* _)
        (Rep.res (⊤ : Subgroup _).subtype
          (Rep.ofMulDistribMulAction (F ≃ₐ[IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))] F) (IdeleClassGroup (𝓞 F) F)))
        (Rep.ofMulDistribMulAction (F ≃ₐ[IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))] F) (IdeleClassGroup (𝓞 F) F))
        (Iso.refl _) 1
      exact isZero_of_forall_eq_zero fun x => by
        have hx := eq_zero_of_isZero htop (ψ.symm x)
        simpa using congrArg ψ hx
    have := hcor y
    rw [eq_zero_of_isZero hP ((groupCohomology.map _ _ 1).hom y), map_zero] at this
    exact this.symm

end Ws7IsZeroH1

open Ws7IsZeroH1 in
theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c) :
    ∀ S : Subgroup (F ≃ₐ[E] F), Limits.IsZero
      (groupCohomology (Rep.res S.subtype
        (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 1) := by
  intro S
  exact Ws7IsZeroH1.isZero_res_of_isZero_fixedField E F D hact S 1
    fun D' _ hact' => Ws7IsZeroH1.isZero_H1_top (IntermediateField.fixedField S) F D' hact'

end S_NumberField_IdeleClassGroup_isZero_H1
end P2MW
export P2MW.S_NumberField_IdeleClassGroup_isZero_H1 (solution)
