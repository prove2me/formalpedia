-- Prove2me | solution 1 for NumberField.IdeleClassGroup.finite_H2_and_natCard_H2_le_card
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/1baf3337-0c10-556b-833e-d652806f1625

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Theorems.Thm_NumberField_IdeleClassGroup_finite_H2_and_natCard_H2_le_card_of_isPGroup
import Theorems.Thm_NumberField_IdeleClassGroup_nonempty_res_iso_fixedField_and_groupCohomology_iso
import Theorems.Thm_groupCohomology_exists_corestriction_comp_res_eq_index_nsmul
import Theorems.Thm_M4aHerbrand_nonempty_ideleGaloisDescent
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_exists_mulDistribMulAction_smul_eq_classAct
import Theorems.Thm_groupCohomology_nonempty_linearEquiv_of_iso_res_mulEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_IdeleClassGroup_finite_H2_and_natCard_H2_le_card
p2m_attr_erase "instance" "M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed"
p2m_attr_erase "instance" "RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul"
p2m_attr_erase "simp" "IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec"
p2m_attr_erase "simp" "LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero"

set_option autoImplicit false
open NumberField M4aHerbrand CategoryTheory CategoryTheory.Limits groupCohomology Rep

namespace Ws7H2Le

private theorem eq_zero_of_isZero {M : ModuleCat ℤ} (hM : IsZero M) (x : M) : x = 0 := by
  have h : (𝟙 M : M ⟶ M) = 0 := hM.eq_of_src _ _
  have := congrArg (fun f : M ⟶ M => f.hom x) h
  simpa using this

private theorem eq_zero_of_nsmul_of_forall_prime {A : Type} [AddCommGroup A] (a : A) (N : ℕ) (_hN : N ≠ 0)
    (hNa : N • a = 0) (h : ∀ p : ℕ, p.Prime → p ∣ N → ∃ i : ℕ, ¬ p ∣ i ∧ i • a = 0) : a = 0 := by
  have hord : addOrderOf a ∣ N := addOrderOf_dvd_of_nsmul_eq_zero hNa
  by_contra hne1
  have h1 : addOrderOf a ≠ 1 := fun h1 => hne1 (AddMonoid.addOrderOf_eq_one_iff.mp h1)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h1
  obtain ⟨i, hpi, hia⟩ := h p hp (hpd.trans hord)
  exact hpi (hpd.trans (addOrderOf_dvd_of_nsmul_eq_zero hia))

private theorem finite_and_natCard_le_res_of_fixedField
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)
    (P : Subgroup (F ≃ₐ[E] F)) (n b : ℕ)
    (htop : ∀ (D' : IdeleGaloisDescent (𝓞 F) (IntermediateField.fixedField P) F)
      [MulDistribMulAction (F ≃ₐ[IntermediateField.fixedField P] F) (IdeleClassGroup (𝓞 F) F)],
      (∀ (g : F ≃ₐ[IntermediateField.fixedField P] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D'.classAct g c) →
      Finite (groupCohomology
        (Rep.ofMulDistribMulAction (F ≃ₐ[IntermediateField.fixedField P] F) (IdeleClassGroup (𝓞 F) F)) n) ∧
      Nat.card (groupCohomology
        (Rep.ofMulDistribMulAction (F ≃ₐ[IntermediateField.fixedField P] F) (IdeleClassGroup (𝓞 F) F)) n) ≤ b) :
    Finite (groupCohomology (Rep.res P.subtype
      (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) n) ∧
    Nat.card (groupCohomology (Rep.res P.subtype
      (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) n) ≤ b := by
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
  obtain ⟨hfin, hle⟩ := htop D' hact'
  haveI := hfin
  exact ⟨Finite.of_equiv _ e.toLinearEquiv.toEquiv.symm, (Nat.card_congr e.toLinearEquiv.toEquiv).trans_le hle⟩

private theorem finite_and_natCard_le_of_isPGroup
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)
    (p : ℕ) [Fact p.Prime] (P : Subgroup (F ≃ₐ[E] F)) (hP : IsPGroup p P) :
    Finite (groupCohomology (Rep.res P.subtype
      (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) ∧
    Nat.card (groupCohomology (Rep.res P.subtype
      (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) ≤ Nat.card P := by
  classical
  haveI : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ E F
  refine finite_and_natCard_le_res_of_fixedField E F D hact P 2 (Nat.card P) fun D' _ hact' => ?_
  have hG' : IsPGroup p (F ≃ₐ[IntermediateField.fixedField P] F) :=
    hP.of_equiv (IntermediateField.subgroupEquivAlgEquiv P)
  haveI : Fintype (⊤ : Subgroup (F ≃ₐ[IntermediateField.fixedField P] F)) := Fintype.ofFinite _
  obtain ⟨hfin, hle⟩ := NumberField.IdeleClassGroup.finite_H2_and_natCard_H2_le_card_of_isPGroup
    (IntermediateField.fixedField P) F p hG' D' hact' ⊤
  haveI := hfin
  obtain ⟨ψ, -⟩ := groupCohomology.nonempty_linearEquiv_of_iso_res_mulEquiv
    (Subgroup.topEquiv : (⊤ : Subgroup (F ≃ₐ[IntermediateField.fixedField P] F)) ≃* _)
    (Rep.res (⊤ : Subgroup _).subtype
      (Rep.ofMulDistribMulAction (F ≃ₐ[IntermediateField.fixedField P] F) (IdeleClassGroup (𝓞 F) F)))
    (Rep.ofMulDistribMulAction (F ≃ₐ[IntermediateField.fixedField P] F) (IdeleClassGroup (𝓞 F) F))
    (Iso.refl _) 2
  refine ⟨Finite.of_equiv _ ψ.toEquiv, ?_⟩
  calc Nat.card _ = Nat.card (groupCohomology (Rep.res (⊤ : Subgroup _).subtype
          (Rep.ofMulDistribMulAction (F ≃ₐ[IntermediateField.fixedField P] F) (IdeleClassGroup (𝓞 F) F))) 2) :=
        Nat.card_congr ψ.toEquiv.symm
    _ ≤ Fintype.card (⊤ : Subgroup (F ≃ₐ[IntermediateField.fixedField P] F)) := hle
    _ = Nat.card (F ≃ₐ[IntermediateField.fixedField P] F) := by
        rw [← Nat.card_eq_fintype_card, Subgroup.card_top]
    _ = Nat.card P := (Nat.card_congr (IntermediateField.subgroupEquivAlgEquiv P).toEquiv).symm

private theorem finite_and_natCard_le_top
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c) :
    Finite (groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2) ∧
    Nat.card (groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2)
      ≤ Nat.card (F ≃ₐ[E] F) := by
  classical
  haveI : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ E F

  set X : Rep ℤ (F ≃ₐ[E] F) := Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F) with hX
  set N : ℕ := Nat.card (F ≃ₐ[E] F) with hN
  have hN0 : N ≠ 0 := Nat.card_pos.ne'

  let T := N.primeFactors
  have hTprime : ∀ q : T, (q : ℕ).Prime := fun q => Nat.prime_of_mem_primeFactors q.2
  let Psub : T → Subgroup (F ≃ₐ[E] F) := fun q =>
    haveI : Fact (q : ℕ).Prime := ⟨hTprime q⟩
    ((Classical.arbitrary (Sylow (q : ℕ) (F ≃ₐ[E] F)) : Sylow (q : ℕ) (F ≃ₐ[E] F)) : Subgroup (F ≃ₐ[E] F))
  have hPsyl : ∀ q : T, ∃ (_ : Fact (q : ℕ).Prime) (P : Sylow (q : ℕ) (F ≃ₐ[E] F)), (P : Subgroup (F ≃ₐ[E] F)) = Psub q :=
    fun q => ⟨⟨hTprime q⟩, _, rfl⟩

  have hlayer : ∀ q : T, Finite (groupCohomology (Rep.res (Psub q).subtype X) 2) ∧
      Nat.card (groupCohomology (Rep.res (Psub q).subtype X) 2) ≤ Nat.card (Psub q) := by
    intro q
    obtain ⟨hq, P, hP⟩ := hPsyl q
    rw [← hP]
    exact finite_and_natCard_le_of_isPGroup E F D hact q P P.isPGroup'

  let r : ∀ q : T, groupCohomology X 2 →ₗ[ℤ] groupCohomology (Rep.res (Psub q).subtype X) 2 :=
    fun q => (groupCohomology.map (Psub q).subtype (𝟙 (Rep.res (Psub q).subtype X)) 2).hom
  let f : groupCohomology X 2 →+ (∀ q : T, groupCohomology (Rep.res (Psub q).subtype X) 2) :=
    AddMonoidHom.pi fun q => (r q).toAddMonoidHom

  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    refine eq_zero_of_nsmul_of_forall_prime y N hN0 ?_ ?_
    · obtain ⟨cor, hcor⟩ := groupCohomology.exists_corestriction_comp_res_eq_index_nsmul
        (⊥ : Subgroup (F ≃ₐ[E] F)) X 2
      have h0 : IsZero (groupCohomology (Rep.res (⊥ : Subgroup (F ≃ₐ[E] F)).subtype X) 2) :=
        isZero_groupCohomology_succ_of_subsingleton _ 1
      have := hcor y
      rw [eq_zero_of_isZero h0 ((groupCohomology.map _ _ 2).hom y), map_zero, Subgroup.index_bot] at this
      exact this.symm
    · intro p hp hpd
      have hpT : p ∈ T := Nat.mem_primeFactors.mpr ⟨hp, hpd, hN0⟩
      obtain ⟨hq, P, hP⟩ := hPsyl ⟨p, hpT⟩
      refine ⟨(Psub ⟨p, hpT⟩).index, ?_, ?_⟩
      · rw [← hP]; exact Sylow.not_dvd_index P
      obtain ⟨cor, hcor⟩ := groupCohomology.exists_corestriction_comp_res_eq_index_nsmul (Psub ⟨p, hpT⟩) X 2
      have hy' : r ⟨p, hpT⟩ y = 0 := by
        have := congrFun (congrArg (fun g => (g : ∀ q : T, _)) hy) ⟨p, hpT⟩
        simpa [f] using this
      have := hcor y
      change cor (r ⟨p, hpT⟩ y) = _ at this
      rw [hy', map_zero] at this
      exact this.symm

  haveI : ∀ q : T, Finite (groupCohomology (Rep.res (Psub q).subtype X) 2) := fun q => (hlayer q).1
  haveI : Finite (∀ q : T, groupCohomology (Rep.res (Psub q).subtype X) 2) := Pi.finite
  refine ⟨Finite.of_injective f hf, ?_⟩
  calc Nat.card (groupCohomology X 2)
      ≤ Nat.card (∀ q : T, groupCohomology (Rep.res (Psub q).subtype X) 2) :=
        Nat.card_le_card_of_injective f hf
    _ = ∏ q : T, Nat.card (groupCohomology (Rep.res (Psub q).subtype X) 2) := Nat.card_pi
    _ ≤ ∏ q : T, Nat.card (Psub q) := Finset.prod_le_prod' fun q _ => (hlayer q).2
    _ = ∏ q : T, (q : ℕ) ^ N.factorization q := by
        refine Finset.prod_congr rfl fun q _ => ?_
        obtain ⟨hq, P, hP⟩ := hPsyl q
        rw [← hP, Sylow.card_eq_multiplicity]
    _ = ∏ q ∈ T, q ^ N.factorization q := Finset.prod_coe_sort T (fun q => q ^ N.factorization q)
    _ = N := Nat.prod_factorization_pow_eq_self hN0

end Ws7H2Le

open Ws7H2Le in
theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c) :
    ∀ (S : Subgroup (F ≃ₐ[E] F)) [Fintype S], Finite
        (groupCohomology (Rep.res S.subtype
          (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) ∧
      Nat.card
        (groupCohomology (Rep.res S.subtype
          (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) ≤ Fintype.card S := by
  intro S _
  classical
  haveI : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ E F
  have h := Ws7H2Le.finite_and_natCard_le_res_of_fixedField E F D hact S 2
    (Nat.card (F ≃ₐ[IntermediateField.fixedField S] F))
    fun D' _ hact' => Ws7H2Le.finite_and_natCard_le_top (IntermediateField.fixedField S) F D' hact'
  refine ⟨h.1, h.2.trans_eq ?_⟩
  rw [← Nat.card_congr (IntermediateField.subgroupEquivAlgEquiv S).toEquiv, Nat.card_eq_fintype_card]

end S_NumberField_IdeleClassGroup_finite_H2_and_natCard_H2_le_card
end P2MW
export P2MW.S_NumberField_IdeleClassGroup_finite_H2_and_natCard_H2_le_card (solution)
