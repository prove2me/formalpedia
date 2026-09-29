-- Prove2me | solution 1 for M4aHerbrand.exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/f5842214-a1ff-594e-87d9-fa38b1ba9508

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Theorems.Thm_M4aHerbrand_exists_fundamentalClass_ideleClassGroup_res_eq_localFundamentalClass_of_isPGroup_of_ne_two
import Theorems.Thm_ExtCitation_LocalLevel_isLocalFundamentalClass_map_subtype
import Theorems.Thm_NumberField_PlaceDecomp_faithfulSMul_decomp
import Theorems.Thm_ExtCitation_LocalLevel_isSolvable_of_faithfulSMul_of_padic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul"
p2m_attr_erase "simp" "SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply"
p2m_attr_erase "simp" "IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq IsLocalRing.principalUnits_zero Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk"
p2m_attr_erase "simp" "LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand"
open scoped NumberField.PlaceDecomp

noncomputable section

namespace M4aHerbrand
p2m_export "M4aHerbrand" "infPart finPart IdeleClassGroup IdeleGaloisDescent exists_fundamentalClass_ideleClassGroup_res_eq_localFundamentalClass_of_isPGroup_of_ne_two"
namespace L1Frame
p2m_open "M4aHerbrand"

variable (E F : Type) [Field E] [Field F] [NumberField F] [Algebra E F]

def resHom (K : IntermediateField E F) : (F ≃ₐ[↥K] F) →* (F ≃ₐ[E] F) where
  toFun h := h.restrictScalars E
  map_one' := rfl
  map_mul' _ _ := rfl

@[scoped simp] theorem resHom_apply (K : IntermediateField E F) (h : F ≃ₐ[↥K] F) : resHom E F K h = h.restrictScalars E := rfl

theorem resHom_injective (K : IntermediateField E F) : Function.Injective (resHom E F K) := by
  intro a b h
  ext x
  exact AlgEquiv.congr_fun h x

def descK (D : IdeleGaloisDescent (𝓞 F) E F) (K : IntermediateField E F) : IdeleGaloisDescent (𝓞 F) ↥K F where
  act := D.act.comp (resHom E F K)
  compat h x := D.compat (h.restrictScalars E) x
  continuous_act h := D.continuous_act (h.restrictScalars E)

theorem descK_act (D : IdeleGaloisDescent (𝓞 F) E F) (K : IntermediateField E F) (h : F ≃ₐ[↥K] F) :
    (descK E F D K).act h = D.act (h.restrictScalars E) := rfl

theorem descK_classAct (D : IdeleGaloisDescent (𝓞 F) E F) (K : IntermediateField E F) (h : F ≃ₐ[↥K] F)
    (c : IdeleClassGroup (𝓞 F) F) : (descK E F D K).classAct h c = D.classAct (h.restrictScalars E) c := rfl

@[reducible] def instK [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)] (K : IntermediateField E F) :
    MulDistribMulAction (F ≃ₐ[↥K] F) (IdeleClassGroup (𝓞 F) F) :=
  MulDistribMulAction.compHom _ (resHom E F K)

theorem smulK_def [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)] (K : IntermediateField E F)
    (h : F ≃ₐ[↥K] F) (c : IdeleClassGroup (𝓞 F) F) :
    (letI := instK E F K; h • c) = h.restrictScalars E • c := rfl

theorem hactK [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)] (D : IdeleGaloisDescent (𝓞 F) E F)
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c) (K : IntermediateField E F) :
    letI := instK E F K
    ∀ (h : F ≃ₐ[↥K] F) (c : IdeleClassGroup (𝓞 F) F), h • c = (descK E F D K).classAct h c :=
  fun h c => hact (h.restrictScalars E) c

def rK (K : IntermediateField E F) (w : HeightOneSpectrum (𝓞 F)) :
    ↥(NumberField.PlaceDecomp.decomp (↥K) F w) →* ↥(NumberField.PlaceDecomp.decomp E F w) where
  toFun h := ⟨(h : F ≃ₐ[↥K] F).restrictScalars E, h.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[scoped simp] theorem rK_coe (K : IntermediateField E F) (w : HeightOneSpectrum (𝓞 F)) (h : ↥(NumberField.PlaceDecomp.decomp (↥K) F w)) :
    ((rK E F K w h : ↥(NumberField.PlaceDecomp.decomp E F w)) : F ≃ₐ[E] F) = (h : F ≃ₐ[↥K] F).restrictScalars E := rfl

theorem rK_smul (K : IntermediateField E F) (w : HeightOneSpectrum (𝓞 F)) (h : ↥(NumberField.PlaceDecomp.decomp (↥K) F w))
    (x : w.adicCompletion F) : rK E F K w h • x = h • x := rfl

theorem rK_smul_units (K : IntermediateField E F) (w : HeightOneSpectrum (𝓞 F)) (h : ↥(NumberField.PlaceDecomp.decomp (↥K) F w))
    (x : (w.adicCompletion F)ˣ) : rK E F K w h • x = h • x := rfl

def lamK [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)] (K : IntermediateField E F)
    (lam : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ ⟶
        Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))
    (w : HeightOneSpectrum (𝓞 F)) :
    letI := instK E F K
    Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp (↥K) F w)) (w.adicCompletion F)ˣ ⟶
      Rep.res (NumberField.PlaceDecomp.decomp (↥K) F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[↥K] F) (IdeleClassGroup (𝓞 F) F)) :=
  letI := instK E F K
  Rep.ofHom { toLinearMap := (Rep.Hom.hom (lam w)).toLinearMap
              isIntertwining' := fun h => (Rep.Hom.hom (lam w)).isIntertwining' (rK E F K w h) }

theorem lamK_hom [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)] (K : IntermediateField E F)
    (lam : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ ⟶
        Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))
    (w : HeightOneSpectrum (𝓞 F)) :
    (Rep.Hom.hom (lamK E F K lam w)).toLinearMap = (Rep.Hom.hom (lam w)).toLinearMap := rfl

theorem lamK_hom_apply [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)] (K : IntermediateField E F)
    (lam : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ ⟶
        Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))
    (w : HeightOneSpectrum (𝓞 F)) (a : Additive (w.adicCompletion F)ˣ) :
    (lamK E F K lam w).hom a = (lam w).hom a := rfl

theorem hlamK [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)] (K : IntermediateField E F)
    (ι : ∀ w : HeightOneSpectrum (𝓞 F), (w.adicCompletion F)ˣ →* (AdeleRing (𝓞 F) F)ˣ)
    (lam : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ ⟶
        Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))
    (hlam : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      (lam w).hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (ι w x) : IdeleClassGroup (𝓞 F) F)) :
    letI := instK E F K
    ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      (lamK E F K lam w).hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (ι w x) : IdeleClassGroup (𝓞 F) F) :=
  fun w x => hlam w x

section Sylow

variable [NumberField E] [IsGalois E F] (P : Subgroup (F ≃ₐ[E] F))

abbrev KP : IntermediateField E F := IntermediateField.fixedField P

theorem finiteDimensional_EF : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ E F

theorem numberField_KP : NumberField ↥(KP E F P) :=
  haveI := finiteDimensional_EF E F
  NumberField.of_module_finite E _

theorem isGalois_KP : IsGalois ↥(KP E F P) F := inferInstance

theorem fixingSubgroup_KP : (KP E F P).fixingSubgroup = P :=
  haveI := finiteDimensional_EF E F
  IntermediateField.fixingSubgroup_fixedField P

def ψ : ↥P ≃* (F ≃ₐ[↥(KP E F P)] F) :=
  (MulEquiv.subgroupCongr (fixingSubgroup_KP E F P).symm).trans (IntermediateField.fixingSubgroupEquiv (KP E F P))

theorem ψ_restrictScalars (g : ↥P) : (ψ E F P g).restrictScalars E = (g : F ≃ₐ[E] F) := rfl

theorem resHom_ψ (g : ↥P) : resHom E F (KP E F P) (ψ E F P g) = (g : F ≃ₐ[E] F) := rfl

theorem coe_ψ_symm (h : F ≃ₐ[↥(KP E F P)] F) : ((ψ E F P).symm h : F ≃ₐ[E] F) = h.restrictScalars E := by
  rw [← ψ_restrictScalars E F P ((ψ E F P).symm h), MulEquiv.apply_symm_apply]

theorem restrictScalars_mem_P (h : F ≃ₐ[↥(KP E F P)] F) : h.restrictScalars E ∈ P := by
  rw [← coe_ψ_symm]; exact SetLike.coe_mem _

theorem isPGroup_KP {p : ℕ} (hP : IsPGroup p ↥P) : IsPGroup p (F ≃ₐ[↥(KP E F P)] F) := hP.of_equiv (ψ E F P)

theorem ψ_smul [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)] (g : ↥P) (c : IdeleClassGroup (𝓞 F) F) :
    (letI := instK E F (KP E F P); ψ E F P g • c) = (g : F ≃ₐ[E] F) • c := rfl

def eK (w : HeightOneSpectrum (𝓞 F)) :
    ↥(NumberField.PlaceDecomp.decomp E F w ⊓ P) ≃* ↥(NumberField.PlaceDecomp.decomp (↥(KP E F P)) F w) where
  toFun g := ⟨ψ E F P ⟨g, g.2.2⟩, g.2.1⟩
  invFun h := ⟨((ψ E F P).symm (h : F ≃ₐ[↥(KP E F P)] F) : F ≃ₐ[E] F),
    ⟨by rw [coe_ψ_symm]; exact h.2, SetLike.coe_mem _⟩⟩
  left_inv g := by
    apply Subtype.ext
    show (((ψ E F P).symm (ψ E F P ⟨g, g.2.2⟩) : ↥P) : F ≃ₐ[E] F) = g
    rw [MulEquiv.symm_apply_apply]
  right_inv h := by
    apply Subtype.ext
    show ψ E F P ⟨(((ψ E F P).symm (h : F ≃ₐ[↥(KP E F P)] F) : ↥P) : F ≃ₐ[E] F), _⟩ = (h : F ≃ₐ[↥(KP E F P)] F)
    simp
  map_mul' _ _ := rfl

theorem eK_restrictScalars (w : HeightOneSpectrum (𝓞 F)) (g : ↥(NumberField.PlaceDecomp.decomp E F w ⊓ P)) :
    ((eK E F P w g : ↥(NumberField.PlaceDecomp.decomp (↥(KP E F P)) F w)) : F ≃ₐ[↥(KP E F P)] F).restrictScalars E =
      (g : F ≃ₐ[E] F) := rfl

theorem rK_eK (w : HeightOneSpectrum (𝓞 F)) (g : ↥(NumberField.PlaceDecomp.decomp E F w ⊓ P)) :
    rK E F (KP E F P) w (eK E F P w g) = Subgroup.inclusion inf_le_left g := rfl

theorem eK_smul (w : HeightOneSpectrum (𝓞 F)) (g : ↥(NumberField.PlaceDecomp.decomp E F w ⊓ P)) (x : w.adicCompletion F) :
    eK E F P w g • x = Subgroup.inclusion inf_le_left g • x := rfl

theorem eK_smul_units (w : HeightOneSpectrum (𝓞 F)) (g : ↥(NumberField.PlaceDecomp.decomp E F w ⊓ P)) (x : (w.adicCompletion F)ˣ) :
    eK E F P w g • x = Subgroup.inclusion inf_le_left g • x := rfl

def toP [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)] :
    letI := instK E F (KP E F P)
    Rep.res (ψ E F P).toMonoidHom (Rep.ofMulDistribMulAction (F ≃ₐ[↥(KP E F P)] F) (IdeleClassGroup (𝓞 F) F)) ⟶
      Rep.res P.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) :=
  letI := instK E F (KP E F P)
  Rep.ofHom { toLinearMap := LinearMap.id
              isIntertwining' := fun _ => LinearMap.ext fun _ => rfl }

theorem toP_hom_apply [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)] (c : Additive (IdeleClassGroup (𝓞 F) F)) :
    (toP E F P).hom c = c := rfl

def toPw [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)] (w : HeightOneSpectrum (𝓞 F)) :
    letI := instK E F (KP E F P)
    Rep.res (eK E F P w).toMonoidHom
        (Rep.res (NumberField.PlaceDecomp.decomp (↥(KP E F P)) F w).subtype
          (Rep.ofMulDistribMulAction (F ≃ₐ[↥(KP E F P)] F) (IdeleClassGroup (𝓞 F) F))) ⟶
      Rep.res (Subgroup.inclusion (inf_le_right : NumberField.PlaceDecomp.decomp E F w ⊓ P ≤ P))
        (Rep.res P.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) :=
  letI := instK E F (KP E F P)
  Rep.ofHom { toLinearMap := LinearMap.id
              isIntertwining' := fun _ => LinearMap.ext fun _ => rfl }

theorem toPw_hom_apply [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)] (w : HeightOneSpectrum (𝓞 F))
    (c : Additive (IdeleClassGroup (𝓞 F) F)) : (toPw E F P w).hom c = c := rfl

def unitsPw (w : HeightOneSpectrum (𝓞 F)) :
    Rep.res (eK E F P w).toMonoidHom
        (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp (↥(KP E F P)) F w)) (w.adicCompletion F)ˣ) ⟶
      Rep.res (Subgroup.inclusion (inf_le_left : NumberField.PlaceDecomp.decomp E F w ⊓ P ≤ NumberField.PlaceDecomp.decomp E F w))
        (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ) :=
  Rep.ofHom { toLinearMap := LinearMap.id
              isIntertwining' := fun _ => LinearMap.ext fun _ => rfl }

end Sylow

section Transport

variable [NumberField E] [IsGalois E F] (P : Subgroup (F ≃ₐ[E] F)) [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]

theorem map_ψ_toP_surjective :
    letI := instK E F (KP E F P)
    Function.Surjective (groupCohomology.map (ψ E F P).toMonoidHom (toP E F P) 2).hom := by
  letI := instK E F (KP E F P)
  intro y
  induction y using groupCohomology.H2_induction_on with
  | h z =>

    let x : (F ≃ₐ[↥(KP E F P)] F) × (F ≃ₐ[↥(KP E F P)] F) →
        (Rep.ofMulDistribMulAction (F ≃ₐ[↥(KP E F P)] F) (IdeleClassGroup (𝓞 F) F)) :=
      fun hh => (z : ↥P × ↥P → _) ((ψ E F P).symm hh.1, (ψ E F P).symm hh.2)
    have hx : x ∈ groupCohomology.cocycles₂ (Rep.ofMulDistribMulAction (F ≃ₐ[↥(KP E F P)] F) (IdeleClassGroup (𝓞 F) F)) := by
      rw [groupCohomology.mem_cocycles₂_def]
      intro h₁ h₂ h₃
      have hz := (groupCohomology.mem_cocycles₂_def (z : ↥P × ↥P → _)).1 z.2
        ((ψ E F P).symm h₁) ((ψ E F P).symm h₂) ((ψ E F P).symm h₃)
      simp only [x, map_mul]

      convert hz using 3 <;> rfl
    refine ⟨(groupCohomology.H2π _).hom ⟨x, hx⟩, ?_⟩
    rw [groupCohomology.H2π_comp_map_apply]

    congr 1

theorem span_map_ψ_toP_eq_top
    (uK : letI := instK E F (KP E F P);
      groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[↥(KP E F P)] F) (IdeleClassGroup (𝓞 F) F)) 2)
    (h : Submodule.span ℤ {uK} = ⊤) :
    letI := instK E F (KP E F P)
    Submodule.span ℤ {(groupCohomology.map (ψ E F P).toMonoidHom (toP E F P) 2).hom uK} = ⊤ := by
  letI := instK E F (KP E F P)
  have hs := map_ψ_toP_surjective E F P
  have : Submodule.span ℤ {(groupCohomology.map (ψ E F P).toMonoidHom (toP E F P) 2).hom uK} =
      Submodule.map (groupCohomology.map (ψ E F P).toMonoidHom (toP E F P) 2).hom (Submodule.span ℤ {uK}) := by
    rw [Submodule.map_span, Set.image_singleton]
  rw [this, h, Submodule.map_top, LinearMap.range_eq_top.2 hs]

theorem map_inclusion_map_ψ_toP (w : HeightOneSpectrum (𝓞 F))
    (uK : letI := instK E F (KP E F P);
      groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[↥(KP E F P)] F) (IdeleClassGroup (𝓞 F) F)) 2) :
    letI := instK E F (KP E F P)
    (groupCohomology.map (Subgroup.inclusion (inf_le_right : NumberField.PlaceDecomp.decomp E F w ⊓ P ≤ P))
        (𝟙 (Rep.res (Subgroup.inclusion (inf_le_right : NumberField.PlaceDecomp.decomp E F w ⊓ P ≤ P))
          (Rep.res P.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))))) 2).hom
      ((groupCohomology.map (ψ E F P).toMonoidHom (toP E F P) 2).hom uK) =
    (groupCohomology.map (eK E F P w).toMonoidHom (toPw E F P w) 2).hom
      ((groupCohomology.map (NumberField.PlaceDecomp.decomp (↥(KP E F P)) F w).subtype
        (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp (↥(KP E F P)) F w).subtype
          (Rep.ofMulDistribMulAction (F ≃ₐ[↥(KP E F P)] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom uK) := by
  letI := instK E F (KP E F P)
  induction uK using groupCohomology.H2_induction_on with
  | h c => simp only [groupCohomology.H2π_comp_map_apply]; rfl

end Transport

end M4aHerbrand.L1Frame
p2m_reactivate "P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand.L1Frame"
p2m_reactivate "P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand"

end
p2m_reactivate "P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand.L1Frame"

namespace groupCohomology
p2m_export "groupCohomology" "H2 H2π mem_cocycles₂_def congr cocycles₂ d₁₂_hom_apply H2π_comp_map_apply map mem_cocycles₂_iff π mapCocycles₂ H2_induction_on H2π_eq_zero_iff"
namespace TopRes
p2m_open "groupCohomology"

universe u
variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)

noncomputable abbrev resTop : groupCohomology A 2 ⟶ groupCohomology (Rep.res (⊤ : Subgroup G).subtype A) 2 :=
  groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype A)) 2

def liftFun (z : ↥(⊤ : Subgroup G) × ↥(⊤ : Subgroup G) → (Rep.res (⊤ : Subgroup G).subtype A)) : G × G → A :=
  fun gh => z (⟨gh.1, Subgroup.mem_top gh.1⟩, ⟨gh.2, Subgroup.mem_top gh.2⟩)

theorem liftFun_mem_cocycles₂ {z : ↥(⊤ : Subgroup G) × ↥(⊤ : Subgroup G) → (Rep.res (⊤ : Subgroup G).subtype A)}
    (hz : z ∈ cocycles₂ (Rep.res (⊤ : Subgroup G).subtype A)) : liftFun A z ∈ cocycles₂ A := by
  rw [mem_cocycles₂_iff] at hz ⊢
  intro g h j
  exact hz ⟨g, Subgroup.mem_top g⟩ ⟨h, Subgroup.mem_top h⟩ ⟨j, Subgroup.mem_top j⟩

theorem mapCocycles₂_liftFun (z : ↥(cocycles₂ (Rep.res (⊤ : Subgroup G).subtype A))) :
    (mapCocycles₂ (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype A))) ⟨liftFun A ⇑z, liftFun_mem_cocycles₂ A z.2⟩ =
      z := by
  apply Subtype.ext
  funext gh
  rfl

theorem resTop_surjective : Function.Surjective (resTop A).hom := by
  intro c
  induction c using H2_induction_on with
  | _ z =>
    refine ⟨(H2π A).hom ⟨liftFun A ⇑z, liftFun_mem_cocycles₂ A z.2⟩, ?_⟩
    rw [resTop, H2π_comp_map_apply, mapCocycles₂_liftFun A z]

theorem resTop_injective : Function.Injective (resTop A).hom := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  induction c using H2_induction_on with
  | _ x =>
    rw [resTop, H2π_comp_map_apply, H2π_eq_zero_iff] at hc
    rw [H2π_eq_zero_iff]

    obtain ⟨y, hy⟩ := hc
    refine ⟨fun g => y ⟨g, Subgroup.mem_top g⟩, ?_⟩
    funext gh
    have := congrFun hy (⟨gh.1, Subgroup.mem_top gh.1⟩, ⟨gh.2, Subgroup.mem_top gh.2⟩)
    first
      | simpa [d₁₂_hom_apply] using this
      | (simp [d₁₂_hom_apply] at this; exact this)
      | (simp [d₁₂_hom_apply] at this ⊢; exact this)

theorem resTop_bijective : Function.Bijective (resTop A).hom :=
  ⟨resTop_injective A, resTop_surjective A⟩

theorem natCard_H2_top_eq :
    Nat.card (groupCohomology (Rep.res (⊤ : Subgroup G).subtype A) 2) = Nat.card (groupCohomology A 2) :=
  (Nat.card_congr (Equiv.ofBijective _ (resTop_bijective A))).symm

theorem span_singleton_resTop_eq_top_iff (u : groupCohomology A 2) :
    Submodule.span k {(resTop A).hom u} = ⊤ ↔ Submodule.span k {u} = ⊤ := by
  let e : groupCohomology A 2 ≃ₗ[k] groupCohomology (Rep.res (⊤ : Subgroup G).subtype A) 2 :=
    LinearEquiv.ofBijective (resTop A).hom (resTop_bijective A)
  have key : Submodule.span k {(resTop A).hom u} = Submodule.map e.toLinearMap (Submodule.span k {u}) := by
    rw [Submodule.map_span, Set.image_singleton]
    rfl
  rw [key]
  constructor
  · intro h
    have hinj : Function.Injective e.toLinearMap := e.injective
    apply Submodule.map_injective_of_injective hinj
    rw [h, Submodule.map_top, LinearMap.range_eq_top.2 e.surjective]
  · intro h
    rw [h, Submodule.map_top, LinearMap.range_eq_top.2 e.surjective]

end groupCohomology.TopRes
p2m_reactivate "P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand.L1Frame"
p2m_reactivate "P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand.L1Frame"

namespace M4aHerbrand
p2m_export "M4aHerbrand" "infPart finPart IdeleClassGroup IdeleGaloisDescent exists_fundamentalClass_ideleClassGroup_res_eq_localFundamentalClass_of_isPGroup_of_ne_two"
namespace L1Local
p2m_open "M4aHerbrand"
p2m_open "ExtCitation.LocalLevel groupCohomology P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.groupCohomology"

variable (q : ℕ) [Fact q.Prime]

theorem isBase_of_mulEquiv (L : IntermediateField ℚ_[q] (PadicAlgCl q)) (G G' : Type) [Group G] [Group G']
    [MulSemiringAction G L] [MulSemiringAction G' L] (e : G' ≃* G) (he : ∀ (g' : G') (x : L), g' • x = e g' • x)
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) (hK : IsBase q L G K) : IsBase q L G' K :=
  ⟨hK.le, fun x => (hK.mem_iff x).trans
    ⟨fun h g' => by rw [he]; exact h _, fun h g => by simpa [he] using h (e.symm g)⟩⟩

theorem isLocalFundamentalClass_of_mulEquiv (L : IntermediateField ℚ_[q] (PadicAlgCl q)) (G G' : Type) [Group G] [Group G']
    [MulSemiringAction G L] [MulDistribMulAction G (↥L)ˣ] [MulSemiringAction G' L] [MulDistribMulAction G' (↥L)ˣ]
    (e : G' ≃* G) (he : ∀ (g' : G') (x : L), g' • x = e g' • x) (heu : ∀ (g' : G') (v : (↥L)ˣ), g' • v = e g' • v)
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction G (↥L)ˣ)) (hu : IsLocalFundamentalClass q L G K u)
    (T : Rep.res e.toMonoidHom (Rep.ofMulDistribMulAction G (↥L)ˣ) ⟶ Rep.ofMulDistribMulAction G' (↥L)ˣ)
    (hT : ∀ v : (↥L)ˣ, T.hom (Additive.ofMul v) = Additive.ofMul v) :
    IsLocalFundamentalClass q L G' K ((groupCohomology.map e.toMonoidHom T 2).hom u) := by
  intro M _ hLM H _ _ _ _ _ NL Nn _ _ e' φ π d ι hι hfin hc

  have d₀ : IsUnramOverlayerDatum q L G K M hLM H NL Nn (e.symm.trans e') φ π :=
    { smul_algebraMap := d.smul_algebraMap
      coe_smul_units := d.coe_smul_units
      mem_base_iff := d.mem_base_iff
      mem_layer_iff := d.mem_layer_iff
      coe_smul_eq := fun g h hgh x => by
        have := d.coe_smul_eq (e.symm g) h hgh x
        rw [he, MulEquiv.apply_symm_apply] at this
        exact this
      card_quotient := by rw [d.card_quotient]; exact Nat.card_congr e.toEquiv
      mem_zpowers := d.mem_zpowers
      frobenius := d.frobenius
      smul_pi := d.smul_pi
      pi_mem := d.pi_mem
      norm_pi_lt := d.norm_pi_lt
      norm_le_norm_pi := d.norm_le_norm_pi }
  have hT' : ∀ y : Rep.res e.toMonoidHom (Rep.ofMulDistribMulAction G (↥L)ˣ), T.hom y = y := fun y => hT (Additive.toMul y)

  let ι₀ : Rep.res ((e.symm.trans e').symm.toMonoidHom.comp (QuotientGroup.mk' NL)) (Rep.ofMulDistribMulAction G (↥L)ˣ) ⟶
      Rep.ofMulDistribMulAction H (↥M)ˣ :=
    Rep.ofHom ⟨ι.hom.toLinearMap, fun h => LinearMap.ext fun v => by
      have hιh := LinearMap.congr_fun (ι.hom.isIntertwining' h) v
      simp only [LinearMap.comp_apply] at hιh ⊢
      refine Eq.trans ?_ hιh
      congr 1
      show Additive.ofMul ((e (e'.symm (QuotientGroup.mk h))) • (Additive.toMul v : (↥L)ˣ)) =
        Additive.ofMul ((e'.symm (QuotientGroup.mk h)) • (Additive.toMul v : (↥L)ˣ))
      rw [heu]⟩
  have key := hu M hLM H NL Nn (e.symm.trans e') φ π d₀ ι₀ (fun v => hι v) hfin hc

  induction u using H2_induction_on with
  | h x =>
    have hcoc : (mapCocycles₂ (e'.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) ι) ((mapCocycles₂ e.toMonoidHom T) x) =
        (mapCocycles₂ ((e.symm.trans e').symm.toMonoidHom.comp (QuotientGroup.mk' NL)) ι₀) x := by
      apply Subtype.ext
      funext hh
      show ι.hom (T.hom (x (e (e'.symm (QuotientGroup.mk hh.1)), e (e'.symm (QuotientGroup.mk hh.2))))) =
        ι.hom (x (e (e'.symm (QuotientGroup.mk hh.1)), e (e'.symm (QuotientGroup.mk hh.2))))
      rw [hT']
    rw [H2π_comp_map_apply] at key
    rw [H2π_comp_map_apply, H2π_comp_map_apply, hcoc]
    exact key

theorem smulCommClass_of_smul_algebraMap (L : IntermediateField ℚ_[q] (PadicAlgCl q)) (S : Type) [Group S] [MulSemiringAction S L]
    (h1 : ∀ (s : S) (x : ℚ_[q]), s • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) : SMulCommClass S ℚ_[q] L :=
  ⟨fun s c x => by rw [Algebra.smul_def, Algebra.smul_def, smul_mul', h1]⟩

noncomputable def fixedBase (L : IntermediateField ℚ_[q] (PadicAlgCl q)) (S : Type) [Group S] [MulSemiringAction S L]
    (h1 : ∀ (s : S) (x : ℚ_[q]), s • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) : IntermediateField ℚ_[q] (PadicAlgCl q) :=
  letI := smulCommClass_of_smul_algebraMap q L S h1
  IntermediateField.lift (FixedPoints.intermediateField S : IntermediateField ℚ_[q] L)

theorem fixedBase_le (L : IntermediateField ℚ_[q] (PadicAlgCl q)) (S : Type) [Group S] [MulSemiringAction S L]
    (h1 : ∀ (s : S) (x : ℚ_[q]), s • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) : fixedBase q L S h1 ≤ L :=
  IntermediateField.lift_le _

theorem mem_fixedBase_iff (L : IntermediateField ℚ_[q] (PadicAlgCl q)) (S : Type) [Group S] [MulSemiringAction S L]
    (h1 : ∀ (s : S) (x : ℚ_[q]), s • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) (x : L) :
    (x : PadicAlgCl q) ∈ fixedBase q L S h1 ↔ ∀ s : S, s • x = x := by
  letI := smulCommClass_of_smul_algebraMap q L S h1
  unfold fixedBase
  rw [IntermediateField.mem_lift]
  exact Iff.rfl

scoped instance finiteDimensional_fixedBase (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (S : Type) [Group S] [MulSemiringAction S L]
    (h1 : ∀ (s : S) (x : ℚ_[q]), s • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) : FiniteDimensional ℚ_[q] (fixedBase q L S h1) :=
  FiniteDimensional.of_injective (IntermediateField.inclusion (fixedBase_le q L S h1)).toLinearMap
    (IntermediateField.inclusion_injective (fixedBase_le q L S h1))

theorem isBase_fixedBase (L : IntermediateField ℚ_[q] (PadicAlgCl q)) (S : Type) [Group S] [MulSemiringAction S L]
    (h1 : ∀ (s : S) (x : ℚ_[q]), s • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) : IsBase q L S (fixedBase q L S h1) :=
  ⟨fixedBase_le q L S h1, mem_fixedBase_iff q L S h1⟩

end M4aHerbrand.L1Local
p2m_reactivate "P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand.L1Frame P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand.L1Local"
p2m_reactivate "P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand.L1Frame"

namespace M4aHerbrand
p2m_export "M4aHerbrand" "infPart finPart IdeleClassGroup IdeleGaloisDescent exists_fundamentalClass_ideleClassGroup_res_eq_localFundamentalClass_of_isPGroup_of_ne_two"
namespace L1Local
p2m_open "M4aHerbrand"

theorem faithfulSMul_of_bridge {G : Type} [Group G] {X Y : Type} [MulAction G X] [SMul G Y] [FaithfulSMul G X]
    (Φ : X ≃ Y) (hΦ : ∀ (g : G) (x : X), Φ (g • x) = g • Φ x) : FaithfulSMul G Y :=
  ⟨fun {g₁ g₂} h => eq_of_smul_eq_smul fun x : X => Φ.injective (by rw [hΦ, hΦ, h])⟩
end M4aHerbrand.L1Local
p2m_reactivate "P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand.L1Frame P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand.L1Local"
p2m_reactivate "P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand.L1Frame P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand.L1Local"

namespace M4aHerbrand
p2m_export "M4aHerbrand" "infPart finPart IdeleClassGroup IdeleGaloisDescent exists_fundamentalClass_ideleClassGroup_res_eq_localFundamentalClass_of_isPGroup_of_ne_two"
namespace L1Local
p2m_open "M4aHerbrand"
open M4aHerbrand.L1Frame

variable (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
  (P : Subgroup (F ≃ₐ[E] F)) (w : HeightOneSpectrum (𝓞 F))

noncomputable def eS : ↥(NumberField.PlaceDecomp.decomp (↥(M4aHerbrand.L1Frame.KP E F P)) F w) ≃* ↥((NumberField.PlaceDecomp.decomp E F w ⊓ P).subgroupOf (NumberField.PlaceDecomp.decomp E F w)) where
  toFun h := ⟨rK E F (M4aHerbrand.L1Frame.KP E F P) w h, Subgroup.mem_subgroupOf.2 ⟨(rK E F (M4aHerbrand.L1Frame.KP E F P) w h).2, restrictScalars_mem_P E F P h.1⟩⟩
  invFun s := eK E F P w (Subgroup.subgroupOfEquivOfLe inf_le_left s)
  left_inv h := Subtype.ext (AlgEquiv.ext fun _ => rfl)
  right_inv s := Subtype.ext (Subtype.ext (AlgEquiv.ext fun _ => rfl))
  map_mul' _ _ := rfl

theorem coe_eS (h : ↥(NumberField.PlaceDecomp.decomp (↥(M4aHerbrand.L1Frame.KP E F P)) F w)) : ((eS E F P w h : ↥((NumberField.PlaceDecomp.decomp E F w ⊓ P).subgroupOf (NumberField.PlaceDecomp.decomp E F w))) : ↥(NumberField.PlaceDecomp.decomp E F w)) =
    rK E F (M4aHerbrand.L1Frame.KP E F P) w h := rfl

@[reducible] noncomputable def actK (L' : Type) [Semiring L'] [MulSemiringAction ↥(NumberField.PlaceDecomp.decomp E F w) L'] : MulSemiringAction ↥(NumberField.PlaceDecomp.decomp (↥(M4aHerbrand.L1Frame.KP E F P)) F w) L' :=
  MulSemiringAction.compHom L' (rK E F (M4aHerbrand.L1Frame.KP E F P) w)

@[reducible] noncomputable def actKu (X : Type) [Monoid X] [MulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) X] : MulDistribMulAction ↥(NumberField.PlaceDecomp.decomp (↥(M4aHerbrand.L1Frame.KP E F P)) F w) X :=
  MulDistribMulAction.compHom X (rK E F (M4aHerbrand.L1Frame.KP E F P) w)

end M4aHerbrand.L1Local
p2m_reactivate "P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand.L1Frame P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand.L1Local"
p2m_reactivate "P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand.L1Frame P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand.L1Local"

namespace M4aHerbrand
p2m_export "M4aHerbrand" "infPart finPart IdeleClassGroup IdeleGaloisDescent exists_fundamentalClass_ideleClassGroup_res_eq_localFundamentalClass_of_isPGroup_of_ne_two"
namespace L1Local
p2m_open "M4aHerbrand"

theorem map_two_surjective_of_mulEquiv {k G G' : Type} [CommRing k] [Group G] [Group G']
    (A : Rep k G) (B : Rep k G') (e : G' ≃* G) (φ : Rep.res e.toMonoidHom A ⟶ B)
    (φinv : B → A) (hφ : ∀ b, φ.hom (φinv b) = b) (hadd : ∀ b b', φinv (b + b') = φinv b + φinv b')
    (hρ : ∀ (g : G) (b : B), A.ρ g (φinv b) = φinv (B.ρ (e.symm g) b)) :
    Function.Surjective (groupCohomology.map e.toMonoidHom φ 2).hom := by
  intro c
  induction c using groupCohomology.H2_induction_on with
  | h z =>

    let x : G × G → A := fun gh => φinv (z (e.symm gh.1, e.symm gh.2))
    have hx : x ∈ groupCohomology.cocycles₂ A := by
      rw [groupCohomology.mem_cocycles₂_iff]
      intro g h j
      have hz := (groupCohomology.mem_cocycles₂_iff (A := B) z).1 z.2 (e.symm g) (e.symm h) (e.symm j)
      simp only [x, map_mul, hρ, ← hadd]
      exact congrArg φinv hz
    refine ⟨(groupCohomology.H2π A).hom ⟨x, hx⟩, ?_⟩
    rw [groupCohomology.H2π_comp_map_apply]
    congr 1
    apply Subtype.ext
    funext gh
    show φ.hom (φinv (z (e.symm (e gh.1), e.symm (e gh.2)))) = z gh
    rw [hφ, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

end M4aHerbrand.L1Local
p2m_reactivate "P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand.L1Frame P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand.L1Local"
p2m_reactivate "P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand.L1Frame P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand.L1Local"

namespace M4aHerbrand
p2m_export "M4aHerbrand" "infPart finPart IdeleClassGroup IdeleGaloisDescent exists_fundamentalClass_ideleClassGroup_res_eq_localFundamentalClass_of_isPGroup_of_ne_two"
namespace L1Local
p2m_open "M4aHerbrand"
open M4aHerbrand.L1Frame

section
variable (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
  (P : Subgroup (F ≃ₐ[E] F)) (w : HeightOneSpectrum (𝓞 F))
  (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [MulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (↥L')ˣ]

noncomputable abbrev SP : Subgroup ↥(NumberField.PlaceDecomp.decomp E F w) := (NumberField.PlaceDecomp.decomp E F w ⊓ P).subgroupOf (NumberField.PlaceDecomp.decomp E F w)

noncomputable def TT :
    letI := actKu E F P w (↥L')ˣ
    Rep.res (eS E F P w).toMonoidHom (Rep.res (SP E F P w).subtype (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (↥L')ˣ)) ⟶
      Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp (↥(M4aHerbrand.L1Frame.KP E F P)) F w) (↥L')ˣ :=
  letI := actKu E F P w (↥L')ˣ
  Rep.ofHom ⟨LinearMap.id, fun _ => LinearMap.ext fun _ => rfl⟩

theorem TT_hom_apply (a : Additive (↥L')ˣ) : (TT E F P w q L').hom a = a := rfl

noncomputable def θK (θ : Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (↥L')ˣ ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F)ˣ) :
    letI := actKu E F P w (↥L')ˣ
    Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp (↥(M4aHerbrand.L1Frame.KP E F P)) F w) (↥L')ˣ ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp (↥(M4aHerbrand.L1Frame.KP E F P)) F w) (w.adicCompletion F)ˣ :=
  letI := actKu E F P w (↥L')ˣ
  Rep.ofHom ⟨(Rep.Hom.hom θ).toLinearMap, fun h => (Rep.Hom.hom θ).isIntertwining' (rK E F (M4aHerbrand.L1Frame.KP E F P) w h)⟩

omit [NumberField E] [IsGalois E F] in
theorem θK_hom_apply (θ : Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (↥L')ˣ ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F)ˣ)
    (a : Additive (↥L')ˣ) : (θK E F P w q L' θ).hom a = θ.hom a := rfl

theorem sqL [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (lam : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ ⟶
        Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))
    (θ : Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (↥L')ˣ ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F)ˣ)
    (v : groupCohomology.H2 (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (↥L')ˣ)) :
    letI := instK E F (M4aHerbrand.L1Frame.KP E F P)
    letI := actKu E F P w (↥L')ˣ
    (groupCohomology.map (Subgroup.inclusion (inf_le_left : (NumberField.PlaceDecomp.decomp E F w) ⊓ P ≤ (NumberField.PlaceDecomp.decomp E F w)))
        (𝟙 (Rep.res (Subgroup.inclusion (inf_le_left : (NumberField.PlaceDecomp.decomp E F w) ⊓ P ≤ (NumberField.PlaceDecomp.decomp E F w))) (Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))))) 2).hom
      ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) (lam w) 2).hom ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) θ 2).hom v)) =
    (groupCohomology.map (eK E F P w).toMonoidHom (toPw E F P w) 2).hom
      ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp (↥(M4aHerbrand.L1Frame.KP E F P)) F w)) (lamK E F (M4aHerbrand.L1Frame.KP E F P) lam w) 2).hom
        ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp (↥(M4aHerbrand.L1Frame.KP E F P)) F w)) (θK E F P w q L' θ) 2).hom
          ((groupCohomology.map (eS E F P w).toMonoidHom (TT E F P w q L') 2).hom
            ((groupCohomology.map (SP E F P w).subtype (𝟙 (Rep.res (SP E F P w).subtype (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (↥L')ˣ))) 2).hom v)))) := by
  induction v using groupCohomology.H2_induction_on with
  | h c => simp only [groupCohomology.H2π_comp_map_apply]; rfl

end
p2m_reactivate "P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand.L1Frame P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand.L1Local"

section
variable (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
  [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)] (P : Subgroup (F ≃ₐ[E] F)) (w : HeightOneSpectrum (𝓞 F))

theorem sqR (v : (letI := instK E F (M4aHerbrand.L1Frame.KP E F P); groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[↥(M4aHerbrand.L1Frame.KP E F P)] F) (IdeleClassGroup (𝓞 F) F)) 2)) :
    letI := instK E F (M4aHerbrand.L1Frame.KP E F P)
    (groupCohomology.map (Subgroup.inclusion (inf_le_right : (NumberField.PlaceDecomp.decomp E F w) ⊓ P ≤ P))
        (𝟙 (Rep.res (Subgroup.inclusion (inf_le_right : (NumberField.PlaceDecomp.decomp E F w) ⊓ P ≤ P)) (Rep.res P.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))))) 2).hom
      ((groupCohomology.map (ψ E F P).toMonoidHom (toP E F P) 2).hom v) =
    (groupCohomology.map (eK E F P w).toMonoidHom (toPw E F P w) 2).hom
      ((groupCohomology.map (NumberField.PlaceDecomp.decomp (↥(M4aHerbrand.L1Frame.KP E F P)) F w).subtype
        (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp (↥(M4aHerbrand.L1Frame.KP E F P)) F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[↥(M4aHerbrand.L1Frame.KP E F P)] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom v) := by
  induction v using groupCohomology.H2_induction_on with
  | h c => simp only [groupCohomology.H2π_comp_map_apply]; rfl

end
p2m_reactivate "P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand.L1Frame P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand.L1Local"

end M4aHerbrand.L1Local
p2m_reactivate "P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand.L1Frame P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand.L1Local"
p2m_reactivate "P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand.L1Frame P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two.M4aHerbrand.L1Local"

theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)
    (ι : ∀ w : HeightOneSpectrum (𝓞 F), (w.adicCompletion F)ˣ →* (AdeleRing (𝓞 F) F)ˣ)
    (hι : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      finPart w (ι w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 F), w' ≠ w → finPart w' (ι w x) = 1) ∧ infPart (ι w x) = 1)
    (lam : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ ⟶
        Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))
    (hlam : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      (lam w).hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (ι w x) : IdeleClassGroup (𝓞 F) F))
    (P : Subgroup (F ≃ₐ[E] F)) (hP : IsPGroup p P) :
    ∃ uP : groupCohomology (Rep.res P.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2,
      Submodule.span ℤ {uP} = ⊤ ∧
      ∀ (w : HeightOneSpectrum (𝓞 F))
        (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
        [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F w)) L'] [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ]
        (Φ : w.adicCompletion F ≃+* L')
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x)
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L'))
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : w.adicCompletion F), Φ (g • x) = g • Φ x)
        (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
        (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp E F w)) K₀)
        (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
        (_ : ∀ v : (↥L')ˣ, ((Additive.toMul (θ.hom (Additive.ofMul v)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = Φ.symm (v : L'))
        (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ))
        (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp E F w)) K₀ u'),
        ((groupCohomology.map (Subgroup.inclusion (inf_le_left : (NumberField.PlaceDecomp.decomp E F w) ⊓ P ≤ (NumberField.PlaceDecomp.decomp E F w)))
            (𝟙 (Rep.res (Subgroup.inclusion (inf_le_left : (NumberField.PlaceDecomp.decomp E F w) ⊓ P ≤ (NumberField.PlaceDecomp.decomp E F w))) (Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))))) 2).hom
          ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) (lam w) 2).hom ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) θ 2).hom u')) : groupCohomology (Rep.res ((NumberField.PlaceDecomp.decomp E F w) ⊓ P).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) =
        ((groupCohomology.map (Subgroup.inclusion (inf_le_right : (NumberField.PlaceDecomp.decomp E F w) ⊓ P ≤ P))
            (𝟙 (Rep.res (Subgroup.inclusion (inf_le_right : (NumberField.PlaceDecomp.decomp E F w) ⊓ P ≤ P)) (Rep.res P.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))))) 2).hom
          uP : groupCohomology (Rep.res ((NumberField.PlaceDecomp.decomp E F w) ⊓ P).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) := by
  classical
  haveI := M4aHerbrand.L1Frame.numberField_KP E F P
  letI instKP := M4aHerbrand.L1Frame.instK E F (M4aHerbrand.L1Frame.KP E F P)
  obtain ⟨uK, -, -, h3K, h4K⟩ :=
    M4aHerbrand.exists_fundamentalClass_ideleClassGroup_res_eq_localFundamentalClass_of_isPGroup_of_ne_two
      (↥(M4aHerbrand.L1Frame.KP E F P)) F p hp2 (M4aHerbrand.L1Frame.isPGroup_KP E F P hP) (M4aHerbrand.L1Frame.descK E F D (M4aHerbrand.L1Frame.KP E F P))
      (M4aHerbrand.L1Frame.hactK E F D hact (M4aHerbrand.L1Frame.KP E F P)) ι hι (M4aHerbrand.L1Frame.lamK E F (M4aHerbrand.L1Frame.KP E F P) lam)
      (M4aHerbrand.L1Frame.hlamK E F (M4aHerbrand.L1Frame.KP E F P) ι lam hlam)
  refine ⟨(groupCohomology.map (M4aHerbrand.L1Frame.ψ E F P).toMonoidHom (M4aHerbrand.L1Frame.toP E F P) 2).hom uK, ?_, ?_⟩
  ·
    exact M4aHerbrand.L1Frame.span_map_ψ_toP_eq_top E F P uK
      ((groupCohomology.TopRes.span_singleton_resTop_eq_top_iff _ uK).1 (h3K ⊤))
  · intro w q _ L' _ _ _ Φ h1 h2 h3 K₀ _ hB θ hθ u' hu'

    haveI : FaithfulSMul ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F) := NumberField.PlaceDecomp.faithfulSMul_decomp E F w
    haveI : FaithfulSMul ↥(NumberField.PlaceDecomp.decomp E F w) L' := M4aHerbrand.L1Local.faithfulSMul_of_bridge Φ.toEquiv h3
    have hsolv : Group.IsSolvable ↥(NumberField.PlaceDecomp.decomp E F w) := ExtCitation.LocalLevel.isSolvable_of_faithfulSMul_of_padic q L' ↥(NumberField.PlaceDecomp.decomp E F w) h1

    let KS := M4aHerbrand.L1Local.fixedBase q L' ↥(M4aHerbrand.L1Local.SP E F P w) (fun s x => h1 (s : ↥(NumberField.PlaceDecomp.decomp E F w)) x)
    have hKS : ExtCitation.LocalLevel.IsBase q L' ↥(M4aHerbrand.L1Local.SP E F P w) KS := M4aHerbrand.L1Local.isBase_fixedBase q L' _ _
    have huS := ExtCitation.LocalLevel.isLocalFundamentalClass_map_subtype q L' ↥(NumberField.PlaceDecomp.decomp E F w) h1 h2 hsolv K₀ hB u' hu'
      (M4aHerbrand.L1Local.SP E F P w) KS hKS

    letI := M4aHerbrand.L1Local.actK E F P w L'
    letI := M4aHerbrand.L1Local.actKu E F P w (↥L')ˣ
    have hBK : ExtCitation.LocalLevel.IsBase q L' ↥(NumberField.PlaceDecomp.decomp (↥(M4aHerbrand.L1Frame.KP E F P)) F w) KS :=
      M4aHerbrand.L1Local.isBase_of_mulEquiv q L' _ ↥(NumberField.PlaceDecomp.decomp (↥(M4aHerbrand.L1Frame.KP E F P)) F w) (M4aHerbrand.L1Local.eS E F P w) (fun _ _ => rfl) KS hKS
    have hu'K := M4aHerbrand.L1Local.isLocalFundamentalClass_of_mulEquiv q L' _ ↥(NumberField.PlaceDecomp.decomp (↥(M4aHerbrand.L1Frame.KP E F P)) F w) (M4aHerbrand.L1Local.eS E F P w)
      (fun _ _ => rfl) (fun _ _ => rfl) KS _ huS (M4aHerbrand.L1Local.TT E F P w q L') (fun _ => rfl)

    have h4 := h4K w q L' Φ (fun h x => h1 (M4aHerbrand.L1Frame.rK E F (M4aHerbrand.L1Frame.KP E F P) w h) x)
      (fun h v => h2 (M4aHerbrand.L1Frame.rK E F (M4aHerbrand.L1Frame.KP E F P) w h) v) (fun h x => h3 (M4aHerbrand.L1Frame.rK E F (M4aHerbrand.L1Frame.KP E F P) w h) x)
      KS hBK (M4aHerbrand.L1Local.θK E F P w q L' θ) (fun v => hθ v) _ hu'K
    rw [M4aHerbrand.L1Local.sqR, ← h4]
    exact M4aHerbrand.L1Local.sqL E F P w q L' lam θ u'

end S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two
end P2MW
export P2MW.S_M4aHerbrand_exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two (solution)
