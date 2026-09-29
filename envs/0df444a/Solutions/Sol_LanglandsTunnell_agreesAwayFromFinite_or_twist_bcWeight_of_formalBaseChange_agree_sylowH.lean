-- Prove2me | solution 1 for LanglandsTunnell.agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/614ad59c-ada4-5d51-b89e-913e19927c71

import Definitions.Def_LanglandsTunnell_QuatH
import Definitions.Def_LanglandsTunnell_DetDictionaryRow
import Definitions.Def_LanglandsTunnell_BcWeight
import Definitions.Def_LanglandsTunnell_P52Interface
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_ArithFrobResidue
import Definitions.Def_FrobeniusDensity_DegOneAsymptotic
import Definitions.Def_LanglandsTunnell_C8Character
import Definitions.Def_LanglandsTunnell_GalRep
import Definitions.Def_LanglandsTunnell_RealizationDictionary
import Theorems.Thm_AutomorphicForm_HeckeEigensystem_agreesAwayFromFinite_or_twist_of_formalBaseChange_agreesAwayFromFinite_of_finrank_eq_two_of_coversModCentre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension"
p2m_attr_erase "instance" "NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions FrobeniusDensity.liesOver_ratBelow AutomorphicForm.GaussTwist.instFiniteLocalGaussFactorValHeightOneSpectrumRingOfIntegersMemFinsetModulusPrimes AutomorphicForm.GaussTwist.instFintypeGaussIndex AutomorphicForm.GaussTwist.instCommGroupGaussIndex IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers"
p2m_attr_erase "simp" "LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq LanglandsTunnell.RankinSelberg.mem_primeFibre LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.cpowChar_apply_val AutomorphicForm.gl2Weyl_val AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.StandardAddChar.ratArchLine_apply NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv"
p2m_attr_erase "simp" "LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AutomorphicForm.rightTranslationEmbed_smul_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply"
p2m_attr_erase "simp" "AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul"
p2m_attr_erase "simp" "RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk IsLocalRing.principalUnits_zero"

set_option autoImplicit false

noncomputable section

open NumberField AutomorphicForm IsDedekindDomain NumberField.AdelicLevel HeckeIntegralSeam
p2m_open "AutomorphicForm.SmoothCusp AutomorphicForm.HeckeEigensystem"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_sylowH sylowH Lift48.Mat DetDictionaryRow bcWeight bcWeight_apply chiNegThreeWeight IsRelDegree"
namespace P2
p2m_export "LanglandsTunnell.P2" "exists_pos_pow_mem relDeg primeOver primeOver_isMaximal under_primeOver"
p2m_open "LanglandsTunnell.P2 LanglandsTunnell"

open Classical in
private theorem isRelDegree_relDeg {G : Type*} [Group G] [Finite G] (H : Subgroup G) (σ : G) :
    IsRelDegree H σ (relDeg H σ) := by
  refine ⟨(Nat.find_spec (exists_pos_pow_mem H σ)).1, (Nat.find_spec (exists_pos_pow_mem H σ)).2, fun m hm hlt h => ?_⟩
  exact Nat.find_min (exists_pos_pow_mem H σ) hlt ⟨hm, h⟩

end LanglandsTunnell.P2

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_sylowH sylowH Lift48.Mat DetDictionaryRow bcWeight bcWeight_apply chiNegThreeWeight IsRelDegree"
namespace P4
p2m_open "LanglandsTunnell"

p2m_open "Matrix FLT.ExplicitLift LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2"

private abbrev _root_.LanglandsTunnell.P4.Mat : Type := Lift48.Mat

p2m_export "LanglandsTunnell.P4" "Mat"
private def redc (z : ℤ√(-2)) : ZMod 3 := ((z.re - z.im : ℤ) : ZMod 3)

private theorem red_eq_redc (z : ℤ√(-2)) : red z = redc z := by
  rw [show z = ⟨z.re, z.im⟩ from rfl]
  simp [red, redc, Zsqrtd.lift, sub_eq_add_neg]

private theorem map_red_eq_map_redc (m : Mat) : m.map red = m.map redc := by
  ext i j; simp [Matrix.map_apply, red_eq_redc]

private theorem relDeg_dvd_of_pow_mem {G : Type*} [Group G] [Finite G] (H : Subgroup G) (σ : G) {m : ℕ}
    (hm : σ ^ m ∈ H) : relDeg H σ ∣ m := by
  have hn := isRelDegree_relDeg H σ
  by_contra hndvd
  have hpos : 0 < m % relDeg H σ :=
    Nat.pos_of_ne_zero fun h0 => hndvd (Nat.dvd_of_mod_eq_zero h0)
  have hlt : m % relDeg H σ < relDeg H σ := Nat.mod_lt _ hn.1
  refine hn.2.2 _ hpos hlt ?_
  have h := Nat.div_add_mod m (relDeg H σ)
  have hrew : σ ^ (m % relDeg H σ) = ((σ ^ relDeg H σ) ^ (m / relDeg H σ))⁻¹ * σ ^ m := by
    rw [← pow_mul, eq_inv_mul_iff_mul_eq, ← pow_add, h]
  rw [hrew]
  exact H.mul_mem (H.inv_mem (H.pow_mem hn.2.1 _)) hm

end LanglandsTunnell.P4

section
open LanglandsTunnell.Lift48 (P16 pw)
set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_sylowH sylowH Lift48.Mat DetDictionaryRow bcWeight bcWeight_apply chiNegThreeWeight IsRelDegree"
namespace P5
p2m_open "LanglandsTunnell"

open FLT.ExplicitLift Matrix

private theorem P16_mul_pw_seven : ∀ x ∈ P16, x * pw x 7 = 1 ∧ pw x 7 * x = 1 ∧ pw x 7 ∈ P16 := by decide

end LanglandsTunnell.P5
end

section
p2m_open "LanglandsTunnell.P4~Mat"
open LanglandsTunnell.Lift48 (K48 Mat P16 mem_closure_iff_mem_K48 pw)
set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_sylowH sylowH Lift48.Mat DetDictionaryRow bcWeight bcWeight_apply chiNegThreeWeight IsRelDegree"
namespace P0
p2m_open "LanglandsTunnell"

open FLT.ExplicitLift Matrix

private theorem eq_one_of_mem_K48_of_map_redc_eq_one :
    ∀ k ∈ K48, k.map redc = 1 → k = 1 := by decide

end LanglandsTunnell.P0

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_sylowH sylowH Lift48.Mat DetDictionaryRow bcWeight bcWeight_apply chiNegThreeWeight IsRelDegree"
namespace P5
p2m_open "LanglandsTunnell"

p2m_open "NumberField Ideal NumberField.Ideal FrobeniusDensity AutomorphicForm IsDedekindDomain Ideal.IsDedekindDomain Matrix FLT.ExplicitLift"
open LanglandsTunnell.P0

private theorem P16_sub_K48 : ∀ p ∈ P16, p ∈ K48 := by decide

private theorem lift_unique : ∀ M ∈ Submonoid.closure ({Slift, Tlift} : Set Mat), ∀ N ∈ P16,
    M.map red = N.map red → M = N := by
  intro M hM N hN h
  have hK : M ∈ K48 := (mem_closure_iff_mem_K48 M).1 hM
  obtain ⟨h7, h7', h7P⟩ := P16_mul_pw_seven N hN
  have hprodK : M * pw N 7 ∈ K48 :=
    (mem_closure_iff_mem_K48 _).1 (Submonoid.mul_mem _ hM ((mem_closure_iff_mem_K48 _).2 (P16_sub_K48 _ h7P)))
  have hone : (M * pw N 7).map redc = 1 := by
    rw [← map_red_eq_map_redc, Matrix.map_mul, h, ← Matrix.map_mul, h7,
      Matrix.map_one _ (map_zero red) (map_one red)]
  have h1 : M * pw N 7 = 1 := eq_one_of_mem_K48_of_map_redc_eq_one _ hprodK hone
  calc M = M * pw N 7 * N := by rw [mul_assoc, h7', mul_one]
    _ = N := by rw [h1, one_mul]

end LanglandsTunnell.P5
end

section
p2m_open "LanglandsTunnell.P4~Mat"
open LanglandsTunnell.Lift48 (Mat P16 det2 det2_eq_det mem_closure_iff_mem_K48)
set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_sylowH sylowH Lift48.Mat DetDictionaryRow bcWeight bcWeight_apply chiNegThreeWeight IsRelDegree"
namespace P5
p2m_open "LanglandsTunnell"

open NumberField Matrix FLT.ExplicitLift
open LanglandsTunnell.P0

private theorem nodup_P16 : P16.Nodup := by decide

private theorem P16_det2 : ∀ M ∈ P16, det2 M = 1 ∨ det2 M = -1 := by decide

private theorem det_map_red_ne_zero (M : Mat) (hM : M ∈ P16) : (M.map red).det ≠ 0 := by
  have h : (M.map red).det = red M.det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rw [h, ← det2_eq_det]
  rcases P16_det2 M hM with h1 | h1
  · rw [h1, map_one]
    exact one_ne_zero
  · rw [h1, map_neg, map_one]
    decide

section Index

variable {L : Type} [Field L] [NumberField L]

private noncomputable def redUnit (M : {M : Mat // M ∈ P16}) : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (M.1.map red) (det_map_red_ne_zero M.1 M.2)

private theorem coe_redUnit (M : {M : Mat // M ∈ P16}) :
    (redUnit M : Matrix (Fin 2) (Fin 2) (ZMod 3)) = M.1.map red := rfl

private noncomputable def toSylowH (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (M : {M : Mat // M ∈ P16}) : sylowH e :=
  ⟨e.symm (redUnit M), M.1, M.2, by rw [MulEquiv.apply_symm_apply, coe_redUnit]⟩

private theorem toSylowH_bijective (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    Function.Bijective (toSylowH e) := by
  constructor
  · rintro ⟨M, hM⟩ ⟨N, hN⟩ h
    have h1 : redUnit ⟨M, hM⟩ = redUnit ⟨N, hN⟩ := e.symm.injective (congrArg Subtype.val h)
    have h2 : M.map red = N.map red := by
      rw [← coe_redUnit ⟨M, hM⟩, ← coe_redUnit ⟨N, hN⟩, h1]
    exact Subtype.ext (lift_unique M ((mem_closure_iff_mem_K48 M).2 (P16_sub_K48 M hM)) N hN h2)
  · rintro ⟨γ, M, hM, hMγ⟩
    refine ⟨⟨M, hM⟩, Subtype.ext ?_⟩
    show e.symm (redUnit ⟨M, hM⟩) = γ
    rw [MulEquiv.symm_apply_eq]
    exact Units.ext (by rw [coe_redUnit]; exact hMγ)

end Index

end LanglandsTunnell.P5
end

section
set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_sylowH sylowH Lift48.Mat DetDictionaryRow bcWeight bcWeight_apply chiNegThreeWeight IsRelDegree"
namespace P4
p2m_open "LanglandsTunnell"

open NumberField IsDedekindDomain Matrix AutomorphicForm

section Transitivity

variable (F F' K : Type) [Field F] [NumberField F] [Field F'] [NumberField F'] [Field K]
  [NumberField K]
  [Algebra (𝓞 F) (𝓞 F')] [Algebra.IsIntegral (𝓞 F) (𝓞 F')]
  [Algebra (𝓞 F') (𝓞 K)] [Algebra.IsIntegral (𝓞 F') (𝓞 K)]
  [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]
  [IsScalarTower (𝓞 F) (𝓞 F') (𝓞 K)]
  {R : Type*} [CommRing R]

omit [NumberField F] [NumberField F'] [NumberField K] in

private theorem _root_.LanglandsTunnell.P4.under_under (𝔓 : HeightOneSpectrum (𝓞 K)) :
    (𝔓.under (𝓞 F')).under (𝓞 F) = 𝔓.under (𝓞 F) :=
  HeightOneSpectrum.ext (Ideal.under_under 𝔓.asIdeal)

p2m_export "LanglandsTunnell.P4" "under_under"
omit [NumberField K] in

private theorem inertiaDeg_under_mul (𝔓 : HeightOneSpectrum (𝓞 K)) :
    (𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal
      = (𝔓.under (𝓞 F)).asIdeal.inertiaDeg' (𝔓.under (𝓞 F')).asIdeal
        * (𝔓.under (𝓞 F')).asIdeal.inertiaDeg' 𝔓.asIdeal := by
  haveI : (𝔓.under (𝓞 F')).asIdeal.LiesOver (𝔓.under (𝓞 F)).asIdeal :=
    ⟨congrArg HeightOneSpectrum.asIdeal (under_under F F' K 𝔓).symm⟩
  haveI : 𝔓.asIdeal.LiesOver (𝔓.under (𝓞 F')).asIdeal := ⟨rfl⟩
  exact Ideal.inertiaDeg_algebra_tower _ _ _

end Transitivity

end LanglandsTunnell.P4

set_option pp.deepTerms true
set_option pp.proofs true
end

section
set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_sylowH sylowH Lift48.Mat DetDictionaryRow bcWeight bcWeight_apply chiNegThreeWeight IsRelDegree"
namespace P2
p2m_export "LanglandsTunnell.P2" "exists_pos_pow_mem relDeg primeOver primeOver_isMaximal under_primeOver"
p2m_open "LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField Ideal NumberField.Ideal IsDedekindDomain Ideal.IsDedekindDomain Matrix FLT.ExplicitLift AutomorphicForm"
open LanglandsTunnell.P0 LanglandsTunnell.P5
open scoped Pointwise

section GalInt

variable {L : Type} [Field L] [NumberField L] [IsGalois ℚ L] (H : Subgroup (L ≃ₐ[ℚ] L))
  (w : HeightOneSpectrum (𝓞 (FixedPoints.intermediateField H : IntermediateField ℚ L)))

private scoped instance isGaloisGroup_ringOfIntegers :
    IsGaloisGroup H (𝓞 (FixedPoints.intermediateField H : IntermediateField ℚ L)) (𝓞 L) :=
  IsGaloisGroup.of_isFractionRing H (𝓞 (FixedPoints.intermediateField H : IntermediateField ℚ L)) (𝓞 L)
    (FixedPoints.intermediateField H : IntermediateField ℚ L) L

end GalInt

end LanglandsTunnell.P2
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2"
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2"

set_option pp.deepTerms true
set_option pp.proofs true
end
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2"

section
set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_sylowH sylowH Lift48.Mat DetDictionaryRow bcWeight bcWeight_apply chiNegThreeWeight IsRelDegree"
namespace P0
p2m_open "LanglandsTunnell"

open Polynomial

private theorem card_le_of_forall_pow_eq {R : Type*} [CommRing R] [IsDomain R] [Finite R] {q : ℕ} (hq : 1 < q)
    (h : ∀ y : R, y ^ q = y) : Nat.card R ≤ q := by
  classical
  haveI := Fintype.ofFinite R
  have hdeg : (X ^ q - X : R[X]).natDegree = q := by
    rw [natDegree_sub_eq_left_of_natDegree_lt] <;> rw [natDegree_X_pow]
    rw [natDegree_X]
    exact hq
  have hf0 : (X ^ q - X : R[X]) ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hdeg
    omega
  have hroots : ∀ y : R, y ∈ (X ^ q - X : R[X]).roots := fun y =>
    (mem_roots hf0).2 (by simp [h y])
  calc Nat.card R = Fintype.card R := Nat.card_eq_fintype_card
    _ ≤ (X ^ q - X : R[X]).roots.toFinset.card :=
        Finset.card_le_card fun y _ => Multiset.mem_toFinset.2 (hroots y)
    _ ≤ Multiset.card (X ^ q - X : R[X]).roots := Multiset.toFinset_card_le _
    _ ≤ (X ^ q - X : R[X]).natDegree := card_roots' _
    _ = q := hdeg

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B] [Finite G] [Algebra.IsInvariant A B G]
  {C : Type*} [CommRing C] [Algebra C B] [Algebra A C] [IsScalarTower A C B]

end LanglandsTunnell.P0
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2"
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_sylowH sylowH Lift48.Mat DetDictionaryRow bcWeight bcWeight_apply chiNegThreeWeight IsRelDegree"
namespace P0
p2m_open "LanglandsTunnell"

section Tower

open NumberField FrobeniusDensity MulAction
open scoped Pointwise

attribute [local instance 10000] Ideal.instMulActionElemPrimesOver

variable {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]

private theorem tower_isGaloisGroup (K : Subgroup (L ≃ₐ[ℚ] L)) : IsGaloisGroup (↥K) (𝓞 (↥(fixFld K))) (𝓞 L) :=
  IsGaloisGroup.of_isFractionRing _ _ _ (↥(fixFld K)) L

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

omit hℓ in
private theorem card_int_quot_ratPrimeIdeal : Nat.card (ℤ ⧸ ratPrimeIdeal ℓ) = ℓ := by
  rw [Nat.card_congr (Int.quotientSpanNatEquivZMod ℓ).toEquiv, Nat.card_zmod]

private theorem finite_int_quot_ratPrimeIdeal : Finite (ℤ ⧸ ratPrimeIdeal ℓ) :=
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  Finite.of_equiv _ (Int.quotientSpanNatEquivZMod ℓ).toEquiv.symm

end Tower
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2"

end LanglandsTunnell.P0
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2"
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_sylowH sylowH Lift48.Mat DetDictionaryRow bcWeight bcWeight_apply chiNegThreeWeight IsRelDegree"
namespace P0
p2m_open "LanglandsTunnell"

section BadPrimes

p2m_open "NumberField Ideal NumberField.Ideal IsDedekindDomain Ideal.IsDedekindDomain FrobeniusDensity"
open scoped Pointwise

variable (L : Type*) [Field L] [NumberField L]

private theorem tower_exists_smul_ne {g : L ≃ₐ[ℚ] L} (hg : g ≠ 1) : ∃ x : 𝓞 L, g • x ≠ x := by
  by_contra hcon'
  have hcon : ∀ x : 𝓞 L, g • x = x := fun x => not_not.mp fun h => hcon' ⟨x, h⟩
  refine hg (AlgEquiv.ext fun z => ?_)
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 L) (K := L) z
  have hx : g (algebraMap (𝓞 L) L x) = algebraMap (𝓞 L) L x :=
    congrArg (algebraMap (𝓞 L) L) (hcon x)
  have hy' : g (algebraMap (𝓞 L) L y) = algebraMap (𝓞 L) L y :=
    congrArg (algebraMap (𝓞 L) L) (hcon y)
  rw [← hxy, map_div₀, hx, hy', AlgEquiv.one_apply]

private theorem tower_finite_setOf_inertia_ne_bot :
    {v : HeightOneSpectrum (𝓞 L) | v.asIdeal.inertia (L ≃ₐ[ℚ] L) ≠ ⊥}.Finite := by
  classical
  choose x hx using fun g : {g : L ≃ₐ[ℚ] L // g ≠ 1} => tower_exists_smul_ne L g.2
  refine Set.Finite.subset (Set.Finite.biUnion
    (Set.finite_univ (α := {g : L ≃ₐ[ℚ] L // g ≠ 1}))
    (fun g _ => Ideal.finite_factors (I := Ideal.span {g.1 • x g - x g}) ?_)) ?_
  · rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot, sub_eq_zero]
    exact hx g
  · intro v hv
    simp only [Set.mem_setOf_eq] at hv
    obtain ⟨g, hgmem, hgne⟩ := (v.asIdeal.inertia (L ≃ₐ[ℚ] L)).bot_or_exists_ne_one.resolve_left hv
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨⟨g, hgne⟩, Set.mem_univ _, ?_⟩
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hgmem (x ⟨g, hgne⟩)

private noncomputable def towerBadPrimes : Finset ℕ :=
  insert 0 (insert 1 (((tower_finite_setOf_inertia_ne_bot L).image
    (fun v => Nat.card (ℤ ⧸ v.asIdeal.under ℤ))).toFinset))

variable {L}

private theorem tower_inertia_eq_bot_of_notMem {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓbad : ℓ ∉ towerBadPrimes L)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [hQ : Q.LiesOver (ratPrimeIdeal ℓ)] : Q.inertia (L ≃ₐ[ℚ] L) = ⊥ := by
  by_contra hcon
  apply hℓbad
  have hQbot : Q ≠ ⊥ := ne_bot_of_liesOver_ratPrimeIdeal hℓ
  refine Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr ?_)))
  rw [Set.Finite.mem_toFinset]
  refine ⟨⟨Q, inferInstance, hQbot⟩, hcon, ?_⟩
  change Nat.card (ℤ ⧸ Q.under ℤ) = ℓ
  rw [← hQ.over, Nat.card_congr (Int.quotientSpanNatEquivZMod ℓ).toEquiv, Nat.card_zmod]

end BadPrimes
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2"

end LanglandsTunnell.P0
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2"
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2"

section
set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_sylowH sylowH Lift48.Mat DetDictionaryRow bcWeight bcWeight_apply chiNegThreeWeight IsRelDegree"
namespace P5
p2m_open "LanglandsTunnell"

p2m_open "NumberField Ideal NumberField.Ideal FrobeniusDensity IsDedekindDomain Ideal.IsDedekindDomain AutomorphicForm"

section RatPrimeQuotient

variable {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
  [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower ℚ L (AlgebraicClosure ℚ)]

omit [IsGalois ℚ L] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower ℚ L (AlgebraicClosure ℚ)] in
open Rat.HeightOneSpectrum in

private theorem under_eq_ratPrime_of_natCast_mem {E : IntermediateField ℚ L}
    (𝔓 : HeightOneSpectrum (𝓞 ↥E)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hmem : ((ℓ : ℕ) : 𝓞 ↥E) ∈ 𝔓.asIdeal) :
    𝔓.under (𝓞 ℚ) = ratPrime ⟨ℓ, hℓ⟩ := by
  set v : HeightOneSpectrum (𝓞 ℚ) := 𝔓.under (𝓞 ℚ) with hv_def

  have hmem_v : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    have : algebraMap (𝓞 ℚ) (𝓞 ↥E) ((ℓ : ℕ) : 𝓞 ℚ) ∈ 𝔓.asIdeal := by
      rwa [map_natCast]
    exact this

  have hdvd : natGenerator v ∣ ℓ := by
    rw [natGenerator_dvd_iff]
    have h := Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) hmem_v
    rwa [map_natCast] at h
  have heq : natGenerator v = ℓ := (Nat.prime_dvd_prime_iff_eq (prime_natGenerator v) hℓ).mp hdvd
  have happ : primesEquiv (R := 𝓞 ℚ) v = ⟨ℓ, hℓ⟩ := Subtype.ext heq
  rw [hv_def, ratPrime, ← happ, Equiv.symm_apply_apply]

private theorem card_quot_ratPrime (ℓ : ℕ) (hℓ : ℓ.Prime) :
    Nat.card (𝓞 ℚ ⧸ (ratPrime ⟨ℓ, hℓ⟩).asIdeal) = ℓ := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hid : (ratPrime ⟨ℓ, hℓ⟩).asIdeal
      = (Ideal.span {((ℓ : ℕ) : ℤ)}).map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm := by
    simp [ratPrime, Rat.HeightOneSpectrum.primesEquiv,
      IsDedekindDomain.HeightOneSpectrum.ofPrime_asIdeal]
  rw [hid]
  have hequiv := Ideal.quotientEquiv (Ideal.span {((ℓ : ℕ) : ℤ)})
    ((Ideal.span {((ℓ : ℕ) : ℤ)}).map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm)
    (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm rfl
  rw [← Nat.card_congr hequiv.toEquiv]
  exact LanglandsTunnell.P0.card_int_quot_ratPrimeIdeal

variable {e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)}

end RatPrimeQuotient
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2"

end LanglandsTunnell.P5
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2"
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2"

section
set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_sylowH sylowH Lift48.Mat DetDictionaryRow bcWeight bcWeight_apply chiNegThreeWeight IsRelDegree"
namespace P4
p2m_open "LanglandsTunnell"

p2m_open "NumberField Ideal NumberField.Ideal FrobeniusDensity AutomorphicForm IsDedekindDomain Ideal.IsDedekindDomain Matrix FLT.ExplicitLift"
p2m_open "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P0 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P5 LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2"
open scoped Pointwise MatrixGroups

local notation "M₃" => Matrix (Fin 2) (Fin 2) (ZMod 3)

section FrobPower

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

private theorem mk_pow_smul_of_isArithFrobAt {σ : G} {Q : Ideal B} (hF : IsArithFrobAt A σ Q)
    (n : ℕ) (x : B) :
    Ideal.Quotient.mk Q (σ ^ n • x)
      = Ideal.Quotient.mk Q x ^ (Nat.card (A ⧸ Q.under A) ^ n) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hx : Ideal.Quotient.mk Q (σ • x)
        = Ideal.Quotient.mk Q x ^ Nat.card (A ⧸ Q.under A) := by
      rw [← map_pow, Ideal.Quotient.eq]
      exact hF x
    rw [pow_succ, mul_smul, ih (σ • x), hx, ← pow_mul, pow_succ']

variable [Finite G] [Algebra.IsInvariant A B G] {C : Type*} [CommRing C] [Algebra C B]

private theorem pow_card_pow_eq_self_of_pow_mem {H : Subgroup G} [SMulCommClass (↥H) C B]
    (Q : Ideal B) [Q.IsPrime] [Finite (B ⧸ Q)] {n : ℕ}
    (hmem : arithFrobAt A G Q ^ n ∈ H) (y : C ⧸ Q.under C) :
    y ^ (Nat.card (A ⧸ Q.under A) ^ n) = y := by
  have hF : IsArithFrobAt A (arithFrobAt A G Q) Q := IsArithFrobAt.arithFrobAt A G Q
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hfix : (arithFrobAt A G Q ^ n) • algebraMap C B c = algebraMap C B c := by
    have h : (⟨arithFrobAt A G Q ^ n, hmem⟩ : ↥H) • algebraMap C B c = algebraMap C B c := by
      rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]
    exact h
  have hq := mk_pow_smul_of_isArithFrobAt hF n (algebraMap C B c)
  rw [hfix] at hq
  rw [← map_pow, Ideal.Quotient.eq, Ideal.under_def, Ideal.mem_comap, map_sub, map_pow,
    ← Ideal.Quotient.eq, map_pow]
  exact hq.symm

end FrobPower
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2"

section RationalPrimeUnder

variable {L : Type} [Field L] [NumberField L]

private noncomputable def ratOf {e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)}
    (v : HeightOneSpectrum (𝓞 (↥(fixFld (sylowH e))))) : ℕ :=
  ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)) (v.under (𝓞 ℚ))).1

variable [IsGalois ℚ L]

variable [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower ℚ L (AlgebraicClosure ℚ)]

end RationalPrimeUnder
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2"

end LanglandsTunnell.P4
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2"
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2"

set_option pp.deepTerms true
set_option pp.proofs true
end
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2"

section
set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_sylowH sylowH Lift48.Mat DetDictionaryRow bcWeight bcWeight_apply chiNegThreeWeight IsRelDegree"
namespace P4
p2m_open "LanglandsTunnell"

p2m_open "NumberField Ideal NumberField.Ideal FrobeniusDensity AutomorphicForm IsDedekindDomain Ideal.IsDedekindDomain Matrix FLT.ExplicitLift"
p2m_open "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P0 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P5 LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2"
open scoped Pointwise MatrixGroups

local notation "M₃" => Matrix (Fin 2) (Fin 2) (ZMod 3)

section RelDeg

variable {G : Type*} [Group G] [Finite G]

private theorem relDeg_pos (H : Subgroup G) (σ : G) : 0 < relDeg H σ := (isRelDegree_relDeg H σ).1

private theorem relDeg_dvd_relDeg {H H' : Subgroup G} (hle : H' ≤ H) (σ : G) : relDeg H σ ∣ relDeg H' σ :=
  relDeg_dvd_of_pow_mem H σ (hle (isRelDegree_relDeg H' σ).2.1)

end RelDeg
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2"

section PowMem

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
  [Finite G] [Algebra.IsInvariant A B G] {C : Type*} [CommRing C] [Algebra C B]

private theorem pow_arithFrobAt_mem_of_card_under_eq_pow {H : Subgroup G}
    [SMulCommClass (↥H) C B] [Algebra.IsInvariant C B (↥H)]
    (Q : Ideal B) [Q.IsPrime] [Finite (B ⧸ Q)] {f : ℕ}
    (hcard : Nat.card (C ⧸ Q.under C) = Nat.card (A ⧸ Q.under A) ^ f)
    (hin : Q.inertia G = ⊥) : arithFrobAt A G Q ^ f ∈ H := by
  obtain ⟨s, hs⟩ := IsArithFrobAt.exists_of_isInvariant C (↥H) Q
  have hτ : IsArithFrobAt A (arithFrobAt A G Q) Q := IsArithFrobAt.arithFrobAt A G Q

  have key : ∀ x : B, (arithFrobAt A G Q ^ f) • x - (s : G) • x ∈ Q := by
    intro x
    have h1 := mk_pow_smul_of_isArithFrobAt hτ f x
    have h2 : (s : G) • x - x ^ (Nat.card (A ⧸ Q.under A) ^ f) ∈ Q := by
      have h := hs x
      rwa [hcard] at h
    rw [← Ideal.Quotient.eq, map_pow] at h2
    rw [← Ideal.Quotient.eq, h1, h2]

  have hmem : arithFrobAt A G Q ^ f * (s : G)⁻¹ ∈ Q.inertia G := by
    intro x
    have h := key ((s : G)⁻¹ • x)
    rwa [smul_inv_smul, ← mul_smul] at h
  rw [hin, Subgroup.mem_bot, mul_inv_eq_one] at hmem
  rw [hmem]
  exact s.2

end PowMem
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2"

section ResidueDegree

variable {L : Type} [Field L] [NumberField L]

private theorem natCast_mem_under' (H : Subgroup (L ≃ₐ[ℚ] L)) {ℓ : ℕ}
    (Q : Ideal (𝓞 L)) [hQl : Q.LiesOver (ratPrimeIdeal ℓ)] :
    ((ℓ : ℕ) : 𝓞 (↥(fixFld H))) ∈ Q.under (𝓞 (↥(fixFld H))) := by
  have h1 : ((ℓ : ℕ) : ℤ) ∈ ratPrimeIdeal ℓ := Ideal.mem_span_singleton_self _
  rw [hQl.over] at h1
  have h2 : algebraMap ℤ (𝓞 L) ((ℓ : ℕ) : ℤ) ∈ Q := Ideal.mem_comap.mp h1
  rw [Ideal.mem_comap, map_natCast]
  simpa using h2

variable [IsGalois ℚ L]

private theorem inertiaDeg_eq_relDeg (H : Subgroup (L ≃ₐ[ℚ] L)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (ratPrimeIdeal ℓ)] [Finite (𝓞 L ⧸ Q)]
    (hI : Q.inertia (L ≃ₐ[ℚ] L) = ⊥)
    (w : HeightOneSpectrum (𝓞 (↥(fixFld H)))) (hw : w.asIdeal = Q.under (𝓞 (↥(fixFld H)))) :
    (w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal = relDeg H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI hQmax : Q.IsMaximal := Ideal.IsPrime.isMaximal ‹_› (ne_bot_of_liesOver_ratPrimeIdeal hℓ)
  haveI hZmax : (Q.under ℤ).IsMaximal := by
    rw [← ‹Q.LiesOver (ratPrimeIdeal ℓ)›.over]; infer_instance
  haveI hZfin : Finite (ℤ ⧸ Q.under ℤ) := by
    rw [← ‹Q.LiesOver (ratPrimeIdeal ℓ)›.over]; exact finite_int_quot_ratPrimeIdeal
  haveI : Fintype (ℤ ⧸ Q.under ℤ) := Fintype.ofFinite _
  haveI hGG := tower_isGaloisGroup (L := L) H
  haveI := hGG.commutes
  haveI := hGG.isInvariant
  have hcardZ : Nat.card (ℤ ⧸ Q.under ℤ) = ℓ := by
    rw [← ‹Q.LiesOver (ratPrimeIdeal ℓ)›.over]; exact card_int_quot_ratPrimeIdeal

  haveI hkfin : Finite ((𝓞 (↥(fixFld H))) ⧸ w.asIdeal) := by
    rw [hw]
    exact Finite.of_injective _
      (Ideal.quotientMap_injective (I := Q) (f := algebraMap (𝓞 (↥(fixFld H))) (𝓞 L)))
  haveI : Fintype ((𝓞 (↥(fixFld H))) ⧸ w.asIdeal) := Fintype.ofFinite _
  haveI hkmax : w.asIdeal.IsMaximal := w.isMaximal

  have hunder : w.under (𝓞 ℚ) = ratPrime ⟨ℓ, hℓ⟩ :=
    under_eq_ratPrime_of_natCast_mem w hℓ (by rw [hw]; exact natCast_mem_under' H Q)
  have hcb : Nat.card (𝓞 ℚ ⧸ (w.under (𝓞 ℚ)).asIdeal) = ℓ := by
    rw [hunder]; exact card_quot_ratPrime ℓ hℓ
  haveI : (w.under (𝓞 ℚ)).asIdeal.IsMaximal := (w.under (𝓞 ℚ)).isMaximal
  haveI hoverP : w.asIdeal.LiesOver (w.under (𝓞 ℚ)).asIdeal := ⟨rfl⟩

  have hcardf : Nat.card ((𝓞 (↥(fixFld H))) ⧸ w.asIdeal)
      = ℓ ^ ((w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal) := by
    letI := Ideal.Quotient.field (w.under (𝓞 ℚ)).asIdeal
    rw [Ideal.inertiaDeg_algebraMap, Module.natCard_eq_pow_finrank (K := 𝓞 ℚ ⧸ (w.under (𝓞 ℚ)).asIdeal), hcb]
  have hℓ1 : 1 < ℓ := hℓ.one_lt

  have hle : (w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal ≤ relDeg H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) := by
    letI := Ideal.Quotient.field w.asIdeal
    have hpow : ∀ y : (𝓞 (↥(fixFld H))) ⧸ w.asIdeal,
        y ^ (ℓ ^ relDeg H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q)) = y := by
      rw [hw]
      intro y
      have h := pow_card_pow_eq_self_of_pow_mem (A := ℤ) (C := 𝓞 (↥(fixFld H))) (H := H) Q
        (isRelDegree_relDeg H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q)).2.1 y
      rwa [hcardZ] at h
    have h1lt : 1 < ℓ ^ relDeg H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) := Nat.one_lt_pow (relDeg_pos H _).ne' hℓ1
    have hcle := card_le_of_forall_pow_eq h1lt hpow
    rw [hcardf] at hcle
    exact (Nat.pow_le_pow_iff_right hℓ1).mp hcle

  have hge : relDeg H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) ≤ (w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal := by
    have hcard' : Nat.card ((𝓞 (↥(fixFld H))) ⧸ Q.under (𝓞 (↥(fixFld H))))
        = Nat.card (ℤ ⧸ Q.under ℤ) ^ ((w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal) := by
      rw [hcardZ, ← hw, hcardf]
    have hmem := pow_arithFrobAt_mem_of_card_under_eq_pow (A := ℤ) (C := 𝓞 (↥(fixFld H))) (H := H) Q hcard' hI
    have hdvd := relDeg_dvd_of_pow_mem H _ hmem
    exact Nat.le_of_dvd (Ideal.inertiaDeg'_pos (w.under (𝓞 ℚ)).asIdeal w.asIdeal) hdvd
  exact le_antisymm hle hge

end ResidueDegree
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2"

end LanglandsTunnell.P4
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2"
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2"

set_option pp.deepTerms true
set_option pp.proofs true
end
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2"

section
set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_sylowH sylowH Lift48.Mat DetDictionaryRow bcWeight bcWeight_apply chiNegThreeWeight IsRelDegree"
namespace P4
p2m_open "LanglandsTunnell"

open NumberField IsDedekindDomain AutomorphicForm FLT.ExplicitLift EisensteinWeightOne
p2m_open "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P5 LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P0"
p2m_open "FrobeniusDensity Ideal NumberField.Ideal"
open scoped MatrixGroups

local notation "ZRing" => (ℤ√(-2))

section Prelim

variable {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
  {e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)}

omit [IsGalois ℚ L] in

private theorem ratOf_prime (u : HeightOneSpectrum (𝓞 (↥(fixFld (sylowH e))))) : (ratOf u).Prime :=
  ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)) (u.under (𝓞 ℚ))).2

omit [IsGalois ℚ L] in

private theorem under_eq_ratPrime_ratOf (u : HeightOneSpectrum (𝓞 (↥(fixFld (sylowH e))))) :
    u.under (𝓞 ℚ) = ratPrime ⟨ratOf u, ratOf_prime u⟩ := by
  rw [ratPrime]
  exact (Equiv.symm_apply_apply _ _).symm

private theorem natCast_mem_ratPrime_asIdeal (ℓ : ℕ) (hℓ : ℓ.Prime) :
    ((ℓ : ℕ) : 𝓞 ℚ) ∈ (ratPrime ⟨ℓ, hℓ⟩).asIdeal := by
  have hid : (ratPrime ⟨ℓ, hℓ⟩).asIdeal
      = (Ideal.span {((ℓ : ℕ) : ℤ)}).comap (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) := by
    simp [ratPrime, Rat.HeightOneSpectrum.primesEquiv,
      IsDedekindDomain.HeightOneSpectrum.ofPrime_asIdeal]
  rw [hid, Ideal.mem_comap, map_natCast]
  exact Ideal.mem_span_singleton_self _

omit [IsGalois ℚ L] in

private theorem asIdeal_under_int (u : HeightOneSpectrum (𝓞 (↥(fixFld (sylowH e))))) :
    u.asIdeal.under ℤ = ratPrimeIdeal (ratOf u) := by
  haveI : Fact (ratOf u).Prime := ⟨ratOf_prime u⟩
  refine ((Int.ideal_span_isMaximal_of_prime (ratOf u)).eq_of_le
    (Ideal.IsPrime.under ℤ u.asIdeal).ne_top ?_).symm
  show Ideal.span {((ratOf u : ℕ) : ℤ)} ≤ u.asIdeal.under ℤ
  rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap, map_natCast]

  have hmem := natCast_mem_ratPrime_asIdeal (ratOf u) (ratOf_prime u)
  rw [← under_eq_ratPrime_ratOf u] at hmem
  have hmem2 : algebraMap (𝓞 ℚ) (𝓞 (↥(fixFld (sylowH e)))) ((ratOf u : ℕ) : 𝓞 ℚ)
      ∈ u.asIdeal := hmem
  simpa using hmem2

omit [IsGalois ℚ L] in

private scoped instance primeOver_liesOver_ratPrimeIdeal (u : HeightOneSpectrum (𝓞 (↥(fixFld (sylowH e))))) :
    (primeOver (sylowH e) u).LiesOver (ratPrimeIdeal (ratOf u)) := by
  constructor
  rw [← Ideal.under_under (A := ℤ) (B := 𝓞 (↥(fixFld (sylowH e)))) (C := 𝓞 L),
    under_primeOver, asIdeal_under_int]

private scoped instance primeOver_isPrime (u : HeightOneSpectrum (𝓞 (↥(fixFld (sylowH e))))) :
    (primeOver (sylowH e) u).IsPrime :=
  (primeOver_isMaximal (sylowH e) u).isPrime

end Prelim
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2"

end LanglandsTunnell.P4
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P4"
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P4"

section
open LanglandsTunnell.Lift48 (Mat P16 length_P16)
set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_sylowH sylowH Lift48.Mat DetDictionaryRow bcWeight bcWeight_apply chiNegThreeWeight IsRelDegree"
namespace P5
p2m_open "LanglandsTunnell"

open NumberField Matrix FLT.ExplicitLift
open LanglandsTunnell.P0

private theorem natCard_P16 : Nat.card {M : Mat // M ∈ P16} = 16 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun M => (List.mem_toFinset (l := P16) (a := M)).symm)),
    Nat.card_eq_finsetCard, List.toFinset_card_of_nodup nodup_P16, length_P16]

private theorem natCard_GL2_F3 : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) = 48 := by
  rw [Matrix.card_GL_field, Fin.prod_univ_two, ZMod.card]
  norm_num

section Index

variable {L : Type} [Field L] [NumberField L]

private theorem natCard_sylowH (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    Nat.card (sylowH e) = 16 := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (toSylowH_bijective e)), natCard_P16]

private theorem natCard_gal (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    Nat.card (L ≃ₐ[ℚ] L) = 48 := by
  rw [Nat.card_congr e.toEquiv, natCard_GL2_F3]

private theorem index_sylowH (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    (sylowH e).index = 3 := by
  have h := (sylowH e).card_mul_index
  rw [natCard_sylowH, natCard_gal e] at h
  omega

end Index
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P4"

end LanglandsTunnell.P5
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P4"
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P4"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P4"

section
set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_sylowH sylowH Lift48.Mat DetDictionaryRow bcWeight bcWeight_apply chiNegThreeWeight IsRelDegree"
namespace P5
p2m_open "LanglandsTunnell"

open NumberField

variable {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]

private theorem finrank_fixFld_sylowH
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    Module.finrank ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e)) = 3 := by
  have htop : Module.finrank ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e)) L =
      Nat.card ↥(LanglandsTunnell.sylowH e) :=
    IntermediateField.finrank_fixedField_eq_card (LanglandsTunnell.sylowH e)
  have htower : Module.finrank ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e)) *
      Module.finrank ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e)) L =
      Module.finrank ℚ L :=
    Module.finrank_mul_finrank ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e)) L
  have hgal : Nat.card (L ≃ₐ[ℚ] L) = Module.finrank ℚ L :=
    IsGalois.card_aut_eq_finrank ℚ L
  have hmul : Nat.card ↥(LanglandsTunnell.sylowH e) * (LanglandsTunnell.sylowH e).index =
      Nat.card (L ≃ₐ[ℚ] L) :=
    (LanglandsTunnell.sylowH e).card_mul_index
  have hidx : (LanglandsTunnell.sylowH e).index = 3 := LanglandsTunnell.P5.index_sylowH e
  have hpos : 0 < Nat.card ↥(LanglandsTunnell.sylowH e) := Nat.card_pos
  have hkey : Module.finrank ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e)) *
      Nat.card ↥(LanglandsTunnell.sylowH e) =
      Nat.card ↥(LanglandsTunnell.sylowH e) * 3 := by
    rw [← htop, htower, ← hgal, ← hmul, hidx, htop]
  rw [Nat.mul_comm (Nat.card ↥(LanglandsTunnell.sylowH e)) 3] at hkey
  exact Nat.eq_of_mul_eq_mul_right hpos hkey

end LanglandsTunnell.P5
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P4"
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P4"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P4"

section
set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_sylowH sylowH Lift48.Mat DetDictionaryRow bcWeight bcWeight_apply chiNegThreeWeight IsRelDegree"
namespace P4
p2m_open "LanglandsTunnell"

p2m_open "NumberField Ideal NumberField.Ideal FrobeniusDensity AutomorphicForm IsDedekindDomain Ideal.IsDedekindDomain Matrix FLT.ExplicitLift"
p2m_open "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P0 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P5 LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2 EisensteinWeightOne"
open scoped Pointwise MatrixGroups

local notation "M₃" => Matrix (Fin 2) (Fin 2) (ZMod 3)

section Signs

private theorem intCast_chiNegThree (n : ℕ) : ((chiNegThree n : ℤ) : ZMod 3) = (n : ZMod 3) := by
  rw [← ZMod.natCast_mod n 3]
  unfold chiNegThree
  rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h | h | h <;> simp [h]
  decide

end Signs
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P4"

end LanglandsTunnell.P4
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P4"
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P4"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P4"

section
set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_sylowH sylowH Lift48.Mat DetDictionaryRow bcWeight bcWeight_apply chiNegThreeWeight IsRelDegree"
namespace P4
p2m_open "LanglandsTunnell"

p2m_open "NumberField Ideal NumberField.Ideal FrobeniusDensity AutomorphicForm IsDedekindDomain Ideal.IsDedekindDomain Matrix FLT.ExplicitLift"
p2m_open "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P0 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P5 LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2"
open scoped Pointwise MatrixGroups

local notation "M₃" => Matrix (Fin 2) (Fin 2) (ZMod 3)

section Generic

variable {L : Type} [Field L] [NumberField L]

private theorem natCast_mem_under_intermediateField (E : IntermediateField ℚ L) {ℓ : ℕ} (Q : Ideal (𝓞 L))
    [hQl : Q.LiesOver (ratPrimeIdeal ℓ)] : ((ℓ : ℕ) : 𝓞 ↥E) ∈ Q.under (𝓞 ↥E) := by
  have h1 : ((ℓ : ℕ) : ℤ) ∈ ratPrimeIdeal ℓ := Ideal.mem_span_singleton_self _
  rw [hQl.over] at h1
  have h2 : algebraMap ℤ (𝓞 L) ((ℓ : ℕ) : ℤ) ∈ Q := Ideal.mem_comap.mp h1
  rw [Ideal.mem_comap, map_natCast]
  simpa using h2

private noncomputable def placeUnderH (H : Subgroup (L ≃ₐ[ℚ] L)) {ℓ : ℕ} (hℓ : ℓ.Prime) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver (ratPrimeIdeal ℓ)] : HeightOneSpectrum (𝓞 (↥(fixFld H))) :=
  ⟨Q.under _, Ideal.IsPrime.under _ Q, fun hbot => by
    have h := natCast_mem_under_intermediateField (fixFld H) (ℓ := ℓ) Q
    rw [hbot, Ideal.mem_bot] at h
    exact hℓ.ne_zero (by exact_mod_cast h)⟩

private theorem placeUnderH_asIdeal (H : Subgroup (L ≃ₐ[ℚ] L)) {ℓ : ℕ} (hℓ : ℓ.Prime) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver (ratPrimeIdeal ℓ)] : (placeUnderH H hℓ Q).asIdeal = Q.under (𝓞 (↥(fixFld H))) := rfl

end Generic
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P4"

end LanglandsTunnell.P4
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P4"
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P4"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P4"

section
set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_sylowH sylowH Lift48.Mat DetDictionaryRow bcWeight bcWeight_apply chiNegThreeWeight IsRelDegree"
namespace P4
p2m_open "LanglandsTunnell"

open NumberField IsDedekindDomain AutomorphicForm FLT.ExplicitLift EisensteinWeightOne
p2m_open "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P5 LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P0"
p2m_open "FrobeniusDensity Ideal NumberField.Ideal"
open scoped MatrixGroups

local notation "ZRing" => (ℤ√(-2))

section Finiteness

variable {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
  {e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)}

omit [IsGalois ℚ L] in

private theorem finite_setOf_ratOf_eq (ℓ : ℕ) :
    {u : HeightOneSpectrum (𝓞 (↥(fixFld (sylowH e)))) | ratOf u = ℓ}.Finite := by
  by_cases hℓ : ℓ.Prime
  · haveI : Fact ℓ.Prime := ⟨hℓ⟩
    apply Set.Finite.of_finite_image
      (f := fun u : HeightOneSpectrum (𝓞 (↥(fixFld (sylowH e)))) => u.asIdeal)
      (hi := fun x _ y _ h => IsDedekindDomain.HeightOneSpectrum.ext h)
    apply Set.Finite.subset (IsDedekindDomain.primesOver_finite (ratPrimeIdeal ℓ) _)
    rintro I ⟨u, hu, rfl⟩
    refine ⟨u.isPrime, ⟨?_⟩⟩
    rw [asIdeal_under_int u, hu]
  · convert Set.finite_empty
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun h => hℓ (h ▸ ratOf_prime u)

omit [IsGalois ℚ L] in

private theorem finite_setOf_ratOf_mem (T : Finset ℕ) :
    {u : HeightOneSpectrum (𝓞 (↥(fixFld (sylowH e)))) | ratOf u ∈ T}.Finite := by
  have hsub : {u : HeightOneSpectrum (𝓞 (↥(fixFld (sylowH e)))) | ratOf u ∈ T}
      ⊆ ⋃ ℓ ∈ T, {u | ratOf u = ℓ} := fun u hu => by
    simp only [Set.mem_iUnion]
    exact ⟨ratOf u, hu, rfl⟩
  exact Set.Finite.subset
    (Set.Finite.biUnion T.finite_toSet (fun ℓ _ => finite_setOf_ratOf_eq ℓ)) hsub

end Finiteness
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P4"

end LanglandsTunnell.P4
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P4"
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P4"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P4"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_sylowH sylowH Lift48.Mat DetDictionaryRow bcWeight bcWeight_apply chiNegThreeWeight IsRelDegree"
namespace QuatHOrder
p2m_open "LanglandsTunnell"

open NumberField Matrix FLT.ExplicitLift
p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P0 LanglandsTunnell.Lift48"

private def P16det1 : List Mat := P16.filter fun M => det2 M = 1

private theorem length_P16det1 : P16det1.length = 8 := by decide

private theorem nodup_P16det1 : P16det1.Nodup := nodup_P16.filter _

private theorem natCard_P16det1 : Nat.card {M : Mat // M ∈ P16det1} = 8 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight
        (fun M => (List.mem_toFinset (l := P16det1) (a := M)).symm)),
    Nat.card_eq_finsetCard, List.toFinset_card_of_nodup nodup_P16det1, length_P16det1]

private theorem mem_P16det1_iff (M : Mat) : M ∈ P16det1 ↔ M ∈ P16 ∧ det2 M = 1 := by
  simp only [P16det1, List.mem_filter, decide_eq_true_eq]

private theorem red_neg_one_ne_one : red (-1 : ℤ√(-2)) ≠ (1 : ZMod 3) := by
  rw [map_neg, map_one]; decide

section Card

variable {L : Type} [Field L] [NumberField L]

private theorem esymm_redUnit_mem_detKer (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    {M : Mat} (hM : M ∈ P16) (hdet : det2 M = 1) :
    e.symm (redUnit ⟨M, hM⟩) ∈ detKer e := by
  rw [mem_detKer_iff, MulEquiv.apply_symm_apply, coe_redUnit,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← det2_eq_det, hdet, map_one]

private noncomputable def toQuatH (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (M : {M : Mat // M ∈ P16det1}) : quatH e :=
  let hPd := (mem_P16det1_iff M.1).1 M.2
  ⟨e.symm (redUnit ⟨M.1, hPd.1⟩),
    Subgroup.mem_inf.2 ⟨(toSylowH e ⟨M.1, hPd.1⟩).2, esymm_redUnit_mem_detKer e hPd.1 hPd.2⟩⟩

private theorem val_toQuatH (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (M : {M : Mat // M ∈ P16det1}) :
    (toQuatH e M : L ≃ₐ[ℚ] L) = e.symm (redUnit ⟨M.1, ((mem_P16det1_iff M.1).1 M.2).1⟩) := rfl

private theorem toQuatH_bijective (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    Function.Bijective (toQuatH e) := by
  constructor
  ·

    rintro ⟨M, hM⟩ ⟨N, hN⟩ h
    have hP := (mem_P16det1_iff M).1 hM
    have hQ := (mem_P16det1_iff N).1 hN

    have hval : (toQuatH e ⟨M, hM⟩ : L ≃ₐ[ℚ] L) = (toQuatH e ⟨N, hN⟩ : L ≃ₐ[ℚ] L) :=
      Subtype.ext_iff.mp h

    rw [val_toQuatH, val_toQuatH] at hval

    have hred : redUnit ⟨M, hP.1⟩ = redUnit ⟨N, hQ.1⟩ := e.symm.injective hval

    have hinj : (⟨M, hP.1⟩ : {M : Mat // M ∈ P16}) = ⟨N, hQ.1⟩ :=
      (toSylowH_bijective e).1 (Subtype.ext (congrArg e.symm hred))

    have hMN : M = N := congrArg (Subtype.val (p := fun x => x ∈ P16)) hinj
    exact Subtype.ext hMN
  ·
    rintro ⟨γ, hγ⟩
    obtain ⟨hγs, hγd⟩ := Subgroup.mem_inf.1 hγ
    obtain ⟨⟨M, hM⟩, hMγ⟩ := (toSylowH_bijective e).2 ⟨γ, hγs⟩
    have hval : e.symm (redUnit ⟨M, hM⟩) = γ := congrArg Subtype.val hMγ

    have hdet_eγ : ((e γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
        Matrix (Fin 2) (Fin 2) (ZMod 3)).det = red (det2 M) := by
      rw [← hval, MulEquiv.apply_symm_apply, coe_redUnit,
        ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← det2_eq_det]
    have hred : red (det2 M) = 1 := hdet_eγ ▸ (mem_detKer_iff e γ).1 hγd
    have hdet2 : det2 M = 1 := by
      rcases P16_det2 M hM with h1 | h1
      · exact h1
      · exact absurd (h1 ▸ hred) red_neg_one_ne_one
    exact ⟨⟨M, (mem_P16det1_iff M).2 ⟨hM, hdet2⟩⟩, Subtype.ext hval⟩

private theorem natCard_quatH (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    Nat.card (quatH e) = 8 := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (toQuatH_bijective e)), natCard_P16det1]

end Card
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P4"

section Finrank

variable {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]

private theorem finrank_fixFld_quatH
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    Module.finrank ℚ ↥(fixFld (quatH e)) = 6 := by
  have htop : Module.finrank ↥(fixFld (quatH e)) L = Nat.card ↥(quatH e) :=
    IntermediateField.finrank_fixedField_eq_card (quatH e)
  have htower : Module.finrank ℚ ↥(fixFld (quatH e)) *
      Module.finrank ↥(fixFld (quatH e)) L = Module.finrank ℚ L :=
    Module.finrank_mul_finrank ℚ ↥(fixFld (quatH e)) L
  have hgal : Nat.card (L ≃ₐ[ℚ] L) = Module.finrank ℚ L :=
    IsGalois.card_aut_eq_finrank ℚ L
  rw [htop, natCard_quatH, ← hgal, natCard_gal e] at htower
  omega

set_option synthInstance.maxHeartbeats 320000 in

private theorem finrank_fixFld_sylowH_fixFld_quatH
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    Module.finrank ↥(fixFld (sylowH e)) ↥(fixFld (quatH e)) = 2 := by
  have htower : Module.finrank ℚ ↥(fixFld (sylowH e)) *
      Module.finrank ↥(fixFld (sylowH e)) ↥(fixFld (quatH e))
      = Module.finrank ℚ ↥(fixFld (quatH e)) :=
    Module.finrank_mul_finrank ℚ ↥(fixFld (sylowH e)) ↥(fixFld (quatH e))
  rw [finrank_fixFld_quatH e, LanglandsTunnell.P5.finrank_fixFld_sylowH e] at htower
  omega

end Finrank
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P4"

end LanglandsTunnell.QuatHOrder
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P4"
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P4"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_sylowH sylowH Lift48.Mat DetDictionaryRow bcWeight bcWeight_apply chiNegThreeWeight IsRelDegree"
namespace BcWeightCharacter
p2m_open "LanglandsTunnell"

p2m_open "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P0 LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P4 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P5"
p2m_open "FrobeniusDensity Ideal NumberField.Ideal"

private theorem bcWeight_mem_pmOne_of_under_ne_three
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (𝔓 : HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e))))
    (h3 : ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)) (𝔓.under (𝓞 ℚ)) : ℕ) ≠ 3) :
    LanglandsTunnell.bcWeight ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e))
      (fun v => AutomorphicForm.iotaZsqrtdNegTwo (LanglandsTunnell.chiNegThreeWeight v)) 𝔓 = 1 ∨
    LanglandsTunnell.bcWeight ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e))
      (fun v => AutomorphicForm.iotaZsqrtdNegTwo (LanglandsTunnell.chiNegThreeWeight v)) 𝔓 = -1 := by

  rw [LanglandsTunnell.bcWeight_apply]

  set v := 𝔓.under (𝓞 ℚ) with hv
  set p := ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)) v : ℕ) with hpdef
  have hp : p.Prime := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v).2

  have hbase : AutomorphicForm.iotaZsqrtdNegTwo (LanglandsTunnell.chiNegThreeWeight v)
      = ((EisensteinWeightOne.chiNegThree p : ℤ) : ℂ) := by
    unfold LanglandsTunnell.chiNegThreeWeight
    rw [← hpdef]

    exact_mod_cast map_intCast AutomorphicForm.iotaZsqrtdNegTwo
      (EisensteinWeightOne.chiNegThree p)
  rw [hbase]

  set f := v.asIdeal.inertiaDeg' 𝔓.asIdeal

  have hmod : p % 3 ≠ 0 := by
    intro h0
    have hdvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
    exact h3 (((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hdvd).symm)

  have hlt : p % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases h : (p % 3)
  · exact absurd rfl hmod
  ·
    left
    have hχ : EisensteinWeightOne.chiNegThree p = 1 := by
      unfold EisensteinWeightOne.chiNegThree; rw [if_pos h]
    rw [hχ, Int.cast_one, one_pow]
  ·
    have hχ : EisensteinWeightOne.chiNegThree p = -1 := by
      unfold EisensteinWeightOne.chiNegThree
      rw [if_neg (by omega : p % 3 ≠ 1), if_pos h]
    rw [hχ, Int.cast_neg, Int.cast_one]

    rcases Nat.even_or_odd f with he | ho
    · left; exact he.neg_one_pow
    · right; exact ho.neg_one_pow

private theorem bcWeight_sq_eq_one_of_under_ne_three
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (𝔓 : HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e))))
    (h3 : ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)) (𝔓.under (𝓞 ℚ)) : ℕ) ≠ 3) :
    LanglandsTunnell.bcWeight ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e))
      (fun v => AutomorphicForm.iotaZsqrtdNegTwo (LanglandsTunnell.chiNegThreeWeight v)) 𝔓 ^ 2
      = 1 := by
  rcases bcWeight_mem_pmOne_of_under_ne_three e 𝔓 h3 with h | h <;> rw [h] <;> ring

section SplittingCriterion

variable {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
  (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))

private theorem chiNegThree_pow_eq_one_iff_zmod {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (f : ℕ) :
    (EisensteinWeightOne.chiNegThree p) ^ f = 1 ↔ (p : ZMod 3) ^ f = 1 := by
  have hmod : p % 3 = 1 ∨ p % 3 = 2 := by
    have h3 : ¬ 3 ∣ p := fun h => hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h).symm
    omega

  have hred : ((EisensteinWeightOne.chiNegThree p : ℤ) : ZMod 3) = (p : ZMod 3) :=
    intCast_chiNegThree p
  rcases hmod with h | h
  ·
    have hχ : EisensteinWeightOne.chiNegThree p = 1 := by
      unfold EisensteinWeightOne.chiNegThree; rw [if_pos h]
    rw [hχ, Int.cast_one] at hred
    simp [hχ, ← hred]
  ·
    have hχ : EisensteinWeightOne.chiNegThree p = -1 := by
      unfold EisensteinWeightOne.chiNegThree
      rw [if_neg (by omega : p % 3 ≠ 1), if_pos h]
    rw [hχ, Int.cast_neg, Int.cast_one] at hred
    rw [hχ, ← hred]
    constructor
    · intro hf; exact_mod_cast congrArg (fun z : ℤ => (z : ZMod 3)) hf
    ·
      intro hf
      rcases Nat.even_or_odd f with he | ho
      · exact he.neg_one_pow
      · rw [ho.neg_one_pow] at hf ⊢
        exact absurd hf (by decide)

private theorem iota_chiNegThree_pow_eq_one_iff_zmod {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)) v : ℕ) = p) (f : ℕ) :
    AutomorphicForm.iotaZsqrtdNegTwo (LanglandsTunnell.chiNegThreeWeight v) ^ f = 1
      ↔ (p : ZMod 3) ^ f = 1 := by

  have hbase : AutomorphicForm.iotaZsqrtdNegTwo (LanglandsTunnell.chiNegThreeWeight v)
      = ((EisensteinWeightOne.chiNegThree p : ℤ) : ℂ) := by
    unfold LanglandsTunnell.chiNegThreeWeight
    rw [hv]
    exact_mod_cast map_intCast AutomorphicForm.iotaZsqrtdNegTwo
      (EisensteinWeightOne.chiNegThree p)
  rw [hbase, ← Int.cast_pow, ← Int.cast_one, Int.cast_inj,
    chiNegThree_pow_eq_one_iff_zmod hp hp3]

private theorem relDeg_quatH_eq_relDeg_sylowH_iff (σ : L ≃ₐ[ℚ] L) :
    relDeg (quatH e) σ = relDeg (sylowH e) σ
      ↔ ((e σ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
          Matrix (Fin 2) (Fin 2) (ZMod 3)).det ^ relDeg (sylowH e) σ = 1 := by
  set f := relDeg (sylowH e) σ with hf
  have hfpos : 0 < f := relDeg_pos (sylowH e) σ
  have hfsylow : σ ^ f ∈ sylowH e := (isRelDegree_relDeg (sylowH e) σ).2.1
  have hdvd : f ∣ relDeg (quatH e) σ := relDeg_dvd_relDeg (quatH_le_sylowH e) σ
  have hquat : (quatH e : Subgroup (L ≃ₐ[ℚ] L)) = sylowH e ⊓ detKer e := rfl
  constructor
  · intro heq
    have hmem : σ ^ f ∈ quatH e := heq ▸ (isRelDegree_relDeg (quatH e) σ).2.1
    rw [hquat, Subgroup.mem_inf] at hmem
    rw [← Matrix.det_pow, ← Units.val_pow_eq_pow_val, ← map_pow]
    exact (mem_detKer_iff e _).1 hmem.2
  · intro hdet
    have hmem : σ ^ f ∈ quatH e := by
      rw [hquat, Subgroup.mem_inf]
      refine ⟨hfsylow, (mem_detKer_iff e _).2 ?_⟩
      rw [map_pow, Units.val_pow_eq_pow_val, Matrix.det_pow]
      exact hdet
    exact Nat.dvd_antisymm (relDeg_dvd_of_pow_mem (quatH e) σ hmem) hdvd

private theorem inertiaDeg_quatH_under_eq_one_iff
    (hdet : DetDictionaryRow e)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (ratPrimeIdeal ℓ)] [Finite (𝓞 L ⧸ Q)]
    (hI : Q.inertia (L ≃ₐ[ℚ] L) = ⊥)
    (𝔓 : HeightOneSpectrum (𝓞 ↥(fixFld (sylowH e))))
    (h𝔓 : 𝔓.asIdeal = Q.under (𝓞 ↥(fixFld (sylowH e)))) :
    𝔓.asIdeal.inertiaDeg' (placeUnderH (quatH e) hℓ Q).asIdeal = 1
      ↔ (ℓ : ZMod 3) ^ (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal = 1 := by

  have hf𝔓 := inertiaDeg_eq_relDeg (sylowH e) hℓ Q hI 𝔓 h𝔓

  set 𝔔 := placeUnderH (quatH e) hℓ Q with h𝔔
  have h𝔔a : 𝔔.asIdeal = Q.under (𝓞 ↥(fixFld (quatH e))) := placeUnderH_asIdeal _ hℓ Q
  have hf𝔔 := inertiaDeg_eq_relDeg (quatH e) hℓ Q hI 𝔔 h𝔔a

  have h𝔔𝔓 : 𝔔.under (𝓞 ↥(fixFld (sylowH e))) = 𝔓 := by
    apply HeightOneSpectrum.ext
    rw [HeightOneSpectrum.under_asIdeal, h𝔔a, h𝔓]
    exact Ideal.under_under Q

  have hmul := inertiaDeg_under_mul ℚ (↥(fixFld (sylowH e))) (↥(fixFld (quatH e))) 𝔔
  rw [h𝔔𝔓] at hmul

  have h𝔔ℚ : 𝔔.under (𝓞 ℚ) = 𝔓.under (𝓞 ℚ) := by
    rw [← h𝔔𝔓]
    exact under_under ℚ (↥(fixFld (sylowH e))) (↥(fixFld (quatH e))) 𝔔
  rw [h𝔔ℚ] at hmul hf𝔔
  rw [hf𝔔, hf𝔓] at hmul

  have hpos := relDeg_pos (sylowH e) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q)
  constructor
  · intro h1
    rw [h1, mul_one] at hmul
    rw [hf𝔓, ← hdet ℓ hℓ hℓ3 Q ‹_› ‹_› ‹_› hI]
    exact (relDeg_quatH_eq_relDeg_sylowH_iff e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q)).1 hmul
  · intro hdetpow
    have heq : relDeg (quatH e) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q)
        = relDeg (sylowH e) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) := by
      refine (relDeg_quatH_eq_relDeg_sylowH_iff e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q)).2 ?_
      rw [hdet ℓ hℓ hℓ3 Q ‹_› ‹_› ‹_› hI]
      rw [hf𝔓] at hdetpow
      exact hdetpow
    rw [heq] at hmul

    nth_rw 1 [← mul_one (relDeg (sylowH e) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q))] at hmul
    exact (Nat.eq_of_mul_eq_mul_left hpos hmul).symm

end SplittingCriterion
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P4"

private theorem bcWeight_eq_one_iff_exists_inertiaDeg_one
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (hdet : LanglandsTunnell.DetDictionaryRow e) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e)))),
      ∀ 𝔓 ∉ S,
        (LanglandsTunnell.bcWeight ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e))
          (fun v => AutomorphicForm.iotaZsqrtdNegTwo (LanglandsTunnell.chiNegThreeWeight v)) 𝔓 = 1
        ↔ ∃ 𝔔 : HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))),
            𝔔.under (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e))) = 𝔓 ∧
            𝔓.asIdeal.inertiaDeg' 𝔔.asIdeal = 1) := by
  classical
  refine ⟨(finite_setOf_ratOf_mem (e := e) (insert 3 (towerBadPrimes L))).toFinset,
    fun 𝔓 h𝔓S => ?_⟩
  have h𝔓S' : ratOf 𝔓 ∉ insert 3 (towerBadPrimes L) := fun h =>
    h𝔓S ((Set.Finite.mem_toFinset _).2 h)
  have hℓ3 : ratOf 𝔓 ≠ 3 := fun h => h𝔓S' (h ▸ Finset.mem_insert_self _ _)
  have hℓbad : ratOf 𝔓 ∉ towerBadPrimes L := fun h => h𝔓S' (Finset.mem_insert_of_mem h)
  have hℓ := ratOf_prime 𝔓
  haveI : Fact (ratOf 𝔓).Prime := ⟨hℓ⟩

  rw [LanglandsTunnell.bcWeight_apply]
  set f := (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal with hfdef

  rw [iota_chiNegThree_pow_eq_one_iff_zmod hℓ hℓ3 (𝔓.under (𝓞 ℚ)) rfl f]

  set Q₀ := primeOver (sylowH e) 𝔓
  haveI : Q₀.IsPrime := (primeOver_isMaximal (sylowH e) 𝔓).isPrime
  haveI : Q₀.LiesOver (ratPrimeIdeal (ratOf 𝔓)) :=
    primeOver_liesOver_ratPrimeIdeal 𝔓
  have hI₀ : Q₀.inertia (L ≃ₐ[ℚ] L) = ⊥ :=
    tower_inertia_eq_bot_of_notMem hℓ hℓbad Q₀
  have h𝔓Q₀ : 𝔓.asIdeal = Q₀.under (𝓞 ↥(fixFld (sylowH e))) :=
    (under_primeOver (sylowH e) 𝔓).symm
  set 𝔔₀ := placeUnderH (quatH e) hℓ Q₀ with h𝔔₀
  have h𝔔₀𝔓 : 𝔔₀.under (𝓞 ↥(fixFld (sylowH e))) = 𝔓 := by
    apply HeightOneSpectrum.ext
    rw [HeightOneSpectrum.under_asIdeal, placeUnderH_asIdeal, h𝔓Q₀]
    exact Ideal.under_under Q₀

  have hkey₀ := inertiaDeg_quatH_under_eq_one_iff e hdet hℓ hℓ3 Q₀ hI₀ 𝔓 h𝔓Q₀
  rw [← h𝔔₀, ← hfdef] at hkey₀
  constructor
  ·
    intro hℓf
    exact ⟨𝔔₀, h𝔔₀𝔓, hkey₀.2 hℓf⟩
  ·
    rintro ⟨𝔔, h𝔔𝔓, hf𝔔1⟩

    set Q' := primeOver (quatH e) 𝔔
    haveI : Q'.IsPrime := (primeOver_isMaximal (quatH e) 𝔔).isPrime

    have hQ'E₃ : Q'.under (𝓞 ↥(fixFld (sylowH e))) = 𝔓.asIdeal := by
      rw [← Ideal.under_under (A := 𝓞 ↥(fixFld (sylowH e))) (B := 𝓞 ↥(fixFld (quatH e)))
        (C := 𝓞 L), under_primeOver, ← h𝔔𝔓, HeightOneSpectrum.under_asIdeal]

    haveI : Q'.LiesOver (ratPrimeIdeal (ratOf 𝔓)) := ⟨by
      rw [← Ideal.under_under (A := ℤ) (B := 𝓞 ↥(fixFld (sylowH e))) (C := 𝓞 L), hQ'E₃]
      exact (asIdeal_under_int 𝔓).symm⟩
    have hI' : Q'.inertia (L ≃ₐ[ℚ] L) = ⊥ :=
      tower_inertia_eq_bot_of_notMem hℓ hℓbad Q'

    have h𝔔' : placeUnderH (quatH e) hℓ Q' = 𝔔 := by
      apply HeightOneSpectrum.ext
      rw [placeUnderH_asIdeal, under_primeOver]

    have hkey' := inertiaDeg_quatH_under_eq_one_iff e hdet hℓ hℓ3 Q' hI' 𝔓 hQ'E₃.symm
    rw [h𝔔', ← hfdef] at hkey'
    exact hkey'.1 hf𝔔1

private theorem finite_under_eq_three
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    {𝔓 : HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e))) |
      ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)) (𝔓.under (𝓞 ℚ)) : ℕ) = 3}.Finite :=
  finite_setOf_ratOf_eq (e := e) 3

private theorem bcWeight_sq_and_eq_one_iff_exists_inertiaDeg_one
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (hdet : LanglandsTunnell.DetDictionaryRow e) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e)))),
      ∀ 𝔓 ∉ S,
        LanglandsTunnell.bcWeight ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e))
          (fun v => AutomorphicForm.iotaZsqrtdNegTwo (LanglandsTunnell.chiNegThreeWeight v)) 𝔓 ^ 2
          = 1 ∧
        (LanglandsTunnell.bcWeight ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e))
          (fun v => AutomorphicForm.iotaZsqrtdNegTwo (LanglandsTunnell.chiNegThreeWeight v)) 𝔓 = 1
        ↔ ∃ 𝔔 : HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))),
            𝔔.under (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e))) = 𝔓 ∧
            𝔓.asIdeal.inertiaDeg' 𝔔.asIdeal = 1) := by
  classical
  obtain ⟨S₁, hS₁⟩ := bcWeight_eq_one_iff_exists_inertiaDeg_one e hdet
  refine ⟨S₁ ∪ (finite_under_eq_three e).toFinset, fun 𝔓 h𝔓 => ?_⟩
  rw [Finset.mem_union, not_or] at h𝔓
  obtain ⟨h𝔓₁, h𝔓₃⟩ := h𝔓
  have h3 : ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)) (𝔓.under (𝓞 ℚ)) : ℕ) ≠ 3 := by
    intro h; exact h𝔓₃ ((finite_under_eq_three e).mem_toFinset.2 h)
  exact ⟨bcWeight_sq_eq_one_of_under_ne_three e 𝔓 h3, hS₁ 𝔓 h𝔓₁⟩

end LanglandsTunnell.BcWeightCharacter
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P4"
p2m_reactivate "P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell.P4"

open _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.LanglandsTunnell IsDedekindDomain NumberField MeasureTheory Matrix in
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox in
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering in
open NumberField.SiegelVolume in
theorem solution
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (hdet : DetDictionaryRow e)
    (c₃ u₃ d₃₁ d₃₂ : ℝ) (T₃ : Finset (AdelicGL2 (𝓞 ↥(fixFld (sylowH e))) ↥(fixFld (sylowH e))))
    (c₆ u₆ d₆₁ d₆₂ : ℝ) (T₆ : Finset (AdelicGL2 (𝓞 ↥(fixFld (quatH e))) ↥(fixFld (quatH e))))
    (Φc Φc' : HeckeEigensystem ↥(fixFld (sylowH e)) ℂ) (Φ₆ : HeckeEigensystem ↥(fixFld (quatH e)) ℂ)
    (hΦc : IsArithGenuineCuspRealizable ↥(fixFld (sylowH e))
      (productionPinsOf ↥(fixFld (sylowH e))
        (⋃ x ∈ T₃, (· * x) '' centreCutSiegelSet ↥(fixFld (sylowH e)) c₃ u₃ d₃₁ d₃₂)
        (fun N => levelOne (𝓞 ↥(fixFld (sylowH e))) ↥(fixFld (sylowH e)) N ⊓
          finiteAdelicGL2Subgroup ↥(fixFld (sylowH e)))
        (fun v => heckeGen (𝓞 ↥(fixFld (sylowH e))) ↥(fixFld (sylowH e)) v) (adelicBox ↥(fixFld (sylowH e)))) Φc)
    (hΦc' : IsArithGenuineCuspRealizable ↥(fixFld (sylowH e))
      (productionPinsOf ↥(fixFld (sylowH e))
        (⋃ x ∈ T₃, (· * x) '' centreCutSiegelSet ↥(fixFld (sylowH e)) c₃ u₃ d₃₁ d₃₂)
        (fun N => levelOne (𝓞 ↥(fixFld (sylowH e))) ↥(fixFld (sylowH e)) N ⊓
          finiteAdelicGL2Subgroup ↥(fixFld (sylowH e)))
        (fun v => heckeGen (𝓞 ↥(fixFld (sylowH e))) ↥(fixFld (sylowH e)) v) (adelicBox ↥(fixFld (sylowH e)))) Φc')
    (hc₆ : IsArithGenuineCuspRealizable ↥(fixFld (quatH e))
      (productionPinsOf ↥(fixFld (quatH e))
        (⋃ x ∈ T₆, (· * x) '' centreCutSiegelSet ↥(fixFld (quatH e)) c₆ u₆ d₆₁ d₆₂)
        (fun N => levelOne (𝓞 ↥(fixFld (quatH e))) ↥(fixFld (quatH e)) N ⊓
          finiteAdelicGL2Subgroup ↥(fixFld (quatH e)))
        (fun v => heckeGen (𝓞 ↥(fixFld (quatH e))) ↥(fixFld (quatH e)) v) (adelicBox ↥(fixFld (quatH e)))) Φ₆)
    (hd₃ : d₃₁ < d₃₂)
    (hcov₃ : CoversModCentre ↥(fixFld (sylowH e))
      (⋃ x ∈ T₃, (· * x) '' centreCutSiegelSet ↥(fixFld (sylowH e)) c₃ u₃ d₃₁ d₃₂))
    (hd₆ : d₆₁ < d₆₂)
    (hcov₆ : CoversModCentre ↥(fixFld (quatH e))
      (⋃ x ∈ T₆, (· * x) '' centreCutSiegelSet ↥(fixFld (quatH e)) c₆ u₆ d₆₁ d₆₂))
    (hBC : (formalBaseChange ↥(fixFld (sylowH e)) ↥(fixFld (quatH e)) Φc).AgreesAwayFromFinite Φ₆)
    (hBC' : (formalBaseChange ↥(fixFld (sylowH e)) ↥(fixFld (quatH e)) Φc').AgreesAwayFromFinite Φ₆) :
    Φc'.AgreesAwayFromFinite Φc ∨
      Φc'.AgreesAwayFromFinite
        (Φc.twist (bcWeight ℚ ↥(fixFld (sylowH e)) (fun v => iotaZsqrtdNegTwo (chiNegThreeWeight v)))) := by
  exact agreesAwayFromFinite_or_twist_of_formalBaseChange_agreesAwayFromFinite_of_finrank_eq_two_of_coversModCentre
    ↥(fixFld (sylowH e)) ↥(fixFld (quatH e))
    (LanglandsTunnell.QuatHOrder.finrank_fixFld_sylowH_fixFld_quatH e)
    (bcWeight ℚ ↥(fixFld (sylowH e)) (fun v => iotaZsqrtdNegTwo (chiNegThreeWeight v)))
    (LanglandsTunnell.BcWeightCharacter.bcWeight_sq_and_eq_one_iff_exists_inertiaDeg_one e hdet)
    c₃ u₃ d₃₁ d₃₂ T₃ c₆ u₆ d₆₁ d₆₂ T₆ hd₃ hcov₃ hd₆ hcov₆ Φc Φc' Φ₆ hΦc hΦc' hc₆ hBC hBC'

end
end S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH
end P2MW
export P2MW.S_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH (solution)
