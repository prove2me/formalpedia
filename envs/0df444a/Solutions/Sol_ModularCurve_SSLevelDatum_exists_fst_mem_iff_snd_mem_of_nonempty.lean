-- Prove2me | solution 1 for ModularCurve.SSLevelDatum.exists_fst_mem_iff_snd_mem_of_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/8cf5fa58-b189-5592-a971-94c3f7567807

import Mathlib
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.Def_WeierstrassCurve_VeluPointMap2
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_ModularCurve_moduliPlace_orbitClauses
import Theorems.Thm_ModularCurve_moduliPlace_restrictAlong_inclusion
import Theorems.Thm_ModularCurve_moduliPlace_restrictAlong_qExpand_fullKernelQuotient
import Theorems.Thm_ModularCurve_moduliPlace_restrictAlong_qExpand_veluQuotient
import Theorems.Thm_ModularCurve_isModuliPlaceOf_nonempty
import Theorems.Thm_ModularCurve_eq_of_isModuliPlaceOf
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_degeneracyPair_finiteSeparableDeg_ssPlaces_preserved_reflected
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_WeierstrassCurve_j_mem_ssJSet_of_forall_smul_eq_zero
import Theorems.Thm_WeierstrassCurve_fullKernelQuotient_discriminant_ne_zero
import Theorems.Thm_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_veluPointHom_mem_rationalHomSet_and_exists_mem_rationalHomSet_comp_eq
import Theorems.Thm_WeierstrassCurve_exists_coe_eq_veluPointMap2_and_mem_rationalHomSet_and_comp_eq_two_smul
import Theorems.Thm_WeierstrassCurve_coordsOrZero_veluPointMap2
import Theorems.Thm_WeierstrassCurve_exists_variableChange_heq_vcInvFun_iff_exists_dualPair
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero
import Theorems.Thm_WeierstrassCurve_exists_nsmul_eq_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_exists_supersingular_endomorphism_natCard_ker_eq_odd_pow_stabilizing_cyclic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_SSLevelDatum_exists_fst_mem_iff_snd_mem_of_nonempty
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 CyclotomicUniv.instCharZeroR₀ CyclotomicUniv.instIsDomain CyclotomicUniv.instIsDomainR₀ CyclotomicUniv.instCharZero ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule"
p2m_attr_erase "instance" "KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois IsDedekindDomain.HeightOneSpectrum.instAlgebraRatAdicCompletion IsDedekindDomain.HeightOneSpectrum.instModuleRatAdicCompletion TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm CyclotomicUniv.lift₀_ζ₀ CyclotomicUniv.lift_algebraMap CyclotomicUniv.val_ζUnit CyclotomicUniv.lift_ζ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg"
p2m_attr_erase "simp" "KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm WeierstrassCurve.pointAddEquivOfEq_refl"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero Submodule.finiteAdeleEvalAt_tmul Submodule.val_finiteIdeleDiagonal_apply QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq FrobeniusEndo.linePencil_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.frobPoint_zero WeierstrassCurve.frobCardHom_apply ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_SSLevelDatum_exists_fst_mem_iff_snd_mem_of_nonempty.ModularCurve WeierstrassCurve~card WeierstrassCurve.Affine"
open scoped IntermediateField

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "levelAlphaC coe_levelAlphaC levelBetaC coe_levelBetaC SSLevelDatum algebraMap_laurentSeries_apply_eq_single mem_restrictAlong_iff jqModC jqNModC modularFunctionFieldC qExpand qExpand_single isSupersingularPlace_iff ssPlaces mem_ssPlaces_iff jGeomGen jNGeomGen jGeomGen_sub_algebraMap_ne_zero evalModularPair_jGeomGen_eq_zero ssJSet ModuliPoint IsModuliPlaceOf moduliPlace modularFunctionFieldFullC jqModC_mem_full full_degeneracyC_le full_degeneracyC_map_le moduliPlace_orbitClauses moduliPlace_restrictAlong_inclusion moduliPlace_restrictAlong_qExpand_fullKernelQuotient moduliPlace_restrictAlong_qExpand_veluQuotient isModuliPlaceOf_nonempty eq_of_isModuliPlaceOf modularFunctionFieldC_eq_modularFunctionFieldFullC degeneracyPair_finiteSeparableDeg_ssPlaces_preserved_reflected place_deg_eq_one_of_isAlgClosed nonempty_modularPolynomialData"
namespace OddWalkW2
p2m_open "ModularCurve"

section PlaceCalculus

variable {K F F' G G' : Type*} [Field K] [Field F] [Field F'] [Field G] [Field G']
  [Algebra K F] [Algebra K F'] [Algebra K G] [Algebra K G']

theorem mem_restrictAlong_iff (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F')
    (x : F) : x ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ x ∈ w.toValuationSubring :=
  Iff.rfl

theorem algebraMap_comm (e : F ≃ₐ[K] G) (a : K) :
    e.toRingEquiv (algebraMap K F a) = algebraMap K G a :=
  e.commutes a

abbrev transport (e : F ≃ₐ[K] G) : Place K F → Place K G :=
  Place.congrRingEquiv e.toRingEquiv (algebraMap_comm e)

theorem mem_transport_iff (e : F ≃ₐ[K] G) (v : Place K F) (y : G) :
    y ∈ (transport e v).toValuationSubring ↔ e.symm y ∈ v.toValuationSubring :=
  Iff.rfl

theorem transport_injective (e : F ≃ₐ[K] G) : Function.Injective (transport e) :=
  (Place.congrEquiv e.toRingEquiv (algebraMap_comm e)).injective

theorem ord_transport (e : F ≃ₐ[K] G) (v : Place K F) (f : F) :
    (transport e v).ord (e f) = v.ord f :=
  Place.ord_congrRingEquiv e.toRingEquiv (algebraMap_comm e) v f

theorem restrictAlong_transport (e₁ : F ≃ₐ[K] G) (e₂ : F' ≃ₐ[K] G')
    (φ : G →ₐ[K] G') (φ' : F →ₐ[K] F') (hcomm : ∀ x, φ (e₁ x) = e₂ (φ' x))
    (hφ : φ.toRingHom.IsIntegral) (hφ' : φ'.toRingHom.IsIntegral) (v : Place K F') :
    (transport e₂ v).restrictAlong φ hφ = transport e₁ (v.restrictAlong φ' hφ') := by
  ext1
  refine SetLike.ext fun y => ?_
  rw [mem_restrictAlong_iff, mem_transport_iff, mem_transport_iff, mem_restrictAlong_iff]
  have hy : φ y = e₂ (φ' (e₁.symm y)) := by
    rw [← hcomm, AlgEquiv.apply_symm_apply]
  rw [hy, AlgEquiv.symm_apply_apply]

theorem isIntegral_of_comm (e₁ : F ≃ₐ[K] G) (e₂ : F' ≃ₐ[K] G')
    (φ : G →ₐ[K] G') (φ' : F →ₐ[K] F') (hcomm : ∀ x, φ (e₁ x) = e₂ (φ' x))
    (hφ : φ.toRingHom.IsIntegral) : φ'.toRingHom.IsIntegral := by
  have h : φ'.toRingHom =
      (e₂.symm : G' →+* F').comp (φ.toRingHom.comp (e₁ : F →+* G)) := by
    ext x
    show φ' x = e₂.symm (φ (e₁ x))
    rw [hcomm, AlgEquiv.symm_apply_apply]
  rw [h]
  refine RingHom.IsIntegral.trans _ _ (RingHom.IsIntegral.trans _ _ ?_ hφ) ?_
  · exact RingHom.isIntegral_of_surjective _ e₁.surjective
  · exact RingHom.isIntegral_of_surjective _ e₂.symm.surjective

end PlaceCalculus

section Tower

variable (K : Type*) [Field K] (M s : ℕ) [NeZero M] [NeZero s]

def jF (N : ℕ) [NeZero N] : modularFunctionFieldFullC K N := ⟨jqModC K, jqModC_mem_full K N⟩

@[scoped simp] theorem coe_jF (N : ℕ) [NeZero N] : ((jF K N : modularFunctionFieldFullC K N) :
    LaurentSeries K) = jqModC K := rfl

def inclMS : modularFunctionFieldFullC K M →ₐ[K] modularFunctionFieldFullC K (M * s) :=
  IntermediateField.inclusion (full_degeneracyC_le K (dvd_mul_right M s))

@[scoped simp] theorem coe_inclMS (x : modularFunctionFieldFullC K M) :
    ((inclMS K M s x : modularFunctionFieldFullC K (M * s)) : LaurentSeries K) = x :=
  IntermediateField.coe_inclusion _ x

def betaMSRingHom : modularFunctionFieldFullC K M →+* modularFunctionFieldFullC K (M * s) where
  toFun x := ⟨qExpand K s (x : LaurentSeries K), full_degeneracyC_map_le K M s ⟨x, x.2, rfl⟩⟩
  map_one' := Subtype.ext (map_one (qExpand K s))
  map_mul' _ _ := Subtype.ext (map_mul (qExpand K s) _ _)
  map_zero' := Subtype.ext (map_zero (qExpand K s))
  map_add' _ _ := Subtype.ext (map_add (qExpand K s) _ _)

def betaMS : modularFunctionFieldFullC K M →ₐ[K] modularFunctionFieldFullC K (M * s) :=
  { betaMSRingHom K M s with
    commutes' := fun a => Subtype.ext <| by
      show qExpand K s (algebraMap K (LaurentSeries K) a) = algebraMap K (LaurentSeries K) a
      rw [algebraMap_laurentSeries_apply_eq_single, qExpand_single, mul_zero] }

@[scoped simp] theorem coe_betaMS (x : modularFunctionFieldFullC K M) :
    ((betaMS K M s x : modularFunctionFieldFullC K (M * s)) : LaurentSeries K) =
      qExpand K s (x : LaurentSeries K) := rfl

theorem coe_equivOfEq {L : Type*} [Field L] [Algebra K L] {S T : IntermediateField K L}
    (h : S = T) (x : S) : ((IntermediateField.equivOfEq h x : T) : L) = x := rfl

variable {K}

theorem fieldC_eq (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) :
    modularFunctionFieldC K N = modularFunctionFieldFullC K N :=
  ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC K (ringChar K) N
    (fun h => hN ((ringChar.spec K N).mpr h))

def eC (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) :
    modularFunctionFieldFullC K N ≃ₐ[K] modularFunctionFieldC K N :=
  IntermediateField.equivOfEq (fieldC_eq N hN).symm

@[scoped simp] theorem coe_eC (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) (x : modularFunctionFieldFullC K N) :
    ((eC N hN x : modularFunctionFieldC K N) : LaurentSeries K) = x :=
  coe_equivOfEq K (fieldC_eq N hN).symm x

theorem eC_jF (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) : eC N hN (jF K N) = jGeomGen K N :=
  Subtype.ext (coe_eC N hN (jF K N))

theorem eC_jF_sub (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) (c : K) :
    eC N hN (jF K N - algebraMap K (modularFunctionFieldFullC K N) c) =
      jGeomGen K N - algebraMap K (modularFunctionFieldC K N) c := by
  rw [map_sub, AlgEquiv.commutes, eC_jF]

variable {M s} (hM : (M : K) ≠ 0) (hMs : ((M * s : ℕ) : K) ≠ 0)

theorem levelAlphaC_eC (hmem : jqNModC K M ∈ modularFunctionFieldC K (M * s)) (x : modularFunctionFieldFullC K M) :
    levelAlphaC K M s hmem (eC M hM x) = eC (M * s) hMs (inclMS K M s x) := by
  apply Subtype.ext
  rw [coe_levelAlphaC, coe_eC, coe_eC, coe_inclMS]

theorem levelBetaC_eC (hmem : jqNModC K s ∈ modularFunctionFieldC K (M * s)) (x : modularFunctionFieldFullC K M) :
    levelBetaC K M s hmem (eC M hM x) = eC (M * s) hMs (betaMS K M s x) := by
  apply Subtype.ext
  rw [coe_levelBetaC, coe_eC, coe_eC, coe_betaMS]

end Tower

section Arith

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [CharP K p]

theorem natCast_ne_zero_of_not_dvd {n : ℕ} (hn : ¬ p ∣ n) : (n : K) ≠ 0 := fun h =>
  hn ((CharP.cast_eq_zero_iff K p n).mp h)

omit [CharP K p] in
theorem not_dvd_mul {M s : ℕ} (hs : s.Prime) (hpM : ¬ p ∣ M) (hsp : s ≠ p) : ¬ p ∣ M * s := by
  have hp : p.Prime := Fact.out
  intro h
  rcases hp.dvd_mul.mp h with h | h
  · exact hpM h
  · exact hsp ((Nat.prime_dvd_prime_iff_eq hp hs).mp h).symm

end Arith

section Clauses

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ] {M s : ℕ} [NeZero M] [NeZero s]

abbrev CycSub (E : WeierstrassCurve κ) (n : ℕ) : Type :=
  {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = n}

variable (hM : (M : κ) ≠ 0) (hMs : ((M * s : ℕ) : κ) ≠ 0)

def gPl (E : WeierstrassCurve κ) (C : AddSubgroup E.toAffine.Point) : Place κ (modularFunctionFieldC κ M) :=
  transport (eC M hM) (moduliPlace κ M E C)

def ePl (E : WeierstrassCurve κ) (D : AddSubgroup E.toAffine.Point) : Place κ (modularFunctionFieldC κ (M * s)) :=
  transport (eC (M * s) hMs) (moduliPlace κ (M * s) E D)

theorem hex_of (N : ℕ) [NeZero N] (hN : (N : κ) ≠ 0) : ∀ x : ModuliPoint N κ, ∃ v, IsModuliPlaceOf κ N x v :=
  fun x => ModularCurve.isModuliPlaceOf_nonempty κ N hN x

theorem huniq_of (N : ℕ) [NeZero N] (hN : (N : κ) ≠ 0) :
    ∀ (x : ModuliPoint N κ) (v v' : Place κ (modularFunctionFieldFullC κ N)),
      IsModuliPlaceOf κ N x v → IsModuliPlaceOf κ N x v' → v = v' :=
  fun x v v' hv hv' => ModularCurve.eq_of_isModuliPlaceOf κ N hN x v v' hv hv'

theorem g1 (E : WeierstrassCurve κ) [E.IsElliptic] (C : CycSub E M) :
    0 < (gPl hM E C.1).ord (jGeomGen κ M - algebraMap κ (modularFunctionFieldC κ M) E.j) := by
  rw [gPl, ← eC_jF_sub M hM, ord_transport]
  exact (ModularCurve.moduliPlace_orbitClauses κ M hM (huniq_of M hM)).1 E C

theorem g3 (E E' : WeierstrassCurve κ) [E.IsElliptic] [E'.IsElliptic] (C : CycSub E M) (C' : CycSub E' M) :
    gPl hM E C.1 = gPl hM E' C'.1 ↔ ∃ γ : VariableChange κ, γ • E = E' ∧
      ∀ T ∈ C.1, ∃ T' ∈ C'.1, HEq (Point.vcInvFun γ E.toAffine T) T' := by
  rw [gPl, gPl, (transport_injective (eC M hM)).eq_iff]
  exact (ModularCurve.moduliPlace_orbitClauses κ M hM (huniq_of M hM)).2.2.1 E E' C C'

theorem law_alpha (hmem : jqNModC κ M ∈ modularFunctionFieldC κ (M * s))
    (hα : (levelAlphaC κ M s hmem).toRingHom.IsIntegral) (E : WeierstrassCurve κ)
    (D : CycSub E (M * s)) (C : CycSub E M) (hDC : ∀ T ∈ D.1, s • T ∈ C.1) :
    (ePl hMs E D.1).restrictAlong (levelAlphaC κ M s hmem) hα = gPl hM E C.1 := by
  have hι : (inclMS κ M s).toRingHom.IsIntegral :=
    isIntegral_of_comm (eC M hM) (eC (M * s) hMs) (levelAlphaC κ M s hmem) (inclMS κ M s)
      (levelAlphaC_eC hM hMs hmem) hα
  rw [ePl, gPl, restrictAlong_transport (eC M hM) (eC (M * s) hMs) (levelAlphaC κ M s hmem) (inclMS κ M s)
    (levelAlphaC_eC hM hMs hmem) hα hι]
  congr 1
  have hq : M * s / M = s := Nat.mul_div_cancel_left s (Nat.pos_of_ne_zero (NeZero.ne M))
  have hDC' : ∀ T ∈ D.1, (M * s / M) • T ∈ C.1 := fun T hT => by
    rw [hq]
    exact hDC T hT
  exact ModularCurve.moduliPlace_restrictAlong_inclusion κ (M * s) M (dvd_mul_right M s)
    (hex_of (M * s) hMs) (huniq_of M hM) hι E D C hDC'

theorem law_beta_full (hmem : jqNModC κ s ∈ modularFunctionFieldC κ (M * s))
    (hβ : (levelBetaC κ M s hmem).toRingHom.IsIntegral) (E : WeierstrassCurve κ) [E.IsElliptic]
    (D : CycSub E (M * s)) (Q : E.toAffine.Point) (hQD : Q ∈ D.1) (hQ : addOrderOf Q = s)
    (hΔ : (E.fullKernelQuotient Q s).Δ ≠ 0)
    (φ : E.toAffine.Point →+ (E.fullKernelQuotient Q s).toAffine.Point)
    (hφker : φ.ker = AddSubgroup.zmultiples Q)
    (hφ : ∀ P : E.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
      (φ P).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (s - 1),
            ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (s - 1),
            ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2)))
    (C'' : CycSub (E.fullKernelQuotient Q s) M) (hDC'' : ∀ T ∈ D.1, φ T ∈ C''.1) :
    (ePl hMs E D.1).restrictAlong (levelBetaC κ M s hmem) hβ = gPl hM (E.fullKernelQuotient Q s) C''.1 := by
  have hb : (betaMS κ M s).toRingHom.IsIntegral :=
    isIntegral_of_comm (eC M hM) (eC (M * s) hMs) (levelBetaC κ M s hmem) (betaMS κ M s)
      (levelBetaC_eC hM hMs hmem) hβ
  rw [ePl, gPl, restrictAlong_transport (eC M hM) (eC (M * s) hMs) (levelBetaC κ M s hmem) (betaMS κ M s)
    (levelBetaC_eC hM hMs hmem) hβ hb]
  congr 1
  exact ModularCurve.moduliPlace_restrictAlong_qExpand_fullKernelQuotient κ M s hMs
    (huniq_of M hM) (hex_of (M * s) hMs)
    (betaMS κ M s) (fun f => rfl) hb E D.1 D.2 Q hQD hQ hΔ φ hφker hφ C''.1 C''.2 hDC''

theorem law_beta_velu (hmem : jqNModC κ s ∈ modularFunctionFieldC κ (M * s))
    (hβ : (levelBetaC κ M s hmem).toRingHom.IsIntegral) (E : WeierstrassCurve κ) [E.IsElliptic]
    (D : CycSub E (M * s)) (n : ℕ) (hn : s = 2 * n + 1) (Q : E.toAffine.Point) (hQD : Q ∈ D.1)
    (hQ : addOrderOf Q = 2 * n + 1)
    (hΔ : (E.veluQuotient (E.oddOrderSummingSet Q n)).Δ ≠ 0)
    (φ : E.toAffine.Point →+ (E.veluQuotient (E.oddOrderSummingSet Q n)).toAffine.Point)
    (hφker : φ.ker = AddSubgroup.zmultiples Q)
    (hφ : ∀ (x y : κ) (h : E.toAffine.Nonsingular x y),
      (.some x y h : E.toAffine.Point) ∉ AddSubgroup.zmultiples Q →
        ∃ h', φ (.some x y h) = .some (E.veluX (E.oddOrderSummingSet Q n) x)
          (E.veluY (E.oddOrderSummingSet Q n) x y) h')
    (C'' : CycSub (E.veluQuotient (E.oddOrderSummingSet Q n)) M) (hDC'' : ∀ T ∈ D.1, φ T ∈ C''.1) :
    (ePl hMs E D.1).restrictAlong (levelBetaC κ M s hmem) hβ =
      gPl hM (E.veluQuotient (E.oddOrderSummingSet Q n)) C''.1 := by
  have hb : (betaMS κ M s).toRingHom.IsIntegral :=
    isIntegral_of_comm (eC M hM) (eC (M * s) hMs) (levelBetaC κ M s hmem) (betaMS κ M s)
      (levelBetaC_eC hM hMs hmem) hβ
  rw [ePl, gPl, restrictAlong_transport (eC M hM) (eC (M * s) hMs) (levelBetaC κ M s hmem) (betaMS κ M s)
    (levelBetaC_eC hM hMs hmem) hβ hb]
  congr 1
  exact ModularCurve.moduliPlace_restrictAlong_qExpand_veluQuotient κ M s hMs
    (huniq_of M hM) (hex_of (M * s) hMs)
    (betaMS κ M s) (fun f => rfl) hb E D.1 D.2 n hn Q hQD hQ hΔ φ hφker hφ C''.1 C''.2 hDC''

end Clauses

section Isogeny

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]

theorem nsmul_id_mem_rationalHomSet (W : WeierstrassCurve κ) [W.IsElliptic] (n : ℕ) :
    (n • AddMonoidHom.id _ : (W.baseChange κ).toAffine.Point →+ (W.baseChange κ).toAffine.Point) ∈
      rationalHomSet κ W W := by
  induction n with
  | zero => rw [zero_nsmul]; exact zero_mem_rationalHomSet κ W W
  | succ n ih => rw [succ_nsmul]; exact add_mem_rationalHomSet κ W W ih (id_mem_rationalHomSet κ W)

theorem surjective_and_exists_dual_of_universal (E A : WeierstrassCurve κ) [E.IsElliptic] [A.IsElliptic]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ0 : (ℓ : κ) ≠ 0) (Q : E.toAffine.Point) (hQ : addOrderOf Q = ℓ)
    (φ : (E.baseChange κ).toAffine.Point →+ (A.baseChange κ).toAffine.Point) (hφ : φ ∈ rationalHomSet κ E A)
    (hker : φ.ker = AddSubgroup.zmultiples Q)
    (huniv : ∀ (V : WeierstrassCurve κ) [V.IsElliptic]
      (α : (E.baseChange κ).toAffine.Point →+ (V.baseChange κ).toAffine.Point),
        α ∈ rationalHomSet κ E V → α Q = 0 → ∃ β ∈ rationalHomSet κ A V, α = β.comp φ) :
    Function.Surjective φ ∧
      ∃ φ' ∈ rationalHomSet κ A E, φ'.comp φ = ℓ • AddMonoidHom.id _ ∧ φ.comp φ' = ℓ • AddMonoidHom.id _ := by
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hQ
    exact hℓ.one_lt.ne hQ
  have hℓQ : ℓ • Q = 0 := by rw [← hQ]; exact addOrderOf_nsmul_eq_zero Q
  have hφ0 : φ ≠ 0 := by
    intro h0
    obtain ⟨T₀, hT₀⟩ := exists_nsmul_eq_of_isAlgClosed E ℓ hℓ0 Q
    let T : (E.baseChange κ).toAffine.Point := T₀
    have hT : ℓ • T = Q := hT₀
    have hTker : T ∈ φ.ker := by rw [h0]; trivial
    rw [hker] at hTker
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hTker
    apply hQ0
    have hkQ : ℓ • (k • Q) = 0 := by rw [smul_comm, hℓQ, smul_zero]
    have hk' : (k • Q : (E.baseChange κ).toAffine.Point) = T := hk
    rw [← hT]
    show ℓ • T = 0
    rw [← hk']
    exact hkQ
  have hsurj : Function.Surjective φ := surjective_of_mem_rationalHomSet κ hφ hφ0
  have hℓQ' : (ℓ • AddMonoidHom.id (E.baseChange κ).toAffine.Point) Q = 0 := hℓQ
  obtain ⟨φ', hφ', hcomp⟩ := huniv E (ℓ • AddMonoidHom.id _) (nsmul_id_mem_rationalHomSet E ℓ) hℓQ'
  refine ⟨hsurj, φ', hφ', hcomp.symm, ?_⟩
  have L : ∀ R : (E.baseChange κ).toAffine.Point, φ' (φ R) = ℓ • R := fun R => (DFunLike.congr_fun hcomp R).symm
  ext P
  obtain ⟨R, rfl⟩ := hsurj P
  show φ (φ' (φ R)) = ℓ • φ R
  rw [L, map_nsmul]

theorem exists_inverse_of_injective_dualPair (A E : WeierstrassCurve κ) [A.IsElliptic] [E.IsElliptic]
    {d : ℕ} (hd : (d : κ) ≠ 0)
    (β : (A.baseChange κ).toAffine.Point →+ (E.baseChange κ).toAffine.Point) (hβ : β ∈ rationalHomSet κ A E)
    (β' : (E.baseChange κ).toAffine.Point →+ (A.baseChange κ).toAffine.Point) (hβ' : β' ∈ rationalHomSet κ E A)
    (h1 : β'.comp β = d • AddMonoidHom.id _) (h2 : β.comp β' = d • AddMonoidHom.id _)
    (hinj : ∀ R, β R = 0 → R = 0) :
    ∃ ε ∈ rationalHomSet κ E A, ε.comp β = AddMonoidHom.id _ ∧ β.comp ε = AddMonoidHom.id _ := by
  have L1 : ∀ R, β' (β R) = d • R := fun R => DFunLike.congr_fun h1 R
  have L2 : ∀ T, β (β' T) = d • T := fun T => DFunLike.congr_fun h2 T
  have hkill : ∀ T : (E.baseChange κ).toAffine.Point, (d : ℤ) • T = 0 → β' T = 0 := by
    intro T hT
    apply hinj
    rw [L2, ← natCast_zsmul, hT]
  obtain ⟨ε, hε, hεeq⟩ := exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero κ E A hd hβ' hkill
  have Lε : ∀ T, β' T = d • ε T := fun T => by rw [← natCast_zsmul]; exact hεeq T
  refine ⟨ε, hε, ?_, ?_⟩
  · ext R
    show ε (β R) = R
    obtain ⟨R₁, hR₁⟩ := exists_nsmul_eq_of_isAlgClosed A d hd R
    let R₀ : (A.baseChange κ).toAffine.Point := R₁
    have hR : d • R₀ = R := hR₁
    rw [← hR, map_nsmul, map_nsmul, ← Lε, L1]
  · ext T
    show β (ε T) = T
    obtain ⟨T₁, hT₁⟩ := exists_nsmul_eq_of_isAlgClosed E d hd T
    let T₀ : (E.baseChange κ).toAffine.Point := T₁
    have hT : d • T₀ = T := hT₁
    rw [← hT, map_nsmul, ← Lε, L2]

theorem exists_dual_of_ker_eq_zmultiples (E A E₀ : WeierstrassCurve κ) [E.IsElliptic] [A.IsElliptic] [E₀.IsElliptic]
    {s : ℕ} (hs0 : (s : κ) ≠ 0) (Q : E.toAffine.Point)
    (φ : (E.baseChange κ).toAffine.Point →+ (A.baseChange κ).toAffine.Point) (hφ : φ ∈ rationalHomSet κ E A)
    (hφker : φ.ker = AddSubgroup.zmultiples Q) (hφsurj : Function.Surjective φ)
    (φ' : (A.baseChange κ).toAffine.Point →+ (E.baseChange κ).toAffine.Point) (hφ' : φ' ∈ rationalHomSet κ A E)
    (hφ'φ : φ'.comp φ = s • AddMonoidHom.id _) (hφφ' : φ.comp φ' = s • AddMonoidHom.id _)
    (huniv : ∀ (V : WeierstrassCurve κ) [V.IsElliptic]
      (α : (E.baseChange κ).toAffine.Point →+ (V.baseChange κ).toAffine.Point),
        α ∈ rationalHomSet κ E V → α Q = 0 → ∃ β ∈ rationalHomSet κ A V, α = β.comp φ)
    (ψ : (E.baseChange κ).toAffine.Point →+ (E₀.baseChange κ).toAffine.Point) (hψ : ψ ∈ rationalHomSet κ E E₀)
    (ψ' : (E₀.baseChange κ).toAffine.Point →+ (E.baseChange κ).toAffine.Point) (hψ' : ψ' ∈ rationalHomSet κ E₀ E)
    (a : ℕ) (h1 : ψ'.comp ψ = s ^ a • AddMonoidHom.id _) (h2 : ψ.comp ψ' = s ^ a • AddMonoidHom.id _)
    (hker : ψ.ker = AddSubgroup.zmultiples Q) :
    ∃ ψ'' ∈ rationalHomSet κ E₀ E, ψ''.comp ψ = s • AddMonoidHom.id _ ∧ ψ.comp ψ'' = s • AddMonoidHom.id _ := by
  have hψQ : ψ Q = 0 := by
    rw [← AddMonoidHom.mem_ker, hker]; exact AddSubgroup.mem_zmultiples _
  obtain ⟨β, hβ, hψβ⟩ := huniv E₀ ψ hψ hψQ
  have Lψ : ∀ T, ψ T = β (φ T) := fun T => by rw [hψβ]; rfl
  have L1 : ∀ T, ψ' (ψ T) = s ^ a • T := fun T => DFunLike.congr_fun h1 T
  have L2 : ∀ T, ψ (ψ' T) = s ^ a • T := fun T => DFunLike.congr_fun h2 T
  have Lφ'φ : ∀ T, φ' (φ T) = s • T := fun T => DFunLike.congr_fun hφ'φ T
  have Lφφ' : ∀ R, φ (φ' R) = s • R := fun R => DFunLike.congr_fun hφφ' R

  have hβ'rat : φ.comp ψ' ∈ rationalHomSet κ E₀ A := comp_mem_rationalHomSet κ _ _ _ hψ' hφ
  have hd : (((s ^ a : ℕ)) : κ) ≠ 0 := by
    rw [Nat.cast_pow]; exact pow_ne_zero _ hs0
  have hb1 : (φ.comp ψ').comp β = (s ^ a) • AddMonoidHom.id _ := by
    ext R
    obtain ⟨T, rfl⟩ := hφsurj R
    show φ (ψ' (β (φ T))) = s ^ a • φ T
    rw [← Lψ, L1, map_nsmul]
  have hb2 : β.comp (φ.comp ψ') = (s ^ a) • AddMonoidHom.id _ := by
    ext T
    show β (φ (ψ' T)) = s ^ a • T
    rw [← Lψ, L2]
  have hinj : ∀ R, β R = 0 → R = 0 := by
    intro R hR
    obtain ⟨T, rfl⟩ := hφsurj R
    have hT : T ∈ ψ.ker := by rw [AddMonoidHom.mem_ker, Lψ]; exact hR
    rw [hker, ← hφker] at hT
    exact hT
  obtain ⟨ε, hε, hεβ, hβε⟩ := exists_inverse_of_injective_dualPair A E₀ hd β hβ (φ.comp ψ') hβ'rat hb1 hb2 hinj
  have Lεβ : ∀ R, ε (β R) = R := fun R => DFunLike.congr_fun hεβ R
  have Lβε : ∀ T, β (ε T) = T := fun T => DFunLike.congr_fun hβε T
  refine ⟨φ'.comp ε, comp_mem_rationalHomSet κ _ _ _ hε hφ', ?_, ?_⟩
  · ext T
    show φ' (ε (ψ T)) = s • T
    rw [Lψ, Lεβ, Lφ'φ]
  · ext T
    show ψ (φ' (ε T)) = s • T
    rw [Lψ, Lφφ', map_nsmul, Lβε]

variable {M s : ℕ} [NeZero M] [NeZero s] (hM : (M : κ) ≠ 0) (hMs : ((M * s : ℕ) : κ) ≠ 0)

theorem exists_veluData (hmem : jqNModC κ s ∈ modularFunctionFieldC κ (M * s))
    (hβ : (levelBetaC κ M s hmem).toRingHom.IsIntegral) (hs : s.Prime) (hs0 : (s : κ) ≠ 0)
    (E : WeierstrassCurve κ) [E.IsElliptic] (Q : E.toAffine.Point) (hQ : addOrderOf Q = s) :
    ∃ (A : WeierstrassCurve κ) (_ : A.IsElliptic)
      (φ : (E.baseChange κ).toAffine.Point →+ (A.baseChange κ).toAffine.Point),
      φ ∈ rationalHomSet κ E A ∧ φ.ker = AddSubgroup.zmultiples Q ∧
      (∀ (V : WeierstrassCurve κ) [V.IsElliptic]
        (α : (E.baseChange κ).toAffine.Point →+ (V.baseChange κ).toAffine.Point),
          α ∈ rationalHomSet κ E V → α Q = 0 → ∃ β ∈ rationalHomSet κ A V, α = β.comp φ) ∧
      ∀ (D : CycSub E (M * s)), Q ∈ D.1 → ∀ C'' : CycSub A M, (∀ T ∈ D.1, φ T ∈ C''.1) →
        (ePl hMs E D.1).restrictAlong (levelBetaC κ M s hmem) hβ = gPl hM A C''.1 := by
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hQ
    exact hs.one_lt.ne hQ
  have hsQ : s • Q = 0 := by rw [← hQ]; exact addOrderOf_nsmul_eq_zero Q
  have hΔf : (E.fullKernelQuotient Q s).Δ ≠ 0 := fullKernelQuotient_discriminant_ne_zero s E hs0 Q hQ
  rcases hs.eq_two_or_odd' with h2 | hodd
  ·
    subst h2
    rcases Q with _ | ⟨x₀, y₀, hns⟩
    · exact absurd rfl hQ0
    have hneg : -(Affine.Point.some x₀ y₀ hns) = Affine.Point.some x₀ y₀ hns := by
      rw [neg_eq_iff_add_eq_zero, ← two_nsmul, hsQ]
    have hy₀ : E.toAffine.negY x₀ y₀ = y₀ := by
      rw [Affine.Point.neg_some] at hneg
      exact ((Affine.Point.some.injEq _ _ _ _ _ _).mp hneg).2
    have hgy : E.veluGy x₀ y₀ = 0 := E.veluGy_eq_zero_of_negY_eq hy₀
    have hA2 : E.fullKernelQuotient (.some x₀ y₀ hns) 2 = E.veluQuotient2 x₀ y₀ := fullKernelQuotient_two E hns hgy
    have hΔ2 : (E.veluQuotient2 x₀ y₀).Δ ≠ 0 := hA2 ▸ hΔf
    haveI hA : (E.veluQuotient2 x₀ y₀).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ2⟩
    obtain ⟨π₀, hπcoe, hπrat, -, hπuniv⟩ :=
      exists_coe_eq_veluPointMap2_and_mem_rationalHomSet_and_comp_eq_two_smul hs0 E hns.1 hgy hΔ2
    let π : (E.baseChange κ).toAffine.Point →+ ((E.veluQuotient2 x₀ y₀).baseChange κ).toAffine.Point := π₀
    have hπapp : ∀ P : E.toAffine.Point, π P = veluPointMap2 hs0 hns.1 hgy hΔ2 P := fun P => by
      show π₀ P = _; rw [hπcoe]
    have hπQ : π (.some x₀ y₀ hns) = 0 := by
      rw [hπapp]; exact veluPointMap2_some_of_eq hs0 hns.1 hgy hΔ2 hns rfl
    have hπker : π.ker = AddSubgroup.zmultiples (Affine.Point.some x₀ y₀ hns) := by
      refine le_antisymm ?_ ((AddSubgroup.zmultiples_le_of_mem) hπQ)
      intro P hP
      rw [AddMonoidHom.mem_ker] at hP
      rcases P with _ | ⟨x, y, h⟩
      · exact zero_mem _
      · by_cases hx : x = x₀
        · subst hx
          have hy : y = y₀ := by
            rcases eq_or_ne y (E.toAffine.negY x y₀) with h1 | h1
            · rw [h1, hy₀]
            · exact Affine.Y_eq_of_Y_ne h.1 hns.1 rfl h1
          subst hy
          exact AddSubgroup.mem_zmultiples _
        · exfalso
          rw [hπapp] at hP
          exact Affine.Point.some_ne_zero _ ((veluPointMap2_some_of_ne hs0 hns.1 hgy hΔ2 h hx).symm.trans hP)
    have hπker₀ : π₀.ker = AddSubgroup.zmultiples (Affine.Point.some x₀ y₀ hns) := hπker
    refine ⟨E.veluQuotient2 x₀ y₀, hA, π, hπrat, hπker, fun V _ α hα hαQ => ?_, ?_⟩
    · refine hπuniv V inferInstance α hα fun T hT => ?_
      have hT' : T ∈ π.ker := hT
      rw [hπker] at hT'
      obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hT'
      rw [map_zsmul]
      exact (congrArg (k • ·) hαQ).trans (smul_zero k)
    · intro D hQD C'' hDC''
      have law := fun (φ : E.toAffine.Point →+ (E.fullKernelQuotient (.some x₀ y₀ hns) 2).toAffine.Point) =>
        law_beta_full hM hMs hmem hβ E D (.some x₀ y₀ hns) hQD hQ hΔf φ
      rw [hA2] at law
      exact law π₀ hπker₀
        (fun P hP => by rw [hπcoe]; exact WeierstrassCurve.coordsOrZero_veluPointMap2 E hs0 hns hgy hΔ2 P hP)
        C'' hDC''
  ·
    have hs2 : s ≠ 2 := by rintro rfl; exact (Nat.not_even_iff_odd.mpr hodd) even_two
    have hsn : s = 2 * (s / 2) + 1 := (Nat.two_mul_div_two_add_one_of_odd hodd).symm
    have hQ' : addOrderOf Q = 2 * (s / 2) + 1 := hQ.trans hsn
    have hAv : E.fullKernelQuotient Q s = E.veluQuotient (E.oddOrderSummingSet Q (s / 2)) := by
      have h := fullKernelQuotient_eq_veluQuotient_oddOrderSummingSet E Q (s / 2) hQ'
      rwa [← hsn] at h
    have hΔv : (E.veluQuotient (E.oddOrderSummingSet Q (s / 2))).Δ ≠ 0 := hAv ▸ hΔf
    haveI hA : (E.veluQuotient (E.oddOrderSummingSet Q (s / 2))).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔv⟩
    obtain ⟨φ₀, hker, hφ₀⟩ := exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed E hs hs2 hs0 Q hQ
    obtain ⟨hφrat, huniv⟩ :=
      veluPointHom_mem_rationalHomSet_and_exists_mem_rationalHomSet_comp_eq E (s / 2) Q hQ' φ₀ hker hφ₀
    refine ⟨E.veluQuotient (E.oddOrderSummingSet Q (s / 2)), hA, φ₀, hφrat, hker,
      fun V _ α hα hαQ => huniv V α hα hαQ, ?_⟩
    intro D hQD C'' hDC''
    exact law_beta_velu hM hMs hmem hβ E D (s / 2) hsn Q hQD hQ' hΔv φ₀ hker hφ₀ C'' hDC''

end Isogeny

section Subgroups

variable {G H L : Type*} [AddCommGroup G] [AddCommGroup H] [AddCommGroup L]

theorem exists_zmultiples_eq (C : AddSubgroup G) (hC : IsAddCyclic C) (n : ℕ) (hn : Nat.card C = n) :
    ∃ P : G, AddSubgroup.zmultiples P = C ∧ addOrderOf P = n := by
  obtain ⟨P, hP⟩ := (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top C).mp hC
  refine ⟨P, hP, ?_⟩
  rw [← Nat.card_zmultiples, hP, hn]

theorem zmultiples_cyclic_card (P : G) (n : ℕ) (hP : addOrderOf P = n) :
    IsAddCyclic (AddSubgroup.zmultiples P) ∧ Nat.card (AddSubgroup.zmultiples P) = n :=
  ⟨inferInstance, by rw [Nat.card_zmultiples, hP]⟩

variable {M s : ℕ}

theorem addOrderOf_add_of_coprime {g Q : G} (hg : addOrderOf g = M) (hQ : addOrderOf Q = s)
    (hcop : M.Coprime s) : addOrderOf (g + Q) = M * s := by
  rw [← hg, ← hQ]
  exact (AddCommute.all g Q).addOrderOf_add_eq_mul_addOrderOf_of_coprime (by rwa [hg, hQ])

theorem nsmul_mem_zmultiples_of_mem_zmultiples_add {g Q : G} (hQ : addOrderOf Q = s)
    {T : G} (hT : T ∈ AddSubgroup.zmultiples (g + Q)) : s • T ∈ AddSubgroup.zmultiples g := by
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hT
  have hsQ : s • Q = 0 := by rw [← hQ]; exact addOrderOf_nsmul_eq_zero Q
  have : s • (k • (g + Q)) = k • (s • g) := by
    rw [smul_comm, smul_add, hsQ, add_zero]
  rw [this]
  exact AddSubgroup.zsmul_mem _ (AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples g) s) k

theorem mem_zmultiples_add_of_coprime {g Q : G} (hg : addOrderOf g = M) (hQ : addOrderOf Q = s)
    (hcop : M.Coprime s) : Q ∈ AddSubgroup.zmultiples (g + Q) := by
  have hMg : (M : ℤ) • g = 0 := by rw [natCast_zsmul, ← hg]; exact addOrderOf_nsmul_eq_zero g
  have hsQ : (s : ℤ) • Q = 0 := by rw [natCast_zsmul, ← hQ]; exact addOrderOf_nsmul_eq_zero Q
  have hbez : (M : ℤ) * M.gcdA s + (s : ℤ) * M.gcdB s = 1 := by
    rw [← Nat.gcd_eq_gcd_ab M s, Nat.Coprime.gcd_eq_one hcop, Nat.cast_one]
  have key : (M.gcdA s * (M : ℤ)) • (g + Q) = Q := by
    rw [zsmul_add, mul_zsmul, hMg, zsmul_zero, zero_add]
    calc (M.gcdA s * (M : ℤ)) • Q
        = (M.gcdA s * (M : ℤ)) • Q + (M.gcdB s * (s : ℤ)) • Q := by
          rw [mul_zsmul Q (M.gcdB s) (s : ℤ), hsQ, zsmul_zero, add_zero]
      _ = ((M : ℤ) * M.gcdA s + (s : ℤ) * M.gcdB s) • Q := by
          rw [add_zsmul, mul_comm (M.gcdA s), mul_comm (M.gcdB s)]
      _ = Q := by rw [hbez, one_zsmul]
  have hmem : (M.gcdA s * (M : ℤ)) • (g + Q) ∈ AddSubgroup.zmultiples (g + Q) :=
    AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples _) _
  rwa [key] at hmem

theorem map_mem_zmultiples_of_mem_zmultiples_add (φ : G →+ H) {g Q : G} (hφQ : φ Q = 0)
    {T : G} (hT : T ∈ AddSubgroup.zmultiples (g + Q)) : φ T ∈ AddSubgroup.zmultiples (φ g) := by
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hT
  rw [map_zsmul, map_add, hφQ, add_zero]
  exact AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples _) k

theorem map_mem_of_mem_zmultiples (φ : G →+ H) {g : G} (C : AddSubgroup H) (hg : φ g ∈ C)
    {T : G} (hT : T ∈ AddSubgroup.zmultiples g) : φ T ∈ C := by
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hT
  rw [map_zsmul]
  exact C.zsmul_mem hg k

theorem addOrderOf_map_of_ker_eq_zmultiples (φ : G →+ H) {g Q : G} (hg : addOrderOf g = M)
    (hQ : addOrderOf Q = s) (hcop : M.Coprime s) (hker : φ.ker = AddSubgroup.zmultiples Q) :
    addOrderOf (φ g) = M := by
  apply Nat.dvd_antisymm
  · rw [← hg]; exact addOrderOf_map_dvd φ g
  · set d := addOrderOf (φ g) with hd
    have h0 : φ (d • g) = 0 := by rw [map_nsmul]; exact addOrderOf_nsmul_eq_zero (φ g)
    have hmem : d • g ∈ AddSubgroup.zmultiples Q := by rw [← hker, AddMonoidHom.mem_ker]; exact h0
    have h1 : addOrderOf (d • g) ∣ s := by rw [← hQ]; exact addOrderOf_dvd_of_mem_zmultiples hmem
    have h2 : addOrderOf (d • g) ∣ M := by rw [← hg]; exact addOrderOf_smul_dvd d
    have h3 : addOrderOf (d • g) = 1 := Nat.eq_one_of_dvd_coprimes hcop h2 h1
    have h4 : d • g = 0 := AddMonoid.addOrderOf_eq_one_iff.mp h3
    rw [← hg]
    exact addOrderOf_dvd_of_nsmul_eq_zero h4

theorem exists_eq_zmultiples_of_card_eq_prime (A : AddSubgroup G) (hs : s.Prime) (hA : Nat.card A = s) :
    ∃ Q : G, Q ∈ A ∧ addOrderOf Q = s ∧ A = AddSubgroup.zmultiples Q := by
  haveI : Fact s.Prime := ⟨hs⟩
  haveI : Finite A := Nat.finite_of_card_ne_zero (by rw [hA]; exact hs.ne_zero)
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := A) s (by rw [hA])
  refine ⟨(x : G), x.2, by rw [AddSubgroup.addOrderOf_coe, hx], ?_⟩
  symm
  apply AddSubgroup.eq_of_le_of_card_ge
  · rw [AddSubgroup.zmultiples_le]; exact x.2
  · rw [hA, Nat.card_zmultiples, AddSubgroup.addOrderOf_coe, hx]

theorem exists_mem_addOrderOf_eq_of_card_eq_prime_pow (A : AddSubgroup G) (hs : s.Prime) (k : ℕ)
    (hA : Nat.card A = s ^ (k + 1)) : ∃ Q : G, Q ∈ A ∧ addOrderOf Q = s := by
  haveI : Fact s.Prime := ⟨hs⟩
  haveI : Finite A := Nat.finite_of_card_ne_zero (by rw [hA]; exact pow_ne_zero _ hs.ne_zero)
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := A) s (by rw [hA]; exact dvd_pow_self s (Nat.succ_ne_zero k))
  exact ⟨(x : G), x.2, by rw [AddSubgroup.addOrderOf_coe, hx]⟩

theorem natCard_ker_comp (φ : G →+ H) (ψ₁ : H →+ L) (hsurj : Function.Surjective φ) :
    Nat.card (ψ₁.comp φ).ker = Nat.card φ.ker * Nat.card ψ₁.ker := by

  have hle : φ.ker ≤ (ψ₁.comp φ).ker := fun T hT => by
    rw [AddMonoidHom.mem_ker] at hT ⊢
    rw [AddMonoidHom.comp_apply, hT, map_zero]
  let f : (ψ₁.comp φ).ker →+ ψ₁.ker :=
    (φ.comp (ψ₁.comp φ).ker.subtype).codRestrict ψ₁.ker (fun T => by
      rw [AddMonoidHom.mem_ker]
      exact T.2)
  have hf : Function.Surjective f := by
    rintro ⟨R, hR⟩
    obtain ⟨T, rfl⟩ := hsurj R
    exact ⟨⟨T, hR⟩, rfl⟩
  have hfker : f.ker = φ.ker.addSubgroupOf (ψ₁.comp φ).ker := by
    ext ⟨T, hT⟩
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have h1 : Nat.card (ψ₁.comp φ).ker = Nat.card ((ψ₁.comp φ).ker ⧸ f.ker) * Nat.card f.ker :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker
  have h2 : Nat.card ((ψ₁.comp φ).ker ⧸ f.ker) = Nat.card ψ₁.ker :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hf).toEquiv
  have h3 : Nat.card f.ker = Nat.card φ.ker := by
    rw [hfker]
    exact Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hle).toEquiv
  rw [h1, h2, h3, Nat.mul_comm]

end Subgroups

section Membership

universe u

theorem jNGeomGen_mem_of_jGeomGen_mem (K : Type u) [Field K] (N : ℕ) [NeZero N]
    {w : Place K (modularFunctionFieldC K N)} (hj : jGeomGen K N ∈ w.toValuationSubring) :
    jNGeomGen K N ∈ w.toValuationSubring := by
  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  have hfac : Polynomial.eval₂RingHom (Int.castRingHom (modularFunctionFieldC K N)) (jGeomGen K N)
      = (SubringClass.subtype w.toValuationSubring).comp
          (Polynomial.eval₂RingHom (Int.castRingHom w.toValuationSubring) ⟨jGeomGen K N, hj⟩) := by
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    simp
  refine w.mem_of_eval_monic_eq_zero
    (P := data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (modularFunctionFieldC K N))
      (jGeomGen K N)))
    (data.monic.map _) (fun i => ?_) ?_
  · rw [Polynomial.coeff_map, hfac, RingHom.comp_apply]
    exact SetLike.coe_mem _
  · rw [Polynomial.eval_map]
    exact evalModularPair_jGeomGen_eq_zero K N data

theorem mem_ssPlaces_of_ord_pos (q N : ℕ) [NeZero N] (K : Type u) [Field K]
    [DecidableEq K] [IsAlgClosed K] {a : K} (ha : a ∈ ssJSet q K)
    (w : Place K (modularFunctionFieldC K N))
    (hpos : 0 < w.ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) a)) :
    w ∈ ssPlaces q N K := by
  have hrat : w.IsRational :=
    (Place.isRational_iff_deg_eq_one w).mpr (place_deg_eq_one_of_isAlgClosed K N w)
  have hj : jGeomGen K N ∈ w.toValuationSubring := by
    have h := add_mem (w.mem_of_ord_nonneg (jGeomGen_sub_algebraMap_ne_zero K N a) hpos.le)
      (w.algebraMap_mem' a)
    rwa [sub_add_cancel] at h
  have hjN : jNGeomGen K N ∈ w.toValuationSubring := jNGeomGen_mem_of_jGeomGen_mem K N hj
  have hev : w.evalAt (jGeomGen K N) = a := by
    rw [w.evalAt_congr hj (w.algebraMap_mem' a) (Or.inr hpos), w.evalAt_algebraMap]
  rw [mem_ssPlaces_iff, isSupersingularPlace_iff]
  refine ⟨hrat, ⟨hj, hjN⟩, ?_⟩
  rw [hev]
  exact ha

end Membership

section Reflection

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [CharP K p] [DecidableEq K] [IsAlgClosed K]
  {M s : ℕ} [NeZero M] [NeZero s] (X : SSLevelDatum p K M s)

def levelPair : Fin 2 → (↥(modularFunctionFieldC K M) →ₐ[K] ↥(modularFunctionFieldC K (M * s))) :=
  ![levelAlphaC K M s X.mem_M, levelBetaC K M s X.mem_s]

theorem levelPair_integral : ∀ i, (levelPair X i).toRingHom.IsIntegral := by
  intro i
  fin_cases i
  · exact X.fstIntegral
  · exact X.sndIntegral

theorem coe_levelPair_zero (x : ↥(modularFunctionFieldC K M)) :
    ((levelPair X 0 x : ↥(modularFunctionFieldC K (M * s))) : LaurentSeries K) = x :=
  coe_levelAlphaC K M s X.mem_M x

theorem coe_levelPair_one (x : ↥(modularFunctionFieldC K M)) :
    ((levelPair X 1 x : ↥(modularFunctionFieldC K (M * s))) : LaurentSeries K) = qExpand K s x :=
  coe_levelBetaC K M s X.mem_s x

theorem mem_ssPlaces_of_restrictAlong_levelAlphaC_eq (hs : s.Prime) (hsp : s ≠ p) (hpM : ¬ p ∣ M) (hsM : ¬ s ∣ M)
    (v : ↥(ssPlaces p M K)) (W : Place K ↥(modularFunctionFieldC K (M * s)))
    (hW : Place.restrictAlong (levelAlphaC K M s X.mem_M) X.fstIntegral W = v.1) :
    W ∈ ssPlaces p (M * s) K :=
  (degeneracyPair_finiteSeparableDeg_ssPlaces_preserved_reflected M s p hs hsp hpM hsM (k := K)
    (levelPair X) (levelPair_integral X) (coe_levelPair_zero X) (coe_levelPair_one X)).2.2.2.2 0 v.1 v.2 W hW

end Reflection

section Walk

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [CharP K p] [DecidableEq K] [IsAlgClosed K]
  {M s : ℕ} [NeZero M] [NeZero s] (X : SSLevelDatum p K M s) (P : Set ↥(ssPlaces p M K))
  (hs : s.Prime) (hsp : s ≠ p) (hpM : ¬ p ∣ M) (hsM : ¬ s ∣ M)
  (hM : (M : K) ≠ 0) (hMs : ((M * s : ℕ) : K) ≠ 0)

def inP (v : Place K ↥(modularFunctionFieldC K M)) : Prop :=
  ∃ h : v ∈ ssPlaces p M K, (⟨v, h⟩ : ↥(ssPlaces p M K)) ∈ P

omit [Fact p.Prime] [CharP K p] [IsAlgClosed K] [NeZero s] in
theorem inP_iff {v : Place K ↥(modularFunctionFieldC K M)} (h : v ∈ ssPlaces p M K) :
    inP P v ↔ (⟨v, h⟩ : ↥(ssPlaces p M K)) ∈ P :=
  ⟨fun ⟨_, h'⟩ => h', fun h' => ⟨h, h'⟩⟩

theorem natCast_ne_zero_of_prime_ne (hs : s.Prime) (hsp : s ≠ p) : (s : K) ≠ 0 :=
  natCast_ne_zero_of_not_dvd (p := p) fun h =>
    hsp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hs).mp h).symm

include hs hsp hpM hsM in

theorem step (Hflip : ∀ W : ↥(ssPlaces p (M * s) K), (X.fst W ∈ P ↔ ¬ X.snd W ∈ P))
    (E' A : WeierstrassCurve K) [E'.IsElliptic] [A.IsElliptic] (g Q : E'.toAffine.Point)
    (hg : addOrderOf g = M) (hQ : addOrderOf Q = s)
    (φ : (E'.baseChange K).toAffine.Point →+ (A.baseChange K).toAffine.Point)
    (hφker : φ.ker = AddSubgroup.zmultiples Q)
    (law : ∀ (D : CycSub E' (M * s)), Q ∈ D.1 → ∀ C'' : CycSub A M, (∀ T ∈ D.1, φ T ∈ C''.1) →
        (ePl hMs E' D.1).restrictAlong (levelBetaC K M s X.mem_s) X.sndIntegral = gPl hM A C''.1)
    (hv : gPl hM E' (AddSubgroup.zmultiples g) ∈ ssPlaces p M K) :
    addOrderOf (φ g) = M ∧
    ∃ hA : gPl hM A (AddSubgroup.zmultiples (φ g : A.toAffine.Point)) ∈ ssPlaces p M K,
      (inP P (gPl hM E' (AddSubgroup.zmultiples g)) ↔
        ¬ inP P (gPl hM A (AddSubgroup.zmultiples (φ g : A.toAffine.Point)))) := by
  have hcop : M.Coprime s := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hs).mpr hsM)
  let φ₀ : E'.toAffine.Point →+ A.toAffine.Point := φ
  have hφ₀ker : φ₀.ker = AddSubgroup.zmultiples Q := hφker
  have hφQ : φ₀ Q = 0 := by
    rw [← AddMonoidHom.mem_ker, hφ₀ker]; exact AddSubgroup.mem_zmultiples Q
  have hord : addOrderOf (φ₀ g) = M := addOrderOf_map_of_ker_eq_zmultiples φ₀ hg hQ hcop hφ₀ker

  let D : CycSub E' (M * s) :=
    ⟨AddSubgroup.zmultiples (g + Q), zmultiples_cyclic_card _ _ (addOrderOf_add_of_coprime hg hQ hcop)⟩
  let C : CycSub E' M := ⟨AddSubgroup.zmultiples g, zmultiples_cyclic_card _ _ hg⟩
  let C'' : CycSub A M := ⟨AddSubgroup.zmultiples (φ₀ g), zmultiples_cyclic_card _ _ hord⟩
  have hDC : ∀ T ∈ D.1, s • T ∈ C.1 := fun T hT => nsmul_mem_zmultiples_of_mem_zmultiples_add hQ hT
  have hQD : Q ∈ D.1 := mem_zmultiples_add_of_coprime hg hQ hcop
  have hDC'' : ∀ T ∈ D.1, φ T ∈ C''.1 := fun T hT => map_mem_zmultiples_of_mem_zmultiples_add φ₀ hφQ hT
  have hWα : Place.restrictAlong (levelAlphaC K M s X.mem_M) X.fstIntegral (ePl hMs E' D.1) = gPl hM E' C.1 :=
    law_alpha hM hMs X.mem_M X.fstIntegral E' D C hDC
  have hW₀ : ePl hMs E' D.1 ∈ ssPlaces p (M * s) K :=
    mem_ssPlaces_of_restrictAlong_levelAlphaC_eq X hs hsp hpM hsM ⟨_, hv⟩ (ePl hMs E' D.1) hWα
  have hWβ : Place.restrictAlong (levelBetaC K M s X.mem_s) X.sndIntegral (ePl hMs E' D.1) = gPl hM A C''.1 :=
    law D hQD C'' hDC''
  let Wss : ↥(ssPlaces p (M * s) K) := ⟨ePl hMs E' D.1, hW₀⟩
  have hfst : X.fst Wss = ⟨gPl hM E' C.1, hv⟩ := Subtype.ext hWα
  have hA : gPl hM A C''.1 ∈ ssPlaces p M K := by
    have h := (X.snd Wss).2
    have h' : (X.snd Wss).1 = gPl hM A C''.1 := hWβ
    rwa [h'] at h
  have hsnd : X.snd Wss = ⟨gPl hM A C''.1, hA⟩ := Subtype.ext hWβ
  have hflip := Hflip Wss
  rw [hfst, hsnd] at hflip
  refine ⟨hord, hA, ?_⟩
  exact (inP_iff P hv).trans (hflip.trans (not_congr (inP_iff P hA)).symm)

include hs hsp hpM hsM hMs in

theorem chain (Hflip : ∀ W : ↥(ssPlaces p (M * s) K), (X.fst W ∈ P ↔ ¬ X.snd W ∈ P))
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic] (C₀ : CycSub E₀ M) (m : ℕ) :
    ∀ (E' : WeierstrassCurve K) [E'.IsElliptic] (g : E'.toAffine.Point) (hg : addOrderOf g = M)
      (ψ : (E'.baseChange K).toAffine.Point →+ (E₀.baseChange K).toAffine.Point) (hψ : ψ ∈ rationalHomSet K E' E₀)
      (ψ' : (E₀.baseChange K).toAffine.Point →+ (E'.baseChange K).toAffine.Point) (hψ' : ψ' ∈ rationalHomSet K E₀ E')
      (a : ℕ) (h1 : ψ'.comp ψ = s ^ a • AddMonoidHom.id _) (h2 : ψ.comp ψ' = s ^ a • AddMonoidHom.id _)
      (hker : Nat.card ψ.ker = s ^ (m + 1)) (hmap : ψ g ∈ C₀.1)
      (hv : gPl hM E' (AddSubgroup.zmultiples g) ∈ ssPlaces p M K),
      (inP P (gPl hM E' (AddSubgroup.zmultiples g)) ↔ inP P (gPl hM E₀ C₀.1)) ↔ Odd m := by
  have hs0 : (s : K) ≠ 0 := natCast_ne_zero_of_prime_ne (p := p) hs hsp
  induction m with
  | zero =>
    intro E' _ g hg ψ hψ ψ' hψ' a h1 h2 hker hmap hv

    obtain ⟨Q, hQker, hQ, hkerQ⟩ := exists_eq_zmultiples_of_card_eq_prime ψ.ker hs (by rw [hker, zero_add, pow_one])
    obtain ⟨A, hA, φ, hφ, hφker, huniv, law⟩ := exists_veluData hM hMs X.mem_s X.sndIntegral hs hs0 E' Q hQ
    haveI := hA
    obtain ⟨hord, hAmem, hflip⟩ := step X P hs hsp hpM hsM hM hMs Hflip E' A g Q hg hQ φ hφker law hv
    obtain ⟨hsurj, φ', hφ', hφ'φ, hφφ'⟩ := surjective_and_exists_dual_of_universal E' A hs hs0 Q hQ φ hφ hφker huniv
    obtain ⟨ψ'', hψ'', hd1, hd2⟩ := exists_dual_of_ker_eq_zmultiples E' A E₀ hs0 Q φ hφ hφker hsurj φ' hφ' hφ'φ hφφ'
      huniv ψ hψ ψ' hψ' a h1 h2 hkerQ

    have hlvl : ∀ T ∈ (AddSubgroup.zmultiples g : Set E'.toAffine.Point), ψ T ∈ (C₀.1 : Set E₀.toAffine.Point) :=
      fun T hT => map_mem_of_mem_zmultiples ψ C₀.1 hmap hT
    obtain ⟨γ, hγ, hheq⟩ := (exists_variableChange_heq_vcInvFun_iff_exists_dualPair E' A E₀ hs hs0 Q hQ φ hφ hφker
      huniv (AddSubgroup.zmultiples g : Set E'.toAffine.Point) (C₀.1 : Set E₀.toAffine.Point)).mpr
        ⟨ψ, hψ, ψ'', hψ'', hkerQ, hd1, hd2, hlvl⟩
    have hEq : gPl hM A (AddSubgroup.zmultiples (φ g : A.toAffine.Point)) = gPl hM E₀ C₀.1 := by
      refine (g3 hM A E₀ ⟨AddSubgroup.zmultiples (φ g : A.toAffine.Point), zmultiples_cyclic_card _ _ hord⟩ C₀).mpr
        ⟨γ, hγ, ?_⟩
      intro T₁ hT₁
      let φ₀ : E'.toAffine.Point →+ A.toAffine.Point := φ
      have hT₁' : T₁ ∈ (AddSubgroup.zmultiples g).map φ₀ := by
        rw [AddMonoidHom.map_zmultiples]; exact hT₁
      obtain ⟨T, hT, rfl⟩ := AddSubgroup.mem_map.mp hT₁'
      exact hheq T hT
    rw [hEq] at hflip
    have h0 : ¬ Odd 0 := Nat.not_odd_zero
    tauto
  | succ m ih =>
    intro E' _ g hg ψ hψ ψ' hψ' a h1 h2 hker hmap hv

    obtain ⟨Q, hQker, hQ⟩ := exists_mem_addOrderOf_eq_of_card_eq_prime_pow ψ.ker hs (m + 1) hker
    obtain ⟨A, hA, φ, hφ, hφker, huniv, law⟩ := exists_veluData hM hMs X.mem_s X.sndIntegral hs hs0 E' Q hQ
    haveI := hA
    obtain ⟨hord, hAmem, hflip⟩ := step X P hs hsp hpM hsM hM hMs Hflip E' A g Q hg hQ φ hφker law hv
    obtain ⟨hsurj, φ', hφ', hφ'φ, hφφ'⟩ := surjective_and_exists_dual_of_universal E' A hs hs0 Q hQ φ hφ hφker huniv

    have hψQ : ψ Q = 0 := hQker
    obtain ⟨ψ₁, hψ₁, hψeq⟩ := huniv E₀ ψ hψ hψQ
    have Lψ : ∀ T, ψ T = ψ₁ (φ T) := fun T => by rw [hψeq]; rfl
    have L1 : ∀ T, ψ' (ψ T) = s ^ a • T := fun T => DFunLike.congr_fun h1 T
    have L2 : ∀ T, ψ (ψ' T) = s ^ a • T := fun T => DFunLike.congr_fun h2 T
    have hψ₁' : φ.comp ψ' ∈ rationalHomSet K E₀ A := comp_mem_rationalHomSet K _ _ _ hψ' hφ
    have h1' : (φ.comp ψ').comp ψ₁ = s ^ a • AddMonoidHom.id _ := by
      ext R
      obtain ⟨T, rfl⟩ := hsurj R
      show φ (ψ' (ψ₁ (φ T))) = s ^ a • φ T
      rw [← Lψ, L1, map_nsmul]
    have h2' : ψ₁.comp (φ.comp ψ') = s ^ a • AddMonoidHom.id _ := by
      ext T
      show ψ₁ (φ (ψ' T)) = s ^ a • T
      rw [← Lψ, L2]
    have hker₁ : Nat.card ψ₁.ker = s ^ (m + 1) := by
      have hcz : Nat.card φ.ker = s := by
        rw [hφker]
        exact (Nat.card_zmultiples Q).trans hQ
      have hc := natCard_ker_comp φ ψ₁ hsurj
      rw [← hψeq, hker, hcz, pow_succ' s (m + 1)] at hc
      exact (Nat.eq_of_mul_eq_mul_left hs.pos hc).symm
    have hmap₁ : ψ₁ (φ g) ∈ C₀.1 := by rw [← Lψ]; exact hmap
    have IH := ih A (φ g) hord ψ₁ hψ₁ (φ.comp ψ') hψ₁' a h1' h2' hker₁ hmap₁ hAmem
    rw [Nat.odd_add_one]
    tauto

end Walk

end ModularCurve.OddWalkW2
p2m_reactivate "P2MW.S_ModularCurve_SSLevelDatum_exists_fst_mem_iff_snd_mem_of_nonempty.ModularCurve P2MW.S_ModularCurve_SSLevelDatum_exists_fst_mem_iff_snd_mem_of_nonempty.ModularCurve.OddWalkW2"
p2m_reactivate "P2MW.S_ModularCurve_SSLevelDatum_exists_fst_mem_iff_snd_mem_of_nonempty.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_SSLevelDatum_exists_fst_mem_iff_snd_mem_of_nonempty.ModularCurve P2MW.S_ModularCurve_SSLevelDatum_exists_fst_mem_iff_snd_mem_of_nonempty.ModularCurve.OddWalkW2"

p2m_open "WeierstrassCurve~card" in open AlgebraicCurve _root_.ModularCurve _root_.P2MW.S_ModularCurve_SSLevelDatum_exists_fst_mem_iff_snd_mem_of_nonempty.ModularCurve ModularCurve.OddWalkW2 in
theorem solution
    (M s q' : ℕ) [NeZero M] [NeZero s] [Fact q'.Prime] (hs : s.Prime)
    (hq5 : 5 ≤ q') (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) q']
    (X : SSLevelDatum q' (IsLocalRing.ResidueField ↥A) M s)
    (P : Set ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A))) (hP : P.Nonempty) :
    ∃ W : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A)), (X.fst W ∈ P ↔ X.snd W ∈ P) := by
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A
  by_contra hcon
  have Hflip : ∀ W : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A)), (X.fst W ∈ P ↔ ¬ X.snd W ∈ P) := by
    intro W
    have h : ¬ (X.fst W ∈ P ↔ X.snd W ∈ P) := fun h => hcon ⟨W, h⟩
    tauto
  have hM : (M : IsLocalRing.ResidueField ↥A) ≠ 0 := natCast_ne_zero_of_not_dvd (p := q') hq'M
  have hMs : ((M * s : ℕ) : IsLocalRing.ResidueField ↥A) ≠ 0 :=
    natCast_ne_zero_of_not_dvd (p := q') (not_dvd_mul hs hq'M hsq')

  obtain ⟨E₀, hE₀, C₀, α, α', n, hss, hcyc, hcard, hstab, hα, hα', h1, h2, hodd, hker⟩ :=
    WeierstrassCurve.exists_supersingular_endomorphism_natCard_ker_eq_odd_pow_stabilizing_cyclic
      (IsLocalRing.ResidueField ↥A) q' M s hs hsq' hq'M hsM
  haveI := hE₀
  obtain ⟨g₀, hg₀C, hg₀⟩ := exists_zmultiples_eq C₀ hcyc M hcard
  subst hg₀C

  have hj : E₀.j ∈ ssJSet q' (IsLocalRing.ResidueField ↥A) :=
    WeierstrassCurve.j_mem_ssJSet_of_forall_smul_eq_zero q' E₀ hss
  have hv₀ : gPl hM E₀ (AddSubgroup.zmultiples g₀) ∈ ssPlaces q' M (IsLocalRing.ResidueField ↥A) :=
    mem_ssPlaces_of_ord_pos q' M (IsLocalRing.ResidueField ↥A) hj _
      (g1 hM E₀ ⟨AddSubgroup.zmultiples g₀, zmultiples_cyclic_card g₀ M hg₀⟩)

  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hodd.pos; omega⟩
  have hmap : α g₀ ∈ AddSubgroup.zmultiples g₀ := hstab g₀ (AddSubgroup.mem_zmultiples g₀)
  have key := chain X P hs hsq' hq'M hsM hM hMs Hflip E₀ ⟨AddSubgroup.zmultiples g₀, zmultiples_cyclic_card g₀ M hg₀⟩
    m E₀ g₀ hg₀ α hα α' hα' (m + 1) h1 h2 hker hmap hv₀
  have hm : ¬ Odd m := Nat.odd_add_one.mp hodd
  exact hm (key.mp Iff.rfl)

end S_ModularCurve_SSLevelDatum_exists_fst_mem_iff_snd_mem_of_nonempty
end P2MW
export P2MW.S_ModularCurve_SSLevelDatum_exists_fst_mem_iff_snd_mem_of_nonempty (solution)
