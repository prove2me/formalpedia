-- Prove2me | solution 1 for ModularCurve.exists_natural_diamond_algHom_qExpFunctionFieldC_gammaH_of_transcendental_j
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/a1201893-a500-5507-83f5-de7c02a8ec25

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_XHDiamondModL
import Theorems.Thm_ModularCurve_exists_natural_diamond_algHom_qExpFunctionFieldC_gammaH_bot_of_transcendental_j
import Theorems.Thm_ModularCurve_exists_isDiamondPullbackModL_bot_forall_coe_mem_gammaH_iff
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Theorems.Thm_AddCommGroup_natCard_torsionOrbit_gammaH_eq_index
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_natCard_torsion_eq_sq
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_natural_diamond_algHom_qExpFunctionFieldC_gammaH_of_transcendental_j
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_succ ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun"
p2m_attr_erase "simp" "KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X"
p2m_attr_erase "simp" "ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply"
p2m_attr_erase "simp" "CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open WeierstrassCurve WeierstrassCurve.Affine ModularCurve AlgebraicCurve
open scoped MatrixGroups ModularForm

noncomputable section

namespace P2MKcDICTH

section Orb

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] {M : ℕ} [NeZero M]

theorem nsmul_eq_mod_nsmul {P : A} (hP : M • P = 0) (n : ℕ) : n • P = (n % M) • P := by
  conv_lhs => rw [← Nat.mod_add_div n M, add_nsmul, mul_nsmul, hP, nsmul_zero, add_zero]

theorem val_natCast_nsmul {P : A} (hP : M • P = 0) (n : ℕ) : ((n : ZMod M).val) • P = n • P := by
  rw [ZMod.val_natCast, ← nsmul_eq_mod_nsmul hP]

theorem val_mul_nsmul {P : A} (hP : M • P = 0) (u v : ZMod M) :
    (u * v).val • P = u.val • (v.val • P) := by
  rw [ZMod.val_mul, ← nsmul_eq_mod_nsmul hP, mul_nsmul']

theorem val_add_nsmul {P : A} (hP : M • P = 0) (u v : ZMod M) :
    (u + v).val • P = u.val • P + v.val • P := by
  rw [ZMod.val_add, ← nsmul_eq_mod_nsmul hP, add_nsmul]

theorem val_neg_nsmul {P : A} (hP : M • P = 0) (u : ZMod M) : (-u).val • P = -(u.val • P) := by
  have h : (-u + u).val • P = 0 := by rw [neg_add_cancel, ZMod.val_zero, zero_nsmul]
  rw [val_add_nsmul hP] at h
  exact eq_neg_of_add_eq_zero_left h

theorem val_one_nsmul {P : A} (hP : M • P = 0) : (1 : ZMod M).val • P = P := by
  have := val_natCast_nsmul hP 1
  rwa [Nat.cast_one, one_nsmul] at this

theorem val_neg_one_nsmul {P : A} (hP : M • P = 0) : (-1 : ZMod M).val • P = -P := by
  rw [val_neg_nsmul hP, val_one_nsmul hP]

theorem nsmul_of_addOrderOf_eq {P : A} (hP : addOrderOf P = M) : M • P = 0 := by
  rw [← hP]; exact addOrderOf_nsmul_eq_zero P

theorem nsmul_val_nsmul_eq_zero {P : A} (hP : M • P = 0) (u : ZMod M) : M • (u.val • P) = 0 := by
  rw [nsmul_left_comm, hP, nsmul_zero]

theorem addOrderOf_units_smul {P : A} (hP : addOrderOf P = M) (u : (ZMod M)ˣ) :
    addOrderOf ((u : ZMod M).val • P) = M := by
  have hP0 := nsmul_of_addOrderOf_eq hP
  refine Nat.dvd_antisymm ?_ ?_
  · rw [addOrderOf_dvd_iff_nsmul_eq_zero]
    exact nsmul_val_nsmul_eq_zero hP0 _
  · have h1 : addOrderOf ((u : ZMod M).val • P) • ((u : ZMod M).val • P) = 0 :=
      addOrderOf_nsmul_eq_zero _
    have h2 : ((u⁻¹ : (ZMod M)ˣ) : ZMod M).val • ((u : ZMod M).val • P) = P := by
      rw [← val_mul_nsmul hP0, ← Units.val_mul, inv_mul_cancel, Units.val_one, val_one_nsmul hP0]
    have := congrArg (fun T => ((u⁻¹ : (ZMod M)ˣ) : ZMod M).val • T) h1
    simp only [nsmul_zero] at this
    rw [nsmul_left_comm, h2] at this
    have key : addOrderOf P ∣ addOrderOf ((u : ZMod M).val • P) :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr this
    rwa [hP] at key

theorem addOrderOf_map_eq {φ : A →+ B} (hφ : Function.Injective φ) {P : A}
    (hP : addOrderOf P = M) : addOrderOf (φ P) = M := by
  rw [addOrderOf_injective φ hφ, hP]

theorem addOrderOf_neg_eq {P : A} (hP : addOrderOf P = M) : addOrderOf (-P) = M := by
  rw [addOrderOf_neg, hP]

variable (H : Subgroup (ZMod M)ˣ)

abbrev orb (P : A) : Set A :=
  {T | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧ T = (u : ZMod M).val • P}

abbrev XH (A : Type*) [AddCommGroup A] (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Type _ :=
  {s : Set A // ∃ P : A, addOrderOf P = M ∧ s = orb H P}

theorem neg_one_mem_Hpm : (-1 : (ZMod M)ˣ) ∈ H ⊔ Subgroup.zpowers (-1) :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem mem_Hpm_of_mem {u : (ZMod M)ˣ} (hu : u ∈ H) : u ∈ H ⊔ Subgroup.zpowers (-1) :=
  Subgroup.mem_sup_left hu

theorem mem_orb_self {P : A} (hP : M • P = 0) : P ∈ orb H P :=
  ⟨1, Subgroup.one_mem _, by rw [Units.val_one, val_one_nsmul hP]⟩

theorem orb_eq_of_mem {P : A} (hP : M • P = 0) {T : A} (hT : T ∈ orb H P) : orb H T = orb H P := by
  obtain ⟨u, hu, rfl⟩ := hT
  ext W
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v * u, Subgroup.mul_mem _ hv hu, ?_⟩
    rw [Units.val_mul, val_mul_nsmul hP]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w * u⁻¹, Subgroup.mul_mem _ hw (Subgroup.inv_mem _ hu), ?_⟩
    rw [← val_mul_nsmul hP, ← Units.val_mul, mul_assoc, inv_mul_cancel, mul_one]

theorem neg_mem_orb {P : A} (hP : M • P = 0) {T : A} (hT : T ∈ orb H P) : -T ∈ orb H P := by
  obtain ⟨u, hu, rfl⟩ := hT
  refine ⟨-1 * u, Subgroup.mul_mem _ (neg_one_mem_Hpm H) hu, ?_⟩
  rw [Units.val_mul, val_mul_nsmul hP, Units.val_neg, Units.val_one,
    val_neg_one_nsmul (nsmul_val_nsmul_eq_zero hP _)]

theorem image_orb (m : A →+ B) (P : A) : m '' orb H P = orb H (m P) := by
  ext W
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨T, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, by rw [map_nsmul]⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨(u : ZMod M).val • P, ⟨u, hu, rfl⟩, by rw [map_nsmul]⟩

theorem eq_or_eq_of_mem_zpowers_neg_one {b : (ZMod M)ˣ} (hb : b ∈ Subgroup.zpowers (-1 : (ZMod M)ˣ)) :
    b = 1 ∨ b = -1 := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  rcases Int.even_or_odd n with hn | hn
  · exact Or.inl hn.neg_one_zpow
  · exact Or.inr hn.neg_one_zpow

theorem exists_of_mem_Hpm {u : (ZMod M)ˣ} (hu : u ∈ H ⊔ Subgroup.zpowers (-1)) :
    ∃ h ∈ H, u = h ∨ u = h * (-1) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hu
  rcases eq_or_eq_of_mem_zpowers_neg_one hb with rfl | rfl
  · exact ⟨a, ha, Or.inl (mul_one a)⟩
  · exact ⟨a, ha, Or.inr rfl⟩

variable {H}

theorem XH.ext' {s s' : XH A M H} (h : s.1 = s'.1) : s = s' := Subtype.ext h

end Orb

section Groups

variable (M : ℕ) [NeZero M]

theorem exists_gamma0_diag (h : (ZMod M)ˣ) :
    ∃ γ : CongruenceSubgroup.Gamma0 M,
      (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = (h : ZMod M) ∧
      (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ((h⁻¹ : (ZMod M)ˣ) : ZMod M) := by
  set a : ℤ := ((h : ZMod M).val : ℤ) with ha
  set d : ℤ := (((h⁻¹ : (ZMod M)ˣ) : ZMod M).val : ℤ) with hd
  have hcast_a : ((a : ℤ) : ZMod M) = (h : ZMod M) := by
    rw [ha, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hcast_d : ((d : ℤ) : ZMod M) = ((h⁻¹ : (ZMod M)ˣ) : ZMod M) := by
    rw [hd, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hdvd : (M : ℤ) ∣ a * d - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    rw [Int.cast_sub, Int.cast_mul, hcast_a, hcast_d, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Int.cast_one, sub_self]
  obtain ⟨b, hb⟩ := hdvd
  have hdet : Matrix.det !![a, b; (M : ℤ), d] = 1 := by
    rw [Matrix.det_fin_two_of]
    linarith
  refine ⟨⟨⟨!![a, b; (M : ℤ), d], hdet⟩, ?_⟩, ?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma0_mem]
    simp
  · simpa using hcast_a
  · simpa using hcast_d

theorem val_gamma0Units_inv (γ : CongruenceSubgroup.Gamma0 M) :
    (((CohCarrier.gamma0Units M γ)⁻¹ : (ZMod M)ˣ) : ZMod M) = (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) :=
  rfl

theorem gamma0Units_mem_of_mem {H : Subgroup (ZMod M)ˣ} (γ : CongruenceSubgroup.Gamma0 M)
    (hγ : (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H) : CohCarrier.gamma0Units M γ ∈ H := by
  obtain ⟨hA, h⟩ := CohCarrier.mem_GammaH_iff.mp hγ
  exact h

theorem mem_GammaH_of_gamma0Units_mem {H : Subgroup (ZMod M)ˣ} (γ : CongruenceSubgroup.Gamma0 M)
    (hγ : CohCarrier.gamma0Units M γ ∈ H) : (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H :=
  CohCarrier.mem_GammaH_iff.mpr ⟨γ.2, hγ⟩

theorem gamma0Units_eq_of_entry (γ : CongruenceSubgroup.Gamma0 M) (u : (ZMod M)ˣ)
    (h : (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = (u : ZMod M)) : CohCarrier.gamma0Units M γ = u := by
  ext
  rw [CohCarrier.val_gamma0Units]
  exact h

scoped instance finiteIndex_GammaH (H : Subgroup (ZMod M)ˣ) : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)

theorem SL_mem_zpowers_neg_one_iff (n : SL(2, ℤ)) :
    n ∈ Subgroup.zpowers (-1 : SL(2, ℤ)) ↔ n = 1 ∨ n = -1 := by
  constructor
  · intro hn
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rcases Int.even_or_odd k with hk | hk
    · exact Or.inl hk.neg_one_zpow
    · exact Or.inr hk.neg_one_zpow
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

scoped instance normal_zpowers_neg_one : (Subgroup.zpowers (-1 : SL(2, ℤ))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rcases (SL_mem_zpowers_neg_one_iff n).mp hn with rfl | rfl
  · rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
  · rw [mul_neg_one, neg_mul, mul_inv_cancel]; exact Subgroup.mem_zpowers _

theorem mem_or_neg_mem_of_mem_sup (Γ : Subgroup SL(2, ℤ)) (σ : SL(2, ℤ))
    (h : σ ∈ Γ ⊔ Subgroup.zpowers (-1)) : σ ∈ Γ ∨ -σ ∈ Γ := by
  have h' : σ ∈ ((Γ ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) : Set SL(2, ℤ)) := h
  rw [Subgroup.mul_normal] at h'
  obtain ⟨γ, hγ, n, hn, rfl⟩ := h'
  rcases (SL_mem_zpowers_neg_one_iff n).mp hn with rfl | rfl
  · exact Or.inl (by simpa using hγ)
  · exact Or.inr (by simpa using hγ)

end Groups

section Torsor

theorem finite_and_natCard_le_of_mk_le {X : Type*} {n : ℕ} (h : Cardinal.mk X ≤ n) :
    Finite X ∧ Nat.card X ≤ n := by
  have hfin : Cardinal.mk X < Cardinal.aleph0 := lt_of_le_of_lt h Cardinal.natCast_lt_aleph0
  haveI : Finite X := Cardinal.lt_aleph0_iff_finite.mp hfin
  refine ⟨this, ?_⟩
  have := Cardinal.toNat_le_toNat h Cardinal.natCast_lt_aleph0
  first | simpa using this | simpa [Nat.card] using this | exact this

theorem finite_and_natCard_algHom_le (L F Ω : Type*) [Field L] [Field F] [Field Ω] [Algebra L F]
    [Algebra L Ω] [FiniteDimensional L F] :
    Finite (F →ₐ[L] Ω) ∧ Nat.card (F →ₐ[L] Ω) ≤ Module.finrank L F := by
  have h := cardinalMk_algHom L F Ω
  rw [Module.finrank_linearMap_self L Ω F] at h
  exact finite_and_natCard_le_of_mk_le h

variable {G F Ω : Type*} [Group G] [Fintype G] [Field F] [Field Ω] [MulSemiringAction G F]
  [FaithfulSMul G F]

theorem exists_smul_of_forall_fixed (ψ ψ' : F →+* Ω)
    (h : ∀ y : F, (∀ g : G, g • y = y) → ψ' y = ψ y) :
    ∃ g : G, ∀ y : F, ψ' y = ψ (g • y) := by
  classical
  set L := FixedPoints.subfield G F with hL
  letI : Algebra L Ω := (ψ.comp L.subtype).toAlgebra
  have hmemL : ∀ y : L, ∀ g : G, g • (y : F) = y := fun y g => y.2 g

  let toA : G → (F →ₐ[L] Ω) := fun g =>
    { (ψ.comp (MulSemiringAction.toRingHom G F g) : F →+* Ω) with
      commutes' := fun c => by
        show ψ (g • (c : F)) = ψ (c : F)
        rw [hmemL c g] }
  have htoA : ∀ g y, toA g y = ψ (g • y) := fun g y => rfl
  have hinj : Function.Injective toA := by
    intro g g' hgg'
    apply FaithfulSMul.eq_of_smul_eq_smul (α := F)
    intro y
    have := congrArg (fun φ : F →ₐ[L] Ω => φ y) hgg'
    simp only [htoA] at this
    exact ψ.injective this

  let ψ'A : F →ₐ[L] Ω :=
    { ψ' with
      commutes' := fun c => by
        show ψ' (c : F) = ψ (c : F)
        exact h c (hmemL c) }

  obtain ⟨hfin, hcard⟩ := finite_and_natCard_algHom_le L F Ω
  haveI := hfin
  have hLF : Module.finrank L F = Fintype.card G := FixedPoints.finrank_eq_card G F
  have hle : Nat.card (F →ₐ[L] Ω) ≤ Nat.card G := by
    rw [Nat.card_eq_fintype_card (α := G), ← hLF]; exact hcard
  have hbij : Function.Bijective toA := hinj.bijective_of_nat_card_le hle
  obtain ⟨g, hg⟩ := hbij.2 ψ'A
  refine ⟨g, fun y => ?_⟩
  have := congrArg (fun φ : F →ₐ[L] Ω => φ y) hg
  simp only [htoA] at this
  exact this.symm

end Torsor

section Count

variable {K F Ω : Type*} [Field K] [Field F] [Field Ω] [Algebra K F] [Algebra K Ω]

def eqLocus (ψ ψ₀ : F →ₐ[K] Ω) : IntermediateField K F where
  carrier := {y | ψ y = ψ₀ y}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, map_mul, ha, hb]
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_add, map_add, ha, hb]
  zero_mem' := by simp
  algebraMap_mem' r := by
    simp only [Set.mem_setOf_eq]
    rw [AlgHom.commutes, AlgHom.commutes]
  inv_mem' a ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv₀, map_inv₀, ha]

theorem apply_eq_of_mem_adjoin {ψ ψ₀ : F →ₐ[K] Ω} {x : F} (hx : ψ x = ψ₀ x) {y : F}
    (hy : y ∈ IntermediateField.adjoin K ({x} : Set F)) : ψ y = ψ₀ y := by
  have hle : IntermediateField.adjoin K ({x} : Set F) ≤ eqLocus ψ ψ₀ :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hx)
  exact hle hy

theorem finite_and_natCard_normalised_le (x : F) (c : Ω)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] :
    Finite {ψ : F →ₐ[K] Ω // ψ x = c} ∧
      Nat.card {ψ : F →ₐ[K] Ω // ψ x = c} ≤
        Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F := by
  classical
  by_cases hne : Nonempty {ψ : F →ₐ[K] Ω // ψ x = c}
  swap
  · rw [not_nonempty_iff] at hne
    haveI := hne
    exact ⟨Finite.of_subsingleton, by simp⟩
  obtain ⟨⟨ψ₀, hψ₀⟩⟩ := hne
  set L := IntermediateField.adjoin K ({x} : Set F) with hL
  letI : Algebra L Ω := ((ψ₀ : F →+* Ω).comp (algebraMap L F)).toAlgebra
  let ι : {ψ : F →ₐ[K] Ω // ψ x = c} → (F →ₐ[L] Ω) := fun ψ =>
    { (ψ.1 : F →+* Ω) with
      commutes' := fun r => by
        show ψ.1 (r : F) = ψ₀ (r : F)
        exact apply_eq_of_mem_adjoin (ψ.2.trans hψ₀.symm) r.2 }
  have hι : Function.Injective ι := by
    intro ψ ψ' h
    apply Subtype.ext
    apply AlgHom.ext
    intro y
    exact congrArg (fun φ : F →ₐ[L] Ω => φ y) h
  obtain ⟨hfin, hcard⟩ := finite_and_natCard_algHom_le L F Ω
  haveI := hfin
  exact ⟨Finite.of_injective ι hι, (Nat.card_le_card_of_injective ι hι).trans hcard⟩

end Count

section Descent

variable {K : Type*} [Field K] {M : ℕ} [NeZero M] (H : Subgroup (ZMod M)ˣ)

def Fb (K : Type*) [Field K] (M : ℕ) : IntermediateField K (LaurentSeries K) :=
  qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)

def FH (K : Type*) [Field K] (M : ℕ) (H : Subgroup (ZMod M)ˣ) :
    IntermediateField K (LaurentSeries K) :=
  qExpFunctionFieldC K (CohCarrier.GammaH M H)

theorem Fb_eq : Fb K M = qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) := rfl

theorem FH_eq : FH K M H = qExpFunctionFieldC K (CohCarrier.GammaH M H) := rfl

scoped instance instFieldFb : Field (Fb K M) := inferInstance
scoped instance instAlgebraFb : Algebra K (Fb K M) := inferInstance
scoped instance instFieldFH : Field (FH K M H) := inferInstance
scoped instance instAlgebraFH : Algebra K (FH K M H) := inferInstance

theorem FH_le_Fb : FH K M H ≤ Fb K M :=
  qExpFunctionFieldC_mono K (ModularCurve.GammaH_mono bot_le)

def incl : FH K M H →ₐ[K] Fb K M := IntermediateField.inclusion (FH_le_Fb H)

theorem coe_incl (y : FH K M H) : ((incl H y : Fb K M) : LaurentSeries K) = y :=
  IntermediateField.coe_inclusion (FH_le_Fb H) y

def xb (x : FH K M H) : Fb K M := ⟨(x : LaurentSeries K), FH_le_Fb H x.2⟩

theorem incl_x (x : FH K M H) : incl H x = xb H x := rfl

variable {Ω : Type*} [Field Ω] [Algebra K Ω] {Pt : Type*} [AddCommGroup Pt]
variable (x : FH K M H) (c : Ω)
variable (ρ : CongruenceSubgroup.Gamma0 M →* (Fb K M ≃ₐ[K] Fb K M))
variable (Ψ : {P : Pt // addOrderOf P = M} → {ψ : Fb K M →ₐ[K] Ω // ψ (xb H x) = c})

def res (ψ : Fb K M →ₐ[K] Ω) : FH K M H →ₐ[K] Ω := ψ.comp (incl H)

theorem res_apply (ψ : Fb K M →ₐ[K] Ω) (y : FH K M H) : res H ψ y = ψ (incl H y) := rfl

def pt (s : XH Pt M H) : {P : Pt // addOrderOf P = M} := ⟨s.2.choose, s.2.choose_spec.1⟩

theorem pt_spec (s : XH Pt M H) : s.1 = orb H (pt H s).1 := s.2.choose_spec.2

def PhiFun (s : XH Pt M H) : {φ : FH K M H →ₐ[K] Ω // φ x = c} :=
  ⟨res H (Ψ (pt H s)).1, by rw [res_apply, incl_x]; exact (Ψ (pt H s)).2⟩

theorem PhiFun_val (s : XH Pt M H) : (PhiFun H x c Ψ s).1 = res H (Ψ (pt H s)).1 := rfl

variable (hρH : ∀ y : Fb K M, (y : LaurentSeries K) ∈ FH K M H ↔
  ∀ γ : CongruenceSubgroup.Gamma0 M, (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H → ρ γ y = y)
variable (hdia : ∀ (γ : CongruenceSubgroup.Gamma0 M) (P P' : {P : Pt // addOrderOf P = M}),
  P'.1 = ((((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M).val) • P.1 →
    ((Ψ P').1 : Fb K M →ₐ[K] Ω) = ((Ψ P).1 : Fb K M →ₐ[K] Ω).comp (ρ γ : Fb K M →ₐ[K] Fb K M))
variable (hneg : ∀ P P' : {P : Pt // addOrderOf P = M}, P'.1 = -P.1 → Ψ P' = Ψ P)
variable (hfib : ∀ P P' : {P : Pt // addOrderOf P = M}, Ψ P' = Ψ P → P'.1 = P.1 ∨ P'.1 = -P.1)

include hρH in

theorem rho_incl (γ : CongruenceSubgroup.Gamma0 M) (hγ : (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H)
    (y : FH K M H) : ρ γ (incl H y) = incl H y :=
  (hρH (incl H y)).mp (by rw [coe_incl]; exact y.2) γ hγ

include hρH hdia in

theorem res_eq_of_unit (h : (ZMod M)ˣ) (hh : h ∈ H) (P P' : {P : Pt // addOrderOf P = M})
    (hP' : P'.1 = ((h : ZMod M).val) • P.1) : res H (Ψ P').1 = res H (Ψ P).1 := by
  obtain ⟨γ, hγa, hγd⟩ := exists_gamma0_diag M h
  have hγH : (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H :=
    mem_GammaH_of_gamma0Units_mem M γ
      (by rw [gamma0Units_eq_of_entry M γ h⁻¹ hγd]; exact H.inv_mem hh)
  have key := hdia γ P P' (by rw [hP', hγa])
  apply AlgHom.ext
  intro y
  rw [res_apply, res_apply, key, AlgHom.comp_apply, AlgEquiv.coe_algHom, rho_incl H ρ hρH γ hγH]

include hρH hdia hneg in

theorem res_eq_of_mem_orb (P P' : {P : Pt // addOrderOf P = M}) (hmem : P'.1 ∈ orb H P.1) :
    res H (Ψ P').1 = res H (Ψ P).1 := by
  obtain ⟨u, hu, hP'⟩ := hmem
  obtain ⟨h, hh, huh⟩ := exists_of_mem_Hpm H hu
  have hP0 := nsmul_of_addOrderOf_eq P.2
  rcases huh with rfl | rfl
  · exact res_eq_of_unit H x c ρ Ψ hρH hdia u hh P P' hP'
  · let Pm : {P : Pt // addOrderOf P = M} := ⟨-P.1, addOrderOf_neg_eq P.2⟩
    have hPm : P'.1 = ((h : ZMod M).val) • Pm.1 := by
      rw [hP', Units.val_mul, val_mul_nsmul hP0, Units.val_neg, Units.val_one, val_neg_one_nsmul hP0]
    rw [res_eq_of_unit H x c ρ Ψ hρH hdia h hh Pm P' hPm, hneg P Pm rfl]

include hρH hdia hneg in

theorem PhiFun_spec (P : {P : Pt // addOrderOf P = M}) (s : XH Pt M H) (hs : s.1 = orb H P.1) :
    (PhiFun H x c Ψ s).1 = res H (Ψ P).1 := by
  rw [PhiFun_val]
  apply res_eq_of_mem_orb H x c ρ Ψ hρH hdia hneg
  have h1 : orb H (pt H s).1 = orb H P.1 := (pt_spec H s).symm.trans hs
  have h2 := mem_orb_self H (nsmul_of_addOrderOf_eq (pt H s).2)
  rwa [h1] at h2

include hρH hdia hneg in

theorem PhiFun_natural (m : Pt →+ Pt) (hm : Function.Injective m) (τ : Ω →ₐ[K] Ω)
    (hΨ : ∀ P P' : {P : Pt // addOrderOf P = M}, P'.1 = m P.1 →
      ((Ψ P').1 : Fb K M →ₐ[K] Ω) = τ.comp (Ψ P).1)
    (s s' : XH Pt M H) (hs : s'.1 = m '' s.1) :
    ((PhiFun H x c Ψ s').1 : FH K M H →ₐ[K] Ω) = τ.comp (PhiFun H x c Ψ s).1 := by
  set P := pt H s with hP
  let Pm : {P : Pt // addOrderOf P = M} := ⟨m P.1, addOrderOf_map_eq hm P.2⟩
  have hs' : s'.1 = orb H Pm.1 := by rw [hs, pt_spec H s, image_orb]
  rw [PhiFun_spec H x c ρ Ψ hρH hdia hneg Pm s' hs', hΨ P Pm rfl, PhiFun_val]
  rfl

def GH : Subgroup (Fb K M ≃ₐ[K] Fb K M) :=
  ((CohCarrier.GammaH M H).comap (CongruenceSubgroup.Gamma0 M).subtype).map ρ

theorem mem_GH_iff (g : Fb K M ≃ₐ[K] Fb K M) :
    g ∈ GH H ρ ↔ ∃ γ : CongruenceSubgroup.Gamma0 M,
      (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H ∧ ρ γ = g := by
  simp only [GH, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype]

variable (hρbot : ∀ γ : CongruenceSubgroup.Gamma0 M, (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M ⊥ → ρ γ = 1)

include hρbot in

theorem finite_range : Finite (ρ.range) := by
  let N : Subgroup (CongruenceSubgroup.Gamma0 M) :=
    (CohCarrier.GammaH M ⊥).subgroupOf (CongruenceSubgroup.Gamma0 M)
  haveI : N.FiniteIndex := inferInstance
  have hN : N ≤ ρ.ker := by
    intro γ hγ
    rw [MonoidHom.mem_ker]
    exact hρbot γ (Subgroup.mem_subgroupOf.mp hγ)
  haveI : ρ.ker.FiniteIndex := Subgroup.finiteIndex_of_le hN
  haveI : Finite (CongruenceSubgroup.Gamma0 M ⧸ ρ.ker) := Subgroup.finite_quotient_of_finiteIndex
  exact Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange ρ).toEquiv

include hρbot in
theorem finite_GH : Finite (GH H ρ) := by
  haveI := finite_range ρ hρbot
  exact Finite.of_injective (Subgroup.inclusion (Subgroup.map_le_range ρ _))
    (Subgroup.inclusion_injective _)

theorem actGH_smul (g : GH H ρ) (y : Fb K M) : g • y = (g : Fb K M ≃ₐ[K] Fb K M) y := rfl

include hρH in
theorem forall_smul_eq_iff (y : Fb K M) :
    (∀ g : GH H ρ, g • y = y) ↔ (y : LaurentSeries K) ∈ FH K M H := by
  rw [hρH y]
  constructor
  · intro h γ hγ
    have := h ⟨ρ γ, (mem_GH_iff H ρ _).mpr ⟨γ, hγ, rfl⟩⟩
    rwa [actGH_smul] at this
  · intro h g
    obtain ⟨γ, hγ, hg⟩ := (mem_GH_iff H ρ _).mp g.2
    rw [actGH_smul, ← hg]
    exact h γ hγ

include hρH hdia hneg hfib hρbot in

theorem PhiFun_injective : Function.Injective (PhiFun H x c Ψ) := by
  intro s s' hss'
  haveI := finite_GH H ρ hρbot
  letI : Fintype (GH H ρ) := Fintype.ofFinite _
  set P := pt H s with hP
  set P' := pt H s' with hP'
  have hres : res H (Ψ P').1 = res H (Ψ P).1 := by
    rw [← PhiFun_val, ← PhiFun_val, hss']

  have hagree : ∀ y : Fb K M, (∀ g : GH H ρ, g • y = y) →
      ((Ψ P').1 : Fb K M →+* Ω) y = ((Ψ P).1 : Fb K M →+* Ω) y := by
    intro y hy
    have hyH : (y : LaurentSeries K) ∈ FH K M H := (forall_smul_eq_iff H ρ hρH y).mp hy
    have hyy : incl H ⟨(y : LaurentSeries K), hyH⟩ = y :=
      Subtype.ext ((coe_incl H ⟨(y : LaurentSeries K), hyH⟩).trans
        (rfl : (((⟨(y : LaurentSeries K), hyH⟩ : FH K M H) : LaurentSeries K)) = (y : LaurentSeries K)))
    have := congrArg (fun φ : FH K M H →ₐ[K] Ω => φ ⟨(y : LaurentSeries K), hyH⟩) hres
    simp only [res_apply, hyy] at this
    exact this
  obtain ⟨g, hg⟩ := exists_smul_of_forall_fixed ((Ψ P).1 : Fb K M →+* Ω) ((Ψ P').1 : Fb K M →+* Ω) hagree
  obtain ⟨γ, hγH, hγg⟩ := (mem_GH_iff H ρ _).mp g.2

  set a : (ZMod M)ˣ := (CohCarrier.gamma0Units M γ)⁻¹ with ha
  have haH : a ∈ H := H.inv_mem (gamma0Units_mem_of_mem M γ hγH)
  let Pa : {P : Pt // addOrderOf P = M} := ⟨((a : ZMod M).val) • P.1, addOrderOf_units_smul P.2 a⟩
  have hPa : ((Ψ Pa).1 : Fb K M →ₐ[K] Ω) = ((Ψ P).1 : Fb K M →ₐ[K] Ω).comp (ρ γ : Fb K M →ₐ[K] Fb K M) :=
    hdia γ P Pa rfl
  have hP'a : ((Ψ P').1 : Fb K M →ₐ[K] Ω) = ((Ψ P).1 : Fb K M →ₐ[K] Ω).comp (ρ γ : Fb K M →ₐ[K] Fb K M) := by
    apply AlgHom.ext
    intro y
    rw [AlgHom.comp_apply, AlgEquiv.coe_algHom, hγg]
    exact hg y
  have hΨeq : Ψ P' = Ψ Pa := Subtype.ext (hP'a.trans hPa.symm)
  have hP0 := nsmul_of_addOrderOf_eq P.2
  have hmemA : Pa.1 ∈ orb H P.1 := ⟨a, mem_Hpm_of_mem H haH, rfl⟩
  have hmem : P'.1 ∈ orb H P.1 := by
    rcases hfib Pa P' hΨeq with h1 | h1
    · rw [h1]; exact hmemA
    · rw [h1]; exact neg_mem_orb H hP0 hmemA
  apply XH.ext'
  rw [pt_spec H s, pt_spec H s', ← hP, ← hP']
  exact (orb_eq_of_mem H hP0 hmem).symm

end Descent

section Unique

open UpperHalfPlane

variable {K : Type*} [Field K] {M : ℕ} [NeZero M] (H : Subgroup (ZMod M)ˣ)

local notation "Γᴳ(" M ", " H ")" =>
  ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

local notation "Γ¹ᴳ(" M ")" =>
  ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γᴳ(M, H)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH M H)]
  exact AddSubgroup.mem_zmultiples 1

theorem slash_eq_self {k : ℤ} (a : ModularForm Γᴳ(M, H) k) {ε : SL(2, ℤ)}
    (hε : ε ∈ CohCarrier.GammaH M H) : (⇑a : ℍ → ℂ) ∣[k] ε = ⇑a := by
  rw [ModularForm.SL_slash]
  exact SlashInvariantFormClass.slash_action_eq a _ (Subgroup.mem_map_of_mem _ hε)

def liftForm {k : ℤ} (F : ModularForm Γ¹ᴳ(M) k)
    (hinv : ∀ δ ∈ CohCarrier.GammaH M H, (⇑F : ℍ → ℂ) ∣[k] δ = ⇑F) : ModularForm Γᴳ(M, H) k where
  toFun := F
  slash_action_eq' A hA := by
    obtain ⟨δ, hδ, rfl⟩ := hA
    have h := hinv δ hδ
    rw [ModularForm.SL_slash] at h
    exact h
  holo' := F.holo'
  bdd_at_cusps' {c} hc := F.bdd_at_cusps'
    ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mpr
      ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc))

@[scoped simp] theorem coe_liftForm {k : ℤ} (F : ModularForm Γ¹ᴳ(M) k)
    (hinv : ∀ δ ∈ CohCarrier.GammaH M H, (⇑F : ℍ → ℂ) ∣[k] δ = ⇑F) :
    (⇑(liftForm H F hinv) : ℍ → ℂ) = ⇑F := rfl

theorem exists_isIntegralQExp_pow_smul_slash {k : ℤ} (a : ModularForm Γᴳ(M, H) k) {pa : PowerSeries ℤ}
    (ha : IsIntegralQExp a pa) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    ∃ (n : ℕ) (f₁ : ModularForm Γᴳ(M, H) k) (p₁ : PowerSeries ℤ), IsIntegralQExp f₁ p₁ ∧
      (⇑f₁ : ℍ → ℂ) = ((M : ℂ) ^ n) • ((⇑a : ℍ → ℂ) ∣[k] γ) := by
  let a₁ : ModularForm Γ¹ᴳ(M) k := restrictForm (Subgroup.map_mono (ModularCurve.Gamma1_le_GammaH M H)) a
  obtain ⟨n, F, p₁, hF, hFeq⟩ :=
    ModularCurve.exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0 M a₁ ha γ hγ
  have hinv : ∀ δ ∈ CohCarrier.GammaH M H, (⇑F : ℍ → ℂ) ∣[k] δ = ⇑F := by
    intro δ hδ
    have hε : γ * δ * γ⁻¹ ∈ CohCarrier.GammaH M H := CohCarrier.conj_mem_GammaH M H ⟨γ, hγ⟩ ⟨δ, hδ⟩
    rw [hFeq, ModularForm.SL_smul_slash, coe_restrictForm, ← SlashAction.slash_mul,
      show γ * δ = (γ * δ * γ⁻¹) * γ by group, SlashAction.slash_mul, slash_eq_self H a hε]
  exact ⟨n, liftForm H F hinv, p₁, hF, hFeq⟩

theorem exists_intCast_smul {k : ℤ} (f : ModularForm Γᴳ(M, H) k) {p : PowerSeries ℤ}
    (hf : IsIntegralQExp f p) (c : ℤ) :
    ∃ f' : ModularForm Γᴳ(M, H) k, IsIntegralQExp f' (PowerSeries.C c * p) ∧
      (⇑f' : ℍ → ℂ) = (c : ℂ) • (⇑f : ℍ → ℂ) := by
  refine ⟨(c : ℝ) • f, ?_, ?_⟩
  · have h1 : (⇑((c : ℝ) • f) : ℍ → ℂ) = ((c : ℝ) : ℂ) • (⇑f : ℍ → ℂ) := by
      rw [ModularForm.coe_smul]
      funext τ
      simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul]
    rw [IsIntegralQExp, h1, ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods H) ((c : ℝ) : ℂ) f,
      ← hf, map_mul, PowerSeries.map_C, eq_intCast, PowerSeries.smul_eq_C_mul, Complex.ofReal_intCast]
  · rw [ModularForm.coe_smul]
    funext τ
    simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul, Complex.ofReal_intCast]

theorem intSeriesC_C_mul (c : ℤ) (p : PowerSeries ℤ) :
    intSeriesC K (PowerSeries.C c * p) = HahnSeries.C (c : K) * intSeriesC K p := by
  rw [intSeriesC_mul]
  congr 1
  rw [intSeriesC, PowerSeries.map_C, eq_intCast, HahnSeries.ofPowerSeries_C]

theorem div_mem {k : ℤ} (f g : ModularForm Γᴳ(M, H) k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) :
    intSeriesC K pf / intSeriesC K pg ∈ qExpFunctionFieldC K (CohCarrier.GammaH M H) := by
  by_cases h0 : intSeriesC K pg = 0
  · rw [h0, div_zero]; exact zero_mem _
  · exact div_mem_qExpFunctionFieldC f g hf hg h0

theorem symm_incl_eq (hMK : (M : K) ≠ 0)
    (ρH : CongruenceSubgroup.Gamma0 M →* (FH K M H ≃ₐ[K] FH K M H)) (hρH : IsDiamondPullbackModL K M H ρH)
    (ρ : CongruenceSubgroup.Gamma0 M →* (Fb K M ≃ₐ[K] Fb K M)) (hρ : IsDiamondPullbackModL K M ⊥ ρ)
    (γ : CongruenceSubgroup.Gamma0 M) (w : FH K M H) :
    (ρ γ).symm (incl H w) = incl H ((ρH γ).symm w) := by

  let E : IntermediateField K (FH K M H) :=
    { carrier := {y | (ρ γ).symm (incl H y) = incl H ((ρH γ).symm y)}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_mul] at *; rw [ha, hb]
      one_mem' := by simp only [Set.mem_setOf_eq, map_one]
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add] at *; rw [ha, hb]
      zero_mem' := by simp only [Set.mem_setOf_eq, map_zero]
      algebraMap_mem' := fun r => by
        simp only [Set.mem_setOf_eq, AlgHom.commutes, AlgEquiv.commutes]
      inv_mem' := fun a ha => by
        simp only [Set.mem_setOf_eq, map_inv₀] at *; rw [ha] }
  suffices hgen : intFormRatiosC K (CohCarrier.GammaH M H) ⊆
      (IntermediateField.lift E : Set (LaurentSeries K)) by
    have hle : FH K M H ≤ IntermediateField.lift E := IntermediateField.adjoin_le_iff.mpr hgen
    exact (IntermediateField.mem_lift w).mp (hle w.2)
  rintro z hz
  have hzH : z ∈ FH K M H := IntermediateField.subset_adjoin K _ hz
  obtain ⟨κ, a, b, pa, pb, ha, hb, hb0, rfl⟩ := hz
  refine (IntermediateField.mem_lift (⟨_, hzH⟩ : FH K M H)).mpr ?_
  change (ρ γ).symm (incl H ⟨_, hzH⟩) = incl H ((ρH γ).symm ⟨_, hzH⟩)

  obtain ⟨n₁, f₁, p₁, hf₁, hf₁eq⟩ := exists_isIntegralQExp_pow_smul_slash H a ha γ γ.2
  obtain ⟨n₂, g₁, p₂, hg₁, hg₁eq⟩ := exists_isIntegralQExp_pow_smul_slash H b hb γ γ.2
  set N : ℕ := n₁ + n₂ with hN
  obtain ⟨f₁', hf₁', hf₁'eq⟩ := exists_intCast_smul H f₁ hf₁ ((M : ℤ) ^ n₂)
  obtain ⟨g₁', hg₁', hg₁'eq⟩ := exists_intCast_smul H g₁ hg₁ ((M : ℤ) ^ n₁)
  obtain ⟨f, hf, hfeq⟩ := exists_intCast_smul H a ha ((M : ℤ) ^ N)
  obtain ⟨g, hg, hgeq⟩ := exists_intCast_smul H b hb ((M : ℤ) ^ N)
  have hMN : ∀ m₁ m₂ : ℕ, ((((M : ℤ) ^ m₁ : ℤ) : ℂ) • ((M : ℂ) ^ m₂ • ((⇑a : ℍ → ℂ) ∣[κ] (γ : SL(2, ℤ)))) : ℍ → ℂ) =
      ((((M : ℤ) ^ (m₂ + m₁) : ℤ) : ℂ) • (⇑a : ℍ → ℂ)) ∣[κ] (γ : SL(2, ℤ)) := by
    intro m₁ m₂
    rw [ModularForm.SL_smul_slash, smul_smul, Int.cast_pow, Int.cast_pow, Int.cast_natCast, ← pow_add, add_comm]
  have hfs : (⇑f₁' : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[κ] (γ : SL(2, ℤ)) := by
    rw [hf₁'eq, hf₁eq, hfeq, hN]; exact hMN n₂ n₁
  have hgs : (⇑g₁' : ℍ → ℂ) = (⇑g : ℍ → ℂ) ∣[κ] (γ : SL(2, ℤ)) := by
    have hMN' : ∀ m₁ m₂ : ℕ, ((((M : ℤ) ^ m₁ : ℤ) : ℂ) • ((M : ℂ) ^ m₂ • ((⇑b : ℍ → ℂ) ∣[κ] (γ : SL(2, ℤ)))) : ℍ → ℂ) =
        ((((M : ℤ) ^ (m₂ + m₁) : ℤ) : ℂ) • (⇑b : ℍ → ℂ)) ∣[κ] (γ : SL(2, ℤ)) := by
      intro m₁ m₂
      rw [ModularForm.SL_smul_slash, smul_smul, Int.cast_pow, Int.cast_pow, Int.cast_natCast, ← pow_add, add_comm]
    rw [hg₁'eq, hg₁eq, hgeq, hN, add_comm n₁ n₂]; exact hMN' n₁ n₂

  have hMK' : (HahnSeries.C (((M : ℤ) ^ N : ℤ) : K) : LaurentSeries K) ≠ 0 := by
    apply HahnSeries.C_ne_zero
    rw [Int.cast_pow, Int.cast_natCast]
    exact pow_ne_zero N hMK
  have hpg : intSeriesC K (PowerSeries.C ((M : ℤ) ^ N) * pb) ≠ 0 := by
    rw [intSeriesC_C_mul]; exact mul_ne_zero hMK' hb0
  have hratio : intSeriesC K (PowerSeries.C ((M : ℤ) ^ N) * pa) / intSeriesC K (PowerSeries.C ((M : ℤ) ^ N) * pb) =
      intSeriesC K pa / intSeriesC K pb := by
    rw [intSeriesC_C_mul, intSeriesC_C_mul, mul_div_mul_left _ _ hMK']

  set x₁ : FH K M H := ⟨_, div_mem H f₁' g₁' hf₁' hg₁'⟩ with hx₁

  have hH : ρH γ x₁ = ⟨_, hzH⟩ :=
    Subtype.ext ((hρH γ κ f g f₁' g₁' _ _ _ _ hf hg hf₁' hg₁' hfs hgs hpg x₁ rfl).trans hratio)

  have hle : ((CohCarrier.GammaH M ⊥ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ Γᴳ(M, H) :=
    Subgroup.map_mono (ModularCurve.GammaH_mono bot_le)
  have hB : ρ γ (incl H x₁) = incl H ⟨_, hzH⟩ := by
    apply Subtype.ext
    refine (hρ γ κ (restrictForm hle f) (restrictForm hle g) (restrictForm hle f₁') (restrictForm hle g₁')
      _ _ _ _ hf hg hf₁' hg₁' hfs hgs hpg (incl H x₁) (coe_incl H x₁)).trans ?_
    rw [coe_incl]
    exact hratio
  rw [← hB, ← hH, AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply]

theorem rho_incl_eq (hMK : (M : K) ≠ 0)
    (ρH : CongruenceSubgroup.Gamma0 M →* (FH K M H ≃ₐ[K] FH K M H)) (hρH : IsDiamondPullbackModL K M H ρH)
    (ρ : CongruenceSubgroup.Gamma0 M →* (Fb K M ≃ₐ[K] Fb K M)) (hρ : IsDiamondPullbackModL K M ⊥ ρ)
    (γ : CongruenceSubgroup.Gamma0 M) (y : FH K M H) :
    ρ γ (incl H y) = incl H (ρH γ y) := by
  have h := symm_incl_eq H hMK ρH hρH ρ hρ γ (ρH γ y)
  rw [AlgEquiv.symm_apply_apply] at h
  rw [← h, AlgEquiv.apply_symm_apply]

end Unique

end P2MKcDICTH
p2m_reactivate "P2MW.S_ModularCurve_exists_natural_diamond_algHom_qExpFunctionFieldC_gammaH_of_transcendental_j.P2MKcDICTH"

universe u v in

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0)
    (H : Subgroup (ZMod M)ˣ)
    (x : qExpFunctionFieldC K (CohCarrier.GammaH M H)) (hx : (x : LaurentSeries K) = jqModC K)
    (k Ω : Type v) [Field k] [Field Ω] [DecidableEq Ω] [Algebra K k] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower K k Ω] (E : WeierstrassCurve k) [E.IsElliptic]
    (hE : Transcendental K E.j)
    (hfull : Nat.card {P : (E.baseChange Ω).toAffine.Point // M • P = 0} = M ^ 2) :
    ∃ Ψ : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M} →
        {ψ : qExpFunctionFieldC K (CohCarrier.GammaH M H) →ₐ[K] Ω // ψ x = algebraMap k Ω E.j},
      (∀ (σ : Ω ≃ₐ[k] Ω) (P P' : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M}),
        P'.1 = WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P.1 →
          ((Ψ P').1 : qExpFunctionFieldC K (CohCarrier.GammaH M H) →ₐ[K] Ω) =
            ((σ : Ω →ₐ[k] Ω).restrictScalars K).comp (Ψ P).1) ∧
      (∀ (ρ : CongruenceSubgroup.Gamma0 M →*
          (qExpFunctionFieldC K (CohCarrier.GammaH M H) ≃ₐ[K]
            qExpFunctionFieldC K (CohCarrier.GammaH M H))),
        IsDiamondPullbackModL K M H ρ →
        ∀ (γ : CongruenceSubgroup.Gamma0 M)
          (P P' : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M}),
          P'.1 = ((((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M).val) • P.1 →
            ((Ψ P').1 : qExpFunctionFieldC K (CohCarrier.GammaH M H) →ₐ[K] Ω) =
              ((Ψ P).1 : qExpFunctionFieldC K (CohCarrier.GammaH M H) →ₐ[K] Ω).comp
                (ρ γ : qExpFunctionFieldC K (CohCarrier.GammaH M H) →ₐ[K]
                  qExpFunctionFieldC K (CohCarrier.GammaH M H))) ∧
      (∀ (u : (ZMod M)ˣ) (P P' : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M}),
        u ∈ H ⊔ Subgroup.zpowers (-1) → P'.1 = (u : ZMod M).val • P.1 → Ψ P' = Ψ P) ∧
      (∀ P P' : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M},
        Ψ P' = Ψ P → ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧
          P'.1 = (u : ZMod M).val • P.1) ∧
      (∀ ψ : qExpFunctionFieldC K (CohCarrier.GammaH M H) →ₐ[K] Ω,
        ψ x = algebraMap k Ω E.j →
          ∃ P : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M},
            ((Ψ P).1 : qExpFunctionFieldC K (CohCarrier.GammaH M H) →ₐ[K] Ω) = ψ) := by
  classical

  have hMk : (M : k) ≠ 0 := fun h => hM <| (algebraMap K k).injective (by
    rw [map_natCast, map_zero]; exact h)

  have hxb : ((P2MKcDICTH.xb H x : P2MKcDICTH.Fb K M) : LaurentSeries K) = jqModC K :=
    (Subtype.coe_mk _ _).trans hx

  obtain ⟨Ψ, hnat, hdia, hneg, hfib⟩ :=
    ModularCurve.exists_natural_diamond_algHom_qExpFunctionFieldC_gammaH_bot_of_transcendental_j
      K M hM (P2MKcDICTH.xb H x) hxb k Ω E hE hfull

  obtain ⟨ρ, hρ, hρfix⟩ :=
    ModularCurve.exists_isDiamondPullbackModL_bot_forall_coe_mem_gammaH_iff K M hM
  have hρbot : ∀ γ : CongruenceSubgroup.Gamma0 M,
      (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M ⊥ → ρ γ = 1 := fun γ hγ =>
    AlgEquiv.ext fun y => (hρfix ⊥ y).mp y.2 γ hγ
  have hρH := hρfix H
  have hdia' := hdia ρ hρ

  have hinj := P2MKcDICTH.PhiFun_injective H x (algebraMap k Ω E.j) ρ Ψ hρH hdia' hneg hfib hρbot

  let cls : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M} →
      P2MKcDICTH.XH (E.baseChange Ω).toAffine.Point M H :=
    fun R => ⟨P2MKcDICTH.orb H R.1, R.1, R.2, rfl⟩
  have hcls : ∀ R, (P2MKcDICTH.PhiFun H x (algebraMap k Ω E.j) Ψ (cls R)).1 = P2MKcDICTH.res H (Ψ R).1 :=
    fun R => P2MKcDICTH.PhiFun_spec H x (algebraMap k Ω E.j) ρ Ψ hρH hdia' hneg R (cls R) rfl

  let ΨH : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M} →
      {ψ : qExpFunctionFieldC K (CohCarrier.GammaH M H) →ₐ[K] Ω // ψ x = (algebraMap k Ω E.j)} :=
    fun R => ⟨P2MKcDICTH.res H (Ψ R).1, (Ψ R).2⟩
  have hΨH : ∀ R, (ΨH R).1 = P2MKcDICTH.res H (Ψ R).1 := fun R => rfl
  refine ⟨ΨH, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro σ R R' h
    apply AlgHom.ext
    intro y
    show (Ψ R').1 (P2MKcDICTH.incl H y) = σ ((Ψ R).1 (P2MKcDICTH.incl H y))
    rw [hnat σ R R' h]
    rfl
  ·
    intro ρH hρH' γ R R' h
    apply AlgHom.ext
    intro y
    show (Ψ R').1 (P2MKcDICTH.incl H y) = (Ψ R).1 (P2MKcDICTH.incl H (ρH γ y))
    rw [hdia' γ R R' h, AlgHom.comp_apply, AlgEquiv.coe_algHom]
    exact congrArg ((Ψ R).1 : P2MKcDICTH.Fb K M →ₐ[K] Ω) (P2MKcDICTH.rho_incl_eq H hM ρH hρH' ρ hρ γ y)
  ·
    intro u R R' hu h
    exact Subtype.ext (P2MKcDICTH.res_eq_of_mem_orb H x (algebraMap k Ω E.j) ρ Ψ hρH hdia' hneg R R' ⟨u, hu, h⟩)
  ·
    intro R R' h
    have h1 : P2MKcDICTH.PhiFun H x (algebraMap k Ω E.j) Ψ (cls R') = P2MKcDICTH.PhiFun H x (algebraMap k Ω E.j) Ψ (cls R) := by
      apply Subtype.ext
      rw [hcls, hcls, ← hΨH, ← hΨH, h]
    have h2 : (cls R').1 = (cls R).1 := congrArg Subtype.val (hinj h1)
    have h3 : R'.1 ∈ P2MKcDICTH.orb H R.1 := by
      change R'.1 ∈ (cls R).1
      rw [← h2]
      exact P2MKcDICTH.mem_orb_self H (P2MKcDICTH.nsmul_of_addOrderOf_eq R'.2)
    obtain ⟨u, hu, hu'⟩ := h3
    exact ⟨u, hu, hu'⟩
  ·
    intro ψ hψ
    obtain ⟨hfd, hdeg⟩ :=
      ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index K
        (CohCarrier.GammaH M H) (translation_mem_GammaH M H)
        (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)) le_sup_left
        (fun γ hγ => P2MKcDICTH.mem_or_neg_mem_of_mem_sup _ γ hγ) x hx
    haveI := hfd
    obtain ⟨hfinNE, hcardNE⟩ := P2MKcDICTH.finite_and_natCard_normalised_le (K := K) x (algebraMap k Ω E.j)
    obtain ⟨e⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_natCard_torsion_eq_sq
      E M hMk hfull
    have hcardX := AddCommGroup.natCard_torsionOrbit_gammaH_eq_index M H e
    haveI : (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)).FiniteIndex :=
      Subgroup.finiteIndex_of_le le_sup_left
    have hidx : (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)).index ≠ 0 :=
      Subgroup.FiniteIndex.index_ne_zero
    haveI : Finite (P2MKcDICTH.XH (E.baseChange Ω).toAffine.Point M H) :=
      Nat.finite_of_card_ne_zero (by rw [hcardX]; exact hidx)
    haveI : Finite {φ : P2MKcDICTH.FH K M H →ₐ[K] Ω // φ x = (algebraMap k Ω E.j)} := hfinNE
    have hle : Nat.card {φ : P2MKcDICTH.FH K M H →ₐ[K] Ω // φ x = (algebraMap k Ω E.j)} ≤
        Nat.card (P2MKcDICTH.XH (E.baseChange Ω).toAffine.Point M H) := by
      rw [hcardX]
      exact hcardNE.trans hdeg
    have hbij := hinj.bijective_of_nat_card_le hle
    obtain ⟨s, hs⟩ := hbij.2 ⟨ψ, hψ⟩
    refine ⟨P2MKcDICTH.pt H s, ?_⟩
    rw [hΨH, ← P2MKcDICTH.PhiFun_val, hs]

end
p2m_reactivate "P2MW.S_ModularCurve_exists_natural_diamond_algHom_qExpFunctionFieldC_gammaH_of_transcendental_j.P2MKcDICTH"

end S_ModularCurve_exists_natural_diamond_algHom_qExpFunctionFieldC_gammaH_of_transcendental_j
end P2MW
export P2MW.S_ModularCurve_exists_natural_diamond_algHom_qExpFunctionFieldC_gammaH_of_transcendental_j (solution)
