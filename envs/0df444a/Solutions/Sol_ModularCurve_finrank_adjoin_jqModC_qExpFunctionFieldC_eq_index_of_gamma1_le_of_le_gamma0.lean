-- Prove2me | solution 1 for ModularCurve.finrank_adjoin_jqModC_qExpFunctionFieldC_eq_index_of_gamma1_le_of_le_gamma0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/4ee4500f-9245-5c8e-a5c8-85b1a0285d0d

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_X1
import Theorems.Thm_ModularCurve_exists_natural_diamond_algHom_qExpFunctionFieldC_gammaH_of_transcendental_j
import Theorems.Thm_CohCarrier_exists_eq_gammaH_of_gamma1_le_of_le_gamma0
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Theorems.Thm_AddCommGroup_natCard_torsionOrbit_gammaH_eq_index
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finrank_adjoin_jqModC_qExpFunctionFieldC_eq_index_of_gamma1_le_of_le_gamma0
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

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

p2m_open "WeierstrassCurve~cusp WeierstrassCurve.Affine ModularCurve"
open scoped MatrixGroups

namespace IgusaDegXH

section Orb

variable {A : Type*} [AddCommGroup A] {M : ℕ} [NeZero M]

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

variable (H : Subgroup (ZMod M)ˣ)

abbrev orb (P : A) : Set A :=
  {T | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧ T = (u : ZMod M).val • P}

abbrev XH (A : Type*) [AddCommGroup A] (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Type _ :=
  {s : Set A // ∃ P : A, addOrderOf P = M ∧ s = orb H P}

theorem neg_one_mem_Hpm : (-1 : (ZMod M)ˣ) ∈ H ⊔ Subgroup.zpowers (-1) :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

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

variable {H}

theorem XH.ext' {s s' : XH A M H} (h : s.1 = s'.1) : s = s' := Subtype.ext h

variable (H)

def pt (s : XH A M H) : {P : A // addOrderOf P = M} := ⟨s.2.choose, s.2.choose_spec.1⟩

theorem pt_spec (s : XH A M H) : s.1 = orb H (pt H s).1 := s.2.choose_spec.2

end Orb

section Count

theorem finite_and_natCard_le_of_mk_le {X : Type*} {n : ℕ} (h : Cardinal.mk X ≤ n) :
    Finite X ∧ Nat.card X ≤ n := by
  have hfin : Cardinal.mk X < Cardinal.aleph0 := lt_of_le_of_lt h Cardinal.natCast_lt_aleph0
  haveI : Finite X := Cardinal.lt_aleph0_iff_finite.mp hfin
  refine ⟨this, ?_⟩
  have := Cardinal.toNat_le_toNat h Cardinal.natCast_lt_aleph0
  first | simpa using this | (rw [Cardinal.toNat_natCast] at this; exact this)

theorem finite_and_natCard_algHom_le (L F Ω : Type*) [Field L] [Field F] [Field Ω] [Algebra L F]
    [Algebra L Ω] [FiniteDimensional L F] :
    Finite (F →ₐ[L] Ω) ∧ Nat.card (F →ₐ[L] Ω) ≤ Module.finrank L F := by
  have h := cardinalMk_algHom L F Ω
  rw [Module.finrank_linearMap_self L Ω F] at h
  exact finite_and_natCard_le_of_mk_le h

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

section Main

variable {K F Ω : Type*} [Field K] [Field F] [Field Ω] [Algebra K F] [Algebra K Ω]
variable {M : ℕ} [NeZero M] {Pt : Type*} [AddCommGroup Pt]

def Phi (H : Subgroup (ZMod M)ˣ) (x : F) (c : Ω)
    (Ψ : {P : Pt // addOrderOf P = M} → {ψ : F →ₐ[K] Ω // ψ x = c})
    (s : XH Pt M H) : {ψ : F →ₐ[K] Ω // ψ x = c} :=
  Ψ (pt H s)

theorem Phi_injective (H : Subgroup (ZMod M)ˣ) (x : F) (c : Ω)
    (Ψ : {P : Pt // addOrderOf P = M} → {ψ : F →ₐ[K] Ω // ψ x = c})
    (hsep : ∀ P P' : {P : Pt // addOrderOf P = M}, Ψ P' = Ψ P →
      ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧ P'.1 = (u : ZMod M).val • P.1) :
    Function.Injective (Phi H x c Ψ) := by
  intro s s' hss'
  have hP0 : M • (pt H s).1 = 0 := nsmul_of_addOrderOf_eq (pt H s).2

  have hmem : (pt H s').1 ∈ orb H (pt H s).1 := by
    obtain ⟨u, hu, h1⟩ := hsep (pt H s) (pt H s') hss'.symm
    exact ⟨u, hu, h1⟩
  apply XH.ext'
  rw [pt_spec H s, pt_spec H s']
  exact (orb_eq_of_mem H hP0 hmem).symm

theorem index_le_finrank_of_separating (H : Subgroup (ZMod M)ˣ)
    (e : ZMod M × ZMod M ≃+ Submodule.torsionBy ℤ Pt M)
    (x : F) (c : Ω) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (Ψ : {P : Pt // addOrderOf P = M} → {ψ : F →ₐ[K] Ω // ψ x = c})
    (hsep : ∀ P P' : {P : Pt // addOrderOf P = M}, Ψ P' = Ψ P →
      ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧ P'.1 = (u : ZMod M).val • P.1) :
    (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)).index ≤
      Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F := by
  classical

  have hcardX := AddCommGroup.natCard_torsionOrbit_gammaH_eq_index M H e

  obtain ⟨hfinNE, hcardNE⟩ := finite_and_natCard_normalised_le (K := K) x c
  haveI : Finite {ψ : F →ₐ[K] Ω // ψ x = c} := hfinNE

  have hinj := Phi_injective H x c Ψ hsep
  have h1 : Nat.card (XH Pt M H) ≤ Nat.card {ψ : F →ₐ[K] Ω // ψ x = c} :=
    Nat.card_le_card_of_injective _ hinj
  rw [hcardX] at h1
  exact h1.trans hcardNE

end Main

section Carrier

variable (K : Type*) [Field K] (M : ℕ) (H : Subgroup (ZMod M)ˣ)

def Fb : IntermediateField K (LaurentSeries K) :=
  qExpFunctionFieldC K (CohCarrier.GammaH M H)

theorem Fb_eq : Fb K M H = qExpFunctionFieldC K (CohCarrier.GammaH M H) := rfl

scoped instance instFieldFb : Field (Fb K M H) := inferInstance
scoped instance instAlgebraFb : Algebra K (Fb K M H) := inferInstance
scoped instance instIsScalarTowerFb : IsScalarTower K (Fb K M H) (Fb K M H) := IsScalarTower.right
scoped instance instAlgebraFbClosure : Algebra K (AlgebraicClosure (Fb K M H)) := inferInstance
scoped instance instIsScalarTowerFbClosure :
    IsScalarTower K (Fb K M H) (AlgebraicClosure (Fb K M H)) := inferInstance

variable {K M H}

theorem transcendental_of_coe_eq_jqModC (x : Fb K M H) (hx : (x : LaurentSeries K) = jqModC K) :
    Transcendental K x := by
  have hinj : Function.Injective (algebraMap (Fb K M H) (LaurentSeries K)) :=
    FaithfulSMul.algebraMap_injective _ _
  have h : Transcendental K (algebraMap (Fb K M H) (LaurentSeries K) x) := by
    rw [IntermediateField.algebraMap_apply, hx]
    exact transcendental_jqModC K
  exact (transcendental_algebraMap_iff hinj).mp h

theorem natCard_torsion_eq_sq_of_addEquiv {Pt : Type*} [AddCommGroup Pt] [NeZero M]
    (e : ZMod M × ZMod M ≃+ Submodule.torsionBy ℤ Pt M) :
    Nat.card {P : Pt // M • P = 0} = M ^ 2 := by
  have h1 : Nat.card {P : Pt // M • P = 0} = Nat.card (Submodule.torsionBy ℤ Pt M) := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight fun P => ?_
    rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
  rw [h1, ← Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zmod, sq]

end Carrier

section Lower

open IgusaDegXH

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem index_le_finrank
    (K : Type*) [Field K] [IsAlgClosed K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0) (H : Subgroup (ZMod M)ˣ)
    (x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H))
    (hx : (x : LaurentSeries K) = ModularCurve.jqModC K) :
    (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)).index ≤
      Module.finrank
        (IntermediateField.adjoin K
          ({x} : Set (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H))))
        (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)) := by
  classical
  change (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)).index ≤
    Module.finrank (IntermediateField.adjoin K ({(x : Fb K M H)} : Set (Fb K M H))) (Fb K M H)
  haveI : (CohCarrier.GammaH M H).FiniteIndex :=
    Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)
  obtain ⟨hfd, -⟩ :=
    ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index K
      (CohCarrier.GammaH M H) (ModularCurve.translation_mem_GammaH M H)
      (CohCarrier.GammaH M H) le_rfl (fun γ hγ => Or.inl hγ) x hx
  haveI := hfd
  haveI : FiniteDimensional (IntermediateField.adjoin K ({(x : Fb K M H)} : Set (Fb K M H))) (Fb K M H) :=
    hfd
  let E : WeierstrassCurve (Fb K M H) := WeierstrassCurve.ofJ (x : Fb K M H)
  have hEj : E.j = (x : Fb K M H) := WeierstrassCurve.ofJ_j _
  have hE : Transcendental K E.j := by
    rw [hEj]
    exact transcendental_of_coe_eq_jqModC (x : Fb K M H) hx
  have hMΩ : (M : AlgebraicClosure (Fb K M H)) ≠ 0 := by
    intro h
    apply hM
    apply (algebraMap K (AlgebraicClosure (Fb K M H))).injective
    rw [map_natCast, map_zero, h]
  obtain ⟨e⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
    (K := AlgebraicClosure (Fb K M H)) E hMΩ
  have hfull : Nat.card {P : (E.baseChange (AlgebraicClosure (Fb K M H))).toAffine.Point // M • P = 0}
      = M ^ 2 := natCard_torsion_eq_sq_of_addEquiv e

  obtain ⟨Ψ, -, -, -, hsep, -⟩ :=
    ModularCurve.exists_natural_diamond_algHom_qExpFunctionFieldC_gammaH_of_transcendental_j
      K M hM H (x : Fb K M H) hx (Fb K M H) (AlgebraicClosure (Fb K M H)) E hE hfull
  exact index_le_finrank_of_separating (F := Fb K M H) H e (x : Fb K M H)
    (algebraMap (Fb K M H) (AlgebraicClosure (Fb K M H)) E.j) Ψ hsep

end Lower

end IgusaDegXH
p2m_reactivate "P2MW.S_ModularCurve_finrank_adjoin_jqModC_qExpFunctionFieldC_eq_index_of_gamma1_le_of_le_gamma0.IgusaDegXH"

end
p2m_reactivate "P2MW.S_ModularCurve_finrank_adjoin_jqModC_qExpFunctionFieldC_eq_index_of_gamma1_le_of_le_gamma0.IgusaDegXH"

open scoped MatrixGroups

namespace IgusaDegGrp

section PM

variable {G : Type*} [Group G]

theorem mem_or_mul_mem_of_mem_sup_zpowers (H : Subgroup G) {z : G} (hz : z ∈ Subgroup.center G)
    (hz2 : z * z = 1) {g : G} (hg : g ∈ H ⊔ Subgroup.zpowers z) : g ∈ H ∨ g * z ∈ H := by
  have hcomm : ∀ g : G, g * z = z * g := fun g => (Subgroup.mem_center_iff.mp hz g)
  let K : Subgroup G :=
    { carrier := {g | g ∈ H ∨ g * z ∈ H}
      one_mem' := Or.inl H.one_mem
      mul_mem' := by
        rintro x y (hx | hx) (hy | hy)
        · exact Or.inl (H.mul_mem hx hy)
        · refine Or.inr ?_
          rw [mul_assoc]
          exact H.mul_mem hx hy
        · refine Or.inr ?_
          rw [mul_assoc, hcomm y, ← mul_assoc]
          exact H.mul_mem hx hy
        · refine Or.inl ?_
          have : x * y = (x * z) * (y * z) := by
            rw [mul_assoc, ← mul_assoc z, ← hcomm y, mul_assoc y, hz2, mul_one]
          rw [this]
          exact H.mul_mem hx hy
      inv_mem' := by
        rintro x (hx | hx)
        · exact Or.inl (H.inv_mem hx)
        · refine Or.inr ?_
          have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
          have : x⁻¹ * z = (x * z)⁻¹ := by rw [mul_inv_rev, hzinv, hcomm]
          rw [this]
          exact H.inv_mem hx }
  have hle : H ⊔ Subgroup.zpowers z ≤ K := by
    refine sup_le (fun g hg => Or.inl hg) ?_
    rw [Subgroup.zpowers_le]
    exact Or.inr (by rw [hz2]; exact H.one_mem)
  exact hle hg

end PM
p2m_reactivate "P2MW.S_ModularCurve_finrank_adjoin_jqModC_qExpFunctionFieldC_eq_index_of_gamma1_le_of_le_gamma0.IgusaDegXH"

theorem negOne_mem_center : (-1 : SL(2, ℤ)) ∈ Subgroup.center SL(2, ℤ) := by
  rw [Subgroup.mem_center_iff]
  intro g
  rw [mul_neg_one, neg_one_mul]

theorem mem_sup_zpowers_negOne_iff (Γ : Subgroup SL(2, ℤ)) (x : SL(2, ℤ)) :
    x ∈ Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) ↔ x ∈ Γ ∨ -x ∈ Γ := by
  constructor
  · intro hx
    rcases mem_or_mul_mem_of_mem_sup_zpowers Γ negOne_mem_center (by rw [neg_one_mul, neg_neg]) hx with h | h
    · exact Or.inl h
    · right; rwa [mul_neg_one] at h
  · rintro (h | h)
    · exact Subgroup.mem_sup_left h
    · have : x = -x * (-1 : SL(2, ℤ)) := by rw [mul_neg_one, neg_neg]
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h) (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

end IgusaDegGrp
p2m_reactivate "P2MW.S_ModularCurve_finrank_adjoin_jqModC_qExpFunctionFieldC_eq_index_of_gamma1_le_of_le_gamma0.IgusaDegXH"

open IgusaDegXH in
theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (L : ℕ) [NeZero L] (hL : (L : K) ≠ 0)
    (Γ : Subgroup SL(2, ℤ))
    (hΓ₁ : CongruenceSubgroup.Gamma1 L ≤ Γ) (hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 L)
    (x : ModularCurve.qExpFunctionFieldC K Γ)
    (hx : (x : LaurentSeries K) = ModularCurve.jqModC K) :
    Module.finrank
        (IntermediateField.adjoin K ({x} : Set (ModularCurve.qExpFunctionFieldC K Γ)))
        (ModularCurve.qExpFunctionFieldC K Γ) =
      (Γ ⊔ Subgroup.zpowers (-1)).index := by
  classical
  obtain ⟨H, rfl⟩ := CohCarrier.exists_eq_gammaH_of_gamma1_le_of_le_gamma0 L Γ hΓ₁ hΓ₀
  apply le_antisymm
  · haveI : (CohCarrier.GammaH L H).FiniteIndex :=
      Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH L H)
    exact (ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index K
      (CohCarrier.GammaH L H) (ModularCurve.translation_mem_GammaH L H)
      (CohCarrier.GammaH L H ⊔ Subgroup.zpowers (-1)) le_sup_left
      (fun γ hγ => (IgusaDegGrp.mem_sup_zpowers_negOne_iff _ γ).mp hγ) x hx).2
  · exact IgusaDegXH.index_le_finrank K L hL H x hx

end S_ModularCurve_finrank_adjoin_jqModC_qExpFunctionFieldC_eq_index_of_gamma1_le_of_le_gamma0
end P2MW
export P2MW.S_ModularCurve_finrank_adjoin_jqModC_qExpFunctionFieldC_eq_index_of_gamma1_le_of_le_gamma0 (solution)
