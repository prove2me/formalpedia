-- Prove2me | solution 1 for ModularCurve.ord_census_qExpFunctionFieldC_gammaH_of_char_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/57c2d529-38ad-5c2c-9e1d-ef3235acb95f

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_ModularCurve_exists_orbitMap_torsionOrbit_places_qExpFunctionFieldC_gammaH
import Theorems.Thm_WeierstrassCurve_natCard_torsionOrbit_and_exists_surjective_doubleCoset_of_char_two
import Theorems.Thm_MulAction_natCard_fixedBy_of_isPretransitive_of_card_eq_twelve
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_census_qExpFunctionFieldC_gammaH_of_char_two
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ"
p2m_attr_erase "simp" "ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP"
p2m_attr_erase "simp" "ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_zero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11"
p2m_attr_erase "simp" "CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open WeierstrassCurve WeierstrassCurve.Affine

namespace P2MKcCENH2

section CharTwo

variable {K : Type*} [Field K] [CharP K 2]

theorem two_eq_zero : (2 : K) = 0 := by
  simpa using CharP.cast_eq_zero K 2

theorem three_eq_one : (3 : K) = 1 := by
  have : (3 : K) = 2 + 1 := by norm_num
  rw [this, two_eq_zero, zero_add]

theorem neg_eq (a : K) : -a = a := by
  have h : a + a = 0 := by rw [← two_mul, two_eq_zero, zero_mul]
  exact (neg_eq_of_add_eq_zero_left h)

theorem sub_eq_add' (a b : K) : a - b = a + b := by
  rw [sub_eq_add_neg, neg_eq]

theorem add_self (a : K) : a + a = 0 := by
  rw [← two_mul, two_eq_zero, zero_mul]

theorem sq_add (a b : K) : (a + b) ^ 2 = a ^ 2 + b ^ 2 := by
  have : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * (a * b) := by ring
  rw [this, two_eq_zero, zero_mul, add_zero]

theorem sq_add_self_eq_zero_iff (x : K) : x ^ 2 + x = 0 ↔ x = 0 ∨ x = 1 := by
  constructor
  · intro h
    have : x * (x + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h0 | h1
    · exact Or.inl h0
    · right
      have := neg_eq (1 : K)
      linear_combination h1 + this
  · rintro (rfl | rfl)
    · ring
    · have := add_self (1 : K); simpa [sq] using this

variable (ω : K) (hω : ω ^ 2 + ω + 1 = 0)
include hω

theorem omega_pow_three : ω ^ 3 = 1 := by
  have h1 : (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
  rw [hω, mul_zero] at h1
  linear_combination -h1

theorem omega_ne_one : ω ≠ 1 := by
  intro h
  rw [h] at hω
  have : (3 : K) = 0 := by linear_combination hω
  rw [three_eq_one] at this
  exact one_ne_zero this

theorem omega_ne_zero : ω ≠ 0 := by
  intro h
  rw [h] at hω
  simp at hω

theorem omega_sq : ω ^ 2 = ω + 1 := by
  have h1 := neg_eq ω
  have h2 := neg_eq (1 : K)
  linear_combination hω + h1 + h2

theorem sq_add_self_add_one_eq_zero_iff (x : K) : x ^ 2 + x + 1 = 0 ↔ x = ω ∨ x = ω + 1 := by
  constructor
  · intro h
    have : (x + ω) * (x + ω + 1) = 0 := by
      have h2 := two_eq_zero (K := K)
      linear_combination h + hω + (x * ω - 1) * h2
    rcases mul_eq_zero.mp this with h0 | h1
    · left
      have := neg_eq ω
      linear_combination h0 + this
    · right
      have := neg_eq (ω + 1)
      linear_combination h1 + this
  · rintro (rfl | rfl)
    · exact hω
    · have h2 := two_eq_zero (K := K)
      linear_combination hω + (ω + 1) * h2

end CharTwo

section Curve

variable (K : Type*) [Field K] [CharP K 2]

def E₀ : WeierstrassCurve K := ⟨0, 0, 1, 0, 0⟩

@[scoped simp] theorem E₀_a₁ : (E₀ K).a₁ = 0 := rfl
@[scoped simp] theorem E₀_a₂ : (E₀ K).a₂ = 0 := rfl
@[scoped simp] theorem E₀_a₃ : (E₀ K).a₃ = 1 := rfl
@[scoped simp] theorem E₀_a₄ : (E₀ K).a₄ = 0 := rfl
@[scoped simp] theorem E₀_a₆ : (E₀ K).a₆ = 0 := rfl

theorem E₀_Δ : (E₀ K).Δ = 1 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, E₀_a₁, E₀_a₂, E₀_a₃, E₀_a₄, E₀_a₆]
  have h2 := two_eq_zero (K := K)
  linear_combination (-14 : K) * h2

scoped instance E₀_isElliptic : (E₀ K).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, E₀_Δ]; exact isUnit_one

theorem E₀_c₄ : (E₀ K).c₄ = 0 := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, E₀_a₁, E₀_a₂, E₀_a₃,
    E₀_a₄]
  ring

theorem E₀_j : (E₀ K).j = 0 := by
  rw [WeierstrassCurve.j, E₀_c₄]; ring

variable {K}

theorem smul_E₀_eq_iff (γ : VariableChange K) :
    γ • E₀ K = E₀ K ↔
      (γ.u : K) ^ 3 = 1 ∧ γ.r = γ.s ^ 2 ∧ γ.s ^ 4 = γ.s ∧ γ.t ^ 2 + γ.t = γ.s ^ 3 := by
  have h2 := two_eq_zero (K := K)
  have h3 := three_eq_one (K := K)
  have hu : (γ.u : K) ≠ 0 := γ.u.ne_zero
  have hui : ((γ.u⁻¹ : Kˣ) : K) * (γ.u : K) = 1 := by simp
  have hv : ((γ.u⁻¹ : Kˣ) : K) ≠ 0 := (γ.u⁻¹).ne_zero
  constructor
  · intro h
    have e₂ := congrArg WeierstrassCurve.a₂ h
    have e₃ := congrArg WeierstrassCurve.a₃ h
    have e₄ := congrArg WeierstrassCurve.a₄ h
    have e₆ := congrArg WeierstrassCurve.a₆ h
    simp only [E₀, variableChange_a₂, variableChange_a₃, variableChange_a₄, variableChange_a₆] at e₂ e₃ e₄ e₆

    have hv3 : ((γ.u⁻¹ : Kˣ) : K) ^ 3 = 1 := by
      linear_combination e₃ - ((γ.u⁻¹ : Kˣ) : K) ^ 3 * γ.t * h2
    have hu3 : (γ.u : K) ^ 3 = 1 := by
      have : ((γ.u⁻¹ : Kˣ) : K) ^ 3 * (γ.u : K) ^ 3 = 1 := by rw [← mul_pow, hui, one_pow]
      rwa [hv3, one_mul] at this

    have hr : γ.r = γ.s ^ 2 := by
      have : ((γ.u⁻¹ : Kˣ) : K) ^ 2 * ((3 : K) * γ.r - γ.s ^ 2) = 0 := by linear_combination e₂
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0) hv
      · rw [h3, one_mul, sub_eq_zero] at h0
        exact h0

    have hs : γ.s ^ 4 = γ.s := by
      have : ((γ.u⁻¹ : Kˣ) : K) ^ 4 * (-γ.s + (3 : K) * γ.r ^ 2 - 2 * γ.s * γ.t) = 0 := by
        linear_combination e₄
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd (pow_eq_zero_iff (n := 4) (by norm_num) |>.mp h0) hv
      · rw [h3, h2, hr] at h0
        linear_combination h0

    have ht : γ.t ^ 2 + γ.t = γ.s ^ 3 := by
      have : ((γ.u⁻¹ : Kˣ) : K) ^ 6 * (γ.r ^ 3 - γ.t - γ.t ^ 2) = 0 := by linear_combination e₆
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd (pow_eq_zero_iff (n := 6) (by norm_num) |>.mp h0) hv
      · rw [hr] at h0
        have e : (γ.s ^ 2) ^ 3 = γ.s ^ 4 * γ.s ^ 2 := by ring
        rw [e, hs] at h0
        linear_combination -h0
    exact ⟨hu3, hr, hs, ht⟩
  · rintro ⟨hu3, hr, hs, ht⟩
    have hv3 : ((γ.u⁻¹ : Kˣ) : K) ^ 3 = 1 := by
      have : ((γ.u⁻¹ : Kˣ) : K) ^ 3 * (γ.u : K) ^ 3 = 1 := by rw [← mul_pow, hui, one_pow]
      rwa [hu3, mul_one] at this
    have hs3 : γ.s ^ 6 = γ.s ^ 3 := by
      calc γ.s ^ 6 = γ.s ^ 4 * γ.s ^ 2 := by ring
        _ = γ.s ^ 3 := by rw [hs]; ring
    have hns := neg_eq γ.s
    have hn1 := neg_eq γ.t
    have hn2 := neg_eq (γ.t ^ 2)
    have hss : γ.s + γ.s ^ 4 = 0 := by rw [hs, add_self]
    ext
    · simp only [variableChange_a₁, E₀]
      linear_combination ((γ.u⁻¹ : Kˣ) : K) * γ.s * h2
    · simp only [variableChange_a₂, E₀]
      rw [h3, hr]; ring
    · simp only [variableChange_a₃, E₀]
      linear_combination ((γ.u⁻¹ : Kˣ) : K) ^ 3 * γ.t * h2 + hv3
    · simp only [variableChange_a₄, E₀]
      rw [h2, h3, hr]
      linear_combination ((γ.u⁻¹ : Kˣ) : K) ^ 4 * hss - ((γ.u⁻¹ : Kˣ) : K) ^ 4 * γ.s * h2
    · simp only [variableChange_a₆, E₀]
      rw [hr]
      have : (γ.s ^ 2) ^ 3 - γ.t * 1 - γ.t ^ 2 = 0 := by
        have e : (γ.s ^ 2) ^ 3 = γ.s ^ 6 := by ring
        rw [e, hs3, ← ht]
        ring
      linear_combination ((γ.u⁻¹ : Kˣ) : K) ^ 6 * this

end Curve

section Explicit

variable {K : Type*} [Field K] [CharP K 2]

def ε : VariableChange K := ⟨1, 0, 0, 1⟩

def αv (ω : K) : VariableChange K := ⟨1, 1, 1, ω⟩

def βv (u : Kˣ) : VariableChange K := ⟨u, 0, 0, 0⟩

@[scoped simp] theorem ε_u : (ε : VariableChange K).u = 1 := rfl
@[scoped simp] theorem ε_r : (ε : VariableChange K).r = 0 := rfl
@[scoped simp] theorem ε_s : (ε : VariableChange K).s = 0 := rfl
@[scoped simp] theorem ε_t : (ε : VariableChange K).t = 1 := rfl
@[scoped simp] theorem αv_u (ω : K) : (αv ω).u = 1 := rfl
@[scoped simp] theorem αv_r (ω : K) : (αv ω).r = 1 := rfl
@[scoped simp] theorem αv_s (ω : K) : (αv ω).s = 1 := rfl
@[scoped simp] theorem αv_t (ω : K) : (αv ω).t = ω := rfl
@[scoped simp] theorem βv_u (u : Kˣ) : (βv u).u = u := rfl
@[scoped simp] theorem βv_r (u : Kˣ) : (βv u).r = 0 := rfl
@[scoped simp] theorem βv_s (u : Kˣ) : (βv u).s = 0 := rfl
@[scoped simp] theorem βv_t (u : Kˣ) : (βv u).t = 0 := rfl

section MulComponents
variable {R : Type*} [CommRing R] (C C' : VariableChange R)
theorem mul_u : (C * C').u = C.u * C'.u := rfl
theorem mul_r : (C * C').r = C.r * (C'.u : R) ^ 2 + C'.r := rfl
theorem mul_s : (C * C').s = (C'.u : R) * C.s + C'.s := rfl
theorem mul_t : (C * C').t = C.t * (C'.u : R) ^ 3 + C.r * C'.s * (C'.u : R) ^ 2 + C'.t := rfl
@[scoped simp] theorem one_u : (1 : VariableChange R).u = 1 := rfl
@[scoped simp] theorem one_r : (1 : VariableChange R).r = 0 := rfl
@[scoped simp] theorem one_s : (1 : VariableChange R).s = 0 := rfl
@[scoped simp] theorem one_t : (1 : VariableChange R).t = 0 := rfl
end MulComponents

theorem ε_smul : (ε : VariableChange K) • E₀ K = E₀ K :=
  (smul_E₀_eq_iff _).2 ⟨by simp, by simp, by simp, by simpa using add_self (1 : K)⟩

theorem ε_mul_ε : (ε : VariableChange K) * ε = 1 := by
  ext
  · simp [mul_u]
  · simp [mul_r]
  · simp [mul_s]
  · simp only [mul_t, ε_t, ε_u, ε_r, one_t, Units.val_one]; simpa using add_self (1 : K)

theorem ε_sq : (ε : VariableChange K) ^ 2 = 1 := by rw [sq, ε_mul_ε]

theorem ε_ne_one : (ε : VariableChange K) ≠ 1 := by
  intro h; have := congrArg VariableChange.t h; simp at this

theorem orderOf_ε : orderOf (ε : VariableChange K) = 2 :=
  orderOf_eq_prime ε_sq ε_ne_one

theorem mul_ε_comm {γ : VariableChange K} (hγ : γ • E₀ K = E₀ K) : γ * ε = ε * γ := by
  obtain ⟨hu3, -, -, -⟩ := (smul_E₀_eq_iff γ).1 hγ
  ext
  · simp [mul_u]
  · simp [mul_r]
  · simp [mul_s]
  · simp only [mul_t, ε_t, ε_u, ε_r, ε_s, Units.val_one, hu3]; ring

variable (ω : K) (hω : ω ^ 2 + ω + 1 = 0)
include hω

theorem αv_smul : αv ω • E₀ K = E₀ K :=
  (smul_E₀_eq_iff _).2 ⟨by simp, by simp, by simp, by
    simp only [αv_t, αv_s, one_pow]
    have := neg_eq (1 : K)
    linear_combination hω + this⟩

theorem αv_sq : αv ω ^ 2 = ε := by
  rw [sq]
  ext
  · simp [mul_u]
  · simp only [mul_r, αv_r, αv_u, Units.val_one, ε_r]; simpa using add_self (1 : K)
  · simp only [mul_s, αv_s, αv_u, Units.val_one, ε_s]; simpa using add_self (1 : K)
  · simp only [mul_t, αv_t, αv_u, αv_r, αv_s, Units.val_one, ε_t]
    have := add_self ω
    linear_combination this

theorem αv_ne_one : αv ω ≠ 1 := by
  intro h; have := congrArg VariableChange.r h; simp at this

theorem αv_ne_ε : αv ω ≠ ε := by
  intro h; have := congrArg VariableChange.r h; simp at this

omit hω in
theorem βv_smul (u : Kˣ) (hu : (u : K) ^ 3 = 1) : βv u • E₀ K = E₀ K :=
  (smul_E₀_eq_iff _).2 ⟨by simpa using hu, by simp, by simp, by simp⟩

omit hω in
theorem βv_pow_three (u : Kˣ) (hu : (u : K) ^ 3 = 1) : βv u ^ 3 = 1 := by
  have hu' : u ^ 3 = 1 := Units.ext (by simpa using hu)
  rw [pow_succ, sq]
  ext
  · simp only [mul_u, βv_u, one_u]; rw [← hu']; simp [pow_succ]
  · simp [mul_r]
  · simp [mul_s]
  · simp [mul_t]

omit hω in
theorem βv_ne_one (u : Kˣ) (hu1 : (u : K) ≠ 1) : βv u ≠ 1 := by
  intro h; have := congrArg VariableChange.u h
  simp only [βv_u, one_u] at this
  exact hu1 (by simp [this])

omit hω in
theorem βv_ne_ε (u : Kˣ) (hu1 : (u : K) ≠ 1) : βv u ≠ ε := by
  intro h; have := congrArg VariableChange.u h
  simp only [βv_u, ε_u] at this
  exact hu1 (by simp [this])

omit hω in

theorem sq_or_cube_mem {γ : VariableChange K} (hγ : γ • E₀ K = E₀ K) :
    γ ^ 2 = 1 ∨ γ ^ 2 = ε ∨ γ ^ 3 = 1 ∨ γ ^ 3 = ε := by
  obtain ⟨hu3, hr, hs, ht⟩ := (smul_E₀_eq_iff γ).1 hγ
  have h2 := two_eq_zero (K := K)

  have hs3 : γ.s ^ 3 = 0 ∨ γ.s ^ 3 = 1 := by
    have : γ.s * (γ.s ^ 3 - 1) = 0 := by linear_combination hs
    rcases mul_eq_zero.mp this with h0 | h0
    · left; rw [h0]; ring
    · right; exact sub_eq_zero.mp h0
  by_cases hu1 : (γ.u : K) = 1
  ·
    have hU : γ.u = 1 := Units.ext (by simpa using hu1)
    have key : ∀ c : K, γ.s ^ 3 = c → γ ^ 2 = (⟨1, 0, 0, c⟩ : VariableChange K) := by
      intro c hc
      rw [sq]
      ext
      · simp [mul_u, hU]
      · simp only [mul_r, hU, Units.val_one]; linear_combination γ.r * h2
      · simp only [mul_s, hU, Units.val_one]; linear_combination γ.s * h2
      · simp only [mul_t, hU, Units.val_one, hr]; rw [← hc]; linear_combination γ.t * h2
    rcases hs3 with h0 | h1
    · exact Or.inl (by rw [key 0 h0]; rfl)
    · exact Or.inr (Or.inl (by rw [key 1 h1]; rfl))
  ·
    have hq : (γ.u : K) ^ 2 + (γ.u : K) + 1 = 0 := by
      have : ((γ.u : K) - 1) * ((γ.u : K) ^ 2 + (γ.u : K) + 1) = 0 := by
        linear_combination hu3
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd (sub_eq_zero.mp h0) hu1
      · exact h0
    have hU3 : γ.u ^ 3 = 1 := Units.ext (by simpa using hu3)

    set c : K := γ.s ^ 3 * (γ.u : K) + γ.t with hc
    have hcc : c ^ 2 + c = 0 := by
      rcases hs3 with h0 | h1
      ·
        have hs0 : γ.s = 0 := pow_eq_zero_iff (n := 3) (by norm_num) |>.mp h0
        have : c = γ.t := by rw [hc, hs0]; ring
        rw [this, ht, hs0]; ring
      · have ht1 : γ.t ^ 2 + γ.t = 1 := by rw [ht, h1]
        rw [hc, h1, one_mul]
        linear_combination hq + ht1 + ((γ.u : K) * γ.t) * h2
    have key : γ ^ 3 = (⟨1, 0, 0, c⟩ : VariableChange K) := by
      have hu4 : (γ.u : K) ^ 4 = (γ.u : K) := by
        calc (γ.u : K) ^ 4 = (γ.u : K) ^ 3 * (γ.u : K) := by ring
          _ = (γ.u : K) := by rw [hu3, one_mul]
      rw [pow_succ, sq]
      ext
      · simp only [mul_u]; rw [← hU3]; push_cast; ring
      · simp only [mul_r, mul_u, Units.val_mul]
        have : γ.r * ((γ.u : K) ^ 4 + (γ.u : K) ^ 2 + 1) = 0 := by
          rw [hu4]; linear_combination γ.r * hq
        linear_combination this
      · simp only [mul_s, mul_u, Units.val_mul]
        linear_combination γ.s * hq
      · simp only [mul_t, mul_r, mul_s, mul_u, Units.val_mul]
        rw [hc, hr]
        linear_combination (γ.t * ((γ.u : K) ^ 3 + 1) + γ.t + γ.s ^ 3 * (γ.u : K) ^ 2 +
          γ.s ^ 3 * (γ.u : K)) * hu3 + (γ.t + γ.s ^ 3 * (γ.u : K) ^ 2) * h2
    rcases (sq_add_self_eq_zero_iff c).1 hcc with h0 | h1
    · exact Or.inr (Or.inr (Or.inl (by rw [key, h0]; rfl)))
    · exact Or.inr (Or.inr (Or.inr (by rw [key, h1]; rfl)))

end Explicit

section Count

variable {K : Type*} [Field K] [CharP K 2]

abbrev Γ (K : Type*) [Field K] [CharP K 2] : Subgroup (VariableChange K) :=
  MulAction.stabilizer (VariableChange K) (E₀ K)

theorem mem_Γ_iff (γ : VariableChange K) : γ ∈ Γ K ↔ γ • E₀ K = E₀ K := MulAction.mem_stabilizer_iff

abbrev Param (K : Type*) [Field K] : Type _ :=
  {p : Kˣ × (K × K) // (p.1 : K) ^ 3 = 1 ∧ (p.2.1 ^ 4 = p.2.1 ∧ p.2.2 ^ 2 + p.2.2 = p.2.1 ^ 3)}

def ΓEquivParam : Γ K ≃ Param K where
  toFun γ := ⟨(γ.1.u, (γ.1.s, γ.1.t)),
    ⟨((smul_E₀_eq_iff γ.1).1 γ.2).1, ((smul_E₀_eq_iff γ.1).1 γ.2).2.2⟩⟩
  invFun p := ⟨⟨p.1.1, p.1.2.1 ^ 2, p.1.2.1, p.1.2.2⟩,
    (mem_Γ_iff _).2 ((smul_E₀_eq_iff _).2 ⟨p.2.1, rfl, p.2.2.1, p.2.2.2⟩)⟩
  left_inv γ := by
    obtain ⟨γ, hγ⟩ := γ
    obtain ⟨-, hr, -, -⟩ := (smul_E₀_eq_iff γ).1 hγ
    apply Subtype.ext
    ext <;> simp [hr]
  right_inv p := by
    obtain ⟨⟨u, s, t⟩, hp⟩ := p
    rfl

theorem pow_four_eq_self_iff (s : K) : s ^ 4 = s ↔ s = 0 ∨ s ^ 3 = 1 := by
  constructor
  · intro h
    have : s * (s ^ 3 - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h0)
  · rintro (rfl | h)
    · ring
    · linear_combination s * h

variable (ω : K) (hω : ω ^ 2 + ω + 1 = 0)
include hω

theorem isPrimitiveRoot_omega : IsPrimitiveRoot ω 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := orderOf_eq_prime (omega_pow_three ω hω) (omega_ne_one ω hω)
  rw [← h]; exact IsPrimitiveRoot.orderOf ω

theorem natCard_units_cube : Nat.card {u : Kˣ // (u : K) ^ 3 = 1} = 3 := by
  have e : {u : Kˣ // (u : K) ^ 3 = 1} ≃ rootsOfUnity 3 K :=
    Equiv.subtypeEquivRight (fun u => by
      rw [mem_rootsOfUnity]
      constructor
      · intro h; exact Units.ext (by simpa using h)
      · intro h; have := congrArg Units.val h; simpa using this)
  rw [Nat.card_congr e]
  exact (isPrimitiveRoot_omega ω hω).card_rootsOfUnity

theorem natCard_pow_four_eq_self [DecidableEq K] : Nat.card {s : K // s ^ 4 = s} = 4 := by
  have h3 := (isPrimitiveRoot_omega ω hω).card_nthRootsFinset
  set F : Finset K := Polynomial.nthRootsFinset 3 (1 : K) with hF
  have hmem : ∀ s : K, s ^ 4 = s ↔ s ∈ insert (0 : K) F := by
    intro s
    rw [pow_four_eq_self_iff, Finset.mem_insert, hF, Polynomial.mem_nthRootsFinset (by norm_num)]
  have e : {s : K // s ^ 4 = s} ≃ (insert (0 : K) F : Finset K) := Equiv.subtypeEquivRight hmem
  rw [Nat.card_congr e, Nat.card_eq_finsetCard, Finset.card_insert_of_notMem, h3]
  rw [hF, Polynomial.mem_nthRootsFinset (by norm_num)]
  norm_num

theorem t_values [DecidableEq K] {s t : K} (hs : s ^ 4 = s) :
    t ^ 2 + t = s ^ 3 ↔ t = (if s = 0 then 0 else ω) ∨ t = (if s = 0 then 0 else ω) + 1 := by
  by_cases h0 : s = 0
  · simp only [h0, if_true, zero_add]
    have : (0 : K) ^ 3 = 0 := by ring
    rw [this]
    exact sq_add_self_eq_zero_iff t
  · simp only [h0, if_false]
    have hs3 : s ^ 3 = 1 := ((pow_four_eq_self_iff s).1 hs).resolve_left h0
    rw [hs3, ← sq_add_self_add_one_eq_zero_iff ω hω t]
    have h2 := two_eq_zero (K := K)
    constructor
    · intro h; linear_combination h + h2
    · intro h; linear_combination h - h2

theorem natCard_st [DecidableEq K] :
    Nat.card {q : K × K // q.1 ^ 4 = q.1 ∧ q.2 ^ 2 + q.2 = q.1 ^ 3} = 8 := by
  set base : K → K := fun s => if s = 0 then 0 else ω with hbase
  have e : {q : K × K // q.1 ^ 4 = q.1 ∧ q.2 ^ 2 + q.2 = q.1 ^ 3} ≃ {s : K // s ^ 4 = s} × Bool :=
    { toFun := fun q => (⟨q.1.1, q.2.1⟩, decide (q.1.2 = base q.1.1 + 1))
      invFun := fun p => ⟨(p.1.1, base p.1.1 + if p.2 then 1 else 0),
        ⟨p.1.2, (t_values ω hω p.1.2).2 (by cases p.2 <;> simp [hbase])⟩⟩
      left_inv := by
        rintro ⟨⟨s, t⟩, hs, ht⟩
        dsimp only at hs ht
        apply Subtype.ext
        simp only [Prod.mk.injEq, true_and]
        rcases (t_values ω hω hs).1 ht with h | h
        · have hne : ¬ (t = base s + 1) := by
            rw [h]; intro h'
            have : (1 : K) = 0 := by linear_combination -h'
            exact one_ne_zero this
          simp only [hne, decide_false]
          rw [h]; simp [hbase]
        · simp only [h, decide_true]
          simp [hbase]
      right_inv := by
        rintro ⟨⟨s, hs⟩, b⟩
        apply Prod.ext
        · exact Subtype.ext rfl
        · cases b
          · show decide (base s + (if false = true then (1 : K) else 0) = base s + 1) = false
            simp
          · show decide (base s + (if true = true then (1 : K) else 0) = base s + 1) = true
            simp }
  rw [Nat.card_congr e, Nat.card_prod, natCard_pow_four_eq_self ω hω]
  simp

theorem natCard_Γ : Nat.card (Γ K) = 24 := by
  classical
  have e : Param K ≃ {u : Kˣ // (u : K) ^ 3 = 1} × {q : K × K // q.1 ^ 4 = q.1 ∧ q.2 ^ 2 + q.2 = q.1 ^ 3} :=
    Equiv.subtypeProdEquivProd (p := fun u : Kˣ => (u : K) ^ 3 = 1)
      (q := fun q : K × K => q.1 ^ 4 = q.1 ∧ q.2 ^ 2 + q.2 = q.1 ^ 3)
  rw [Nat.card_congr ΓEquivParam, Nat.card_congr e, Nat.card_prod, natCard_units_cube ω hω,
    natCard_st ω hω]

theorem finite_Γ' : Finite (Γ K) := by
  classical
  exact Nat.finite_of_card_ne_zero (by rw [natCard_Γ ω hω]; norm_num)

end Count

section GroupG

variable {K : Type*} [Field K] [CharP K 2]

def εΓ : Γ K := ⟨ε, (mem_Γ_iff _).2 ε_smul⟩

@[scoped simp] theorem coe_εΓ : ((εΓ : Γ K) : VariableChange K) = ε := rfl

theorem orderOf_εΓ : orderOf (εΓ : Γ K) = 2 := by
  rw [← Subgroup.orderOf_coe, coe_εΓ, orderOf_ε]

theorem εΓ_mem_center : (εΓ : Γ K) ∈ Subgroup.center (Γ K) := by
  rw [Subgroup.mem_center_iff]
  intro γ
  apply Subtype.ext
  simp only [Subgroup.coe_mul, coe_εΓ]
  exact mul_ε_comm ((mem_Γ_iff _).1 γ.2)

abbrev Zε (K : Type*) [Field K] [CharP K 2] : Subgroup (Γ K) := Subgroup.zpowers (εΓ : Γ K)

scoped instance Zε_normal : (Zε K).Normal :=
  ⟨fun n hn g => by
    have hc : n ∈ Subgroup.center (Γ K) := (Subgroup.zpowers_le.mpr εΓ_mem_center) hn
    rw [Subgroup.mem_center_iff] at hc
    rw [hc g, mul_inv_cancel_right]; exact hn⟩

theorem natCard_Zε : Nat.card (Zε K) = 2 := by
  rw [Nat.card_zpowers, orderOf_εΓ]

theorem mem_Zε_iff (γ : Γ K) : γ ∈ Zε K ↔ (γ : VariableChange K) = 1 ∨ (γ : VariableChange K) = ε := by
  rw [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    have h2 : (εΓ : Γ K) ^ (2 : ℤ) = 1 := by
      have := pow_orderOf_eq_one (εΓ : Γ K)
      rw [orderOf_εΓ] at this
      exact_mod_cast this
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      have : (εΓ : Γ K) ^ (m + m) = 1 := by
        rw [← two_mul, zpow_mul, h2, one_zpow]
      rw [this]; rfl
    · right
      have : (εΓ : Γ K) ^ (2 * m + 1) = εΓ := by
        rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
      rw [this]; rfl
  · rintro (h | h)
    · exact ⟨0, by rw [zpow_zero]; exact Subtype.ext h.symm⟩
    · exact ⟨1, by rw [zpow_one]; exact Subtype.ext h.symm⟩

abbrev G (K : Type*) [Field K] [CharP K 2] : Type _ := Γ K ⧸ Zε K

variable (ω : K) (hω : ω ^ 2 + ω + 1 = 0)
include hω

theorem natCard_G : Nat.card (G K) = 12 := by
  have h : Nat.card (Γ K) = Nat.card (G K) * Nat.card (Zε K) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (Zε K)
  rw [natCard_Γ ω hω, natCard_Zε] at h
  omega

theorem finite_G : Finite (G K) := by
  haveI := finite_Γ' ω hω (K := K)
  infer_instance

omit hω in

theorem G_sq_or_cube (g : G K) : g ^ 2 = 1 ∨ g ^ 3 = 1 := by
  induction g using QuotientGroup.induction_on with
  | H γ =>
    have hγ := (mem_Γ_iff _).1 γ.2
    have key : ∀ n : ℕ, ((γ : VariableChange K) ^ n = 1 ∨ (γ : VariableChange K) ^ n = ε) →
        ((γ : G K)) ^ n = 1 := by
      intro n hn
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_Zε_iff]
      simpa using hn
    rcases sq_or_cube_mem hγ with h | h | h | h
    · exact Or.inl (key 2 (Or.inl h))
    · exact Or.inl (key 2 (Or.inr h))
    · exact Or.inr (key 3 (Or.inl h))
    · exact Or.inr (key 3 (Or.inr h))

end GroupG

section Action

variable {K : Type*} [Field K] [CharP K 2] [DecidableEq K]

def xy {W : WeierstrassCurve K} : W.toAffine.Point → Option (K × K)
  | 0 => none
  | .some x y _ => some (x, y)

theorem xy_injective {W : WeierstrassCurve K} : Function.Injective (xy (W := W)) := by
  rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) hh
  · rfl
  · exact absurd hh (by simp [xy])
  · exact absurd hh (by simp [xy])
  · simp only [xy, Option.some.injEq, Prod.mk.injEq] at hh
    obtain ⟨rfl, rfl⟩ := hh
    rfl

theorem xy_vcInvFun (γ : VariableChange K) {W : WeierstrassCurve K} (P : W.toAffine.Point) :
    xy (Point.vcInvFun γ W.toAffine P) = (xy P).map (fun q => (vcXInv γ q.1, vcYInv γ q.1 q.2)) := by
  rcases P with _ | ⟨x, y, h⟩ <;> rfl

def castPt {W₁ W₂ : WeierstrassCurve K} (e : W₁ = W₂) : W₁.toAffine.Point ≃+ W₂.toAffine.Point := by
  subst e; exact AddEquiv.refl _

theorem heq_castPt {W₁ W₂ : WeierstrassCurve K} (e : W₁ = W₂) (P : W₁.toAffine.Point) :
    HEq P (castPt e P) := by subst e; exact HEq.rfl

theorem xy_castPt {W₁ W₂ : WeierstrassCurve K} (e : W₁ = W₂) (P : W₁.toAffine.Point) :
    xy (castPt e P) = xy P := by subst e; rfl

def act (γ : Γ K) : (E₀ K).toAffine.Point →+ (E₀ K).toAffine.Point :=
  (castPt ((mem_Γ_iff _).1 γ.2)).toAddMonoidHom.comp
    { toFun := Point.vcInvFun γ.1 (E₀ K).toAffine
      map_zero' := Point.vcInvFun_zero
      map_add' := Point.vcInvFun_add γ.1 (E₀ K).toAffine }

theorem act_apply (γ : Γ K) (P : (E₀ K).toAffine.Point) :
    act γ P = castPt ((mem_Γ_iff _).1 γ.2) (Point.vcInvFun γ.1 (E₀ K).toAffine P) := rfl

theorem heq_act (γ : Γ K) (P : (E₀ K).toAffine.Point) :
    HEq (Point.vcInvFun γ.1 (E₀ K).toAffine P) (act γ P) :=
  heq_castPt _ _

theorem xy_act (γ : Γ K) (P : (E₀ K).toAffine.Point) :
    xy (act γ P) = (xy P).map (fun q => (vcXInv γ.1 q.1, vcYInv γ.1 q.1 q.2)) := by
  rw [act_apply, xy_castPt, xy_vcInvFun]

theorem act_injective (γ : Γ K) : Function.Injective (act γ) := by
  intro P Q h
  have h' := congrArg xy h
  rw [xy_act, xy_act] at h'
  have hinj : Function.Injective (fun q : K × K => (vcXInv γ.1 q.1, vcYInv γ.1 q.1 q.2)) := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ hq
    simp only [Prod.mk.injEq] at hq
    obtain ⟨hx, hy⟩ := hq
    have hx' : x = x' := by simpa using congrArg (vcX γ.1) hx
    subst hx'
    have hy' : y = y' := by simpa using congrArg (vcY γ.1 (vcXInv γ.1 x)) hy
    exact Prod.ext rfl hy'
  exact xy_injective (Option.map_injective hinj h')

theorem act_one (P : (E₀ K).toAffine.Point) : act (1 : Γ K) P = P := by
  apply xy_injective
  rw [xy_act]
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · show some (vcXInv (1 : VariableChange K) x, vcYInv (1 : VariableChange K) x y) = some (x, y)
    simp [vcXInv, vcYInv]

theorem act_mul (γ γ' : Γ K) (P : (E₀ K).toAffine.Point) : act (γ * γ') P = act γ (act γ' P) := by
  apply xy_injective
  rw [xy_act, xy_act, xy_act]
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · show some (vcXInv (γ.1 * γ'.1) x, vcYInv (γ.1 * γ'.1) x y) =
      some (vcXInv γ.1 (vcXInv γ'.1 x), vcYInv γ.1 (vcXInv γ'.1 x) (vcYInv γ'.1 x y))
    have hu : (γ.1.u : K) ≠ 0 := γ.1.u.ne_zero
    have hu' : (γ'.1.u : K) ≠ 0 := γ'.1.u.ne_zero
    simp only [vcXInv, vcYInv, mul_u, mul_r, mul_s, mul_t, Units.val_mul, mul_inv, Units.val_inv_eq_inv_val,
      Option.some.injEq, Prod.mk.injEq]
    constructor
    · field_simp; ring
    · field_simp; ring

scoped instance actMulAction : MulAction (Γ K) (E₀ K).toAffine.Point where
  smul γ P := act γ P
  one_smul := act_one
  mul_smul := act_mul

theorem smul_pt_def (γ : Γ K) (P : (E₀ K).toAffine.Point) : γ • P = act γ P := rfl

scoped instance actDistrib : DistribMulAction (Γ K) (E₀ K).toAffine.Point where
  smul_zero γ := (act γ).map_zero
  smul_add γ := (act γ).map_add

theorem εΓ_smul_pt (P : (E₀ K).toAffine.Point) : (εΓ : Γ K) • P = -P := by
  rw [smul_pt_def]
  apply xy_injective
  rw [xy_act]
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [Point.neg_some]
    show some (vcXInv (ε : VariableChange K) x, vcYInv (ε : VariableChange K) x y) =
      some (x, (E₀ K).toAffine.negY x y)
    simp only [vcXInv, vcYInv, ε_u, ε_r, ε_s, ε_t, inv_one, Units.val_one, one_pow, one_mul, sub_zero,
      zero_mul, WeierstrassCurve.Affine.negY, Option.some.injEq, Prod.mk.injEq, true_and]
    show y - 1 = -y - (E₀ K).a₁ * x - (E₀ K).a₃
    rw [E₀_a₁, E₀_a₃, neg_eq]; ring

section Level

variable {M : ℕ} [NeZero M]

theorem nsmul_eq_of_modEq {A : Type*} [AddCommGroup A] {P : A} (hP : M • P = 0) {a b : ℕ}
    (h : a ≡ b [MOD M]) : a • P = b • P := by
  have key : ∀ c : ℕ, c • P = (c % M) • P := by
    intro c
    conv_lhs => rw [← Nat.mod_add_div c M]
    rw [add_nsmul, mul_comm, mul_nsmul', hP, nsmul_zero, add_zero]
  rw [key a, key b, h]

theorem nsmul_eq_zero_of_dvd {A : Type*} [AddCommGroup A] {P : A} (hP : M • P = 0) {a : ℕ}
    (h : M ∣ a) : a • P = 0 := by
  obtain ⟨c, rfl⟩ := h
  rw [mul_comm, mul_nsmul', hP, nsmul_zero]

def usmul {A : Type*} [AddCommGroup A] (u : (ZMod M)ˣ) (P : A) : A := (u : ZMod M).val • P

theorem usmul_def {A : Type*} [AddCommGroup A] (u : (ZMod M)ˣ) (P : A) :
    usmul u P = (u : ZMod M).val • P := rfl

theorem nsmul_usmul_comm {A : Type*} [AddCommGroup A] (u : (ZMod M)ˣ) (P : A) (n : ℕ) :
    n • usmul u P = usmul u (n • P) := by
  rw [usmul_def, usmul_def, ← mul_nsmul', ← mul_nsmul', mul_comm]

theorem torsion_usmul {A : Type*} [AddCommGroup A] {P : A} (hP : M • P = 0) (u : (ZMod M)ˣ) :
    M • usmul u P = 0 := by
  rw [nsmul_usmul_comm, hP, usmul_def, nsmul_zero]

theorem usmul_mul {A : Type*} [AddCommGroup A] {P : A} (hP : M • P = 0) (u v : (ZMod M)ˣ) :
    usmul (u * v) P = usmul u (usmul v P) := by
  rw [usmul_def, usmul_def, usmul_def, ← mul_nsmul', Units.val_mul, ZMod.val_mul]
  exact nsmul_eq_of_modEq hP (Nat.mod_modEq _ _)

theorem usmul_one {A : Type*} [AddCommGroup A] {P : A} (hP : M • P = 0) : usmul (1 : (ZMod M)ˣ) P = P := by
  rw [usmul_def, Units.val_one, ZMod.val_one_eq_one_mod]
  rw [nsmul_eq_of_modEq hP (Nat.mod_modEq 1 M), one_nsmul]

theorem usmul_neg {A : Type*} [AddCommGroup A] {P : A} (hP : M • P = 0) (u : (ZMod M)ˣ) :
    usmul (-u) P = -usmul u P := by
  rw [eq_neg_iff_add_eq_zero, usmul_def, usmul_def, ← add_nsmul]
  apply nsmul_eq_zero_of_dvd hP
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  simp

theorem usmul_inv_usmul {A : Type*} [AddCommGroup A] {P : A} (hP : M • P = 0) (u : (ZMod M)ˣ) :
    usmul u⁻¹ (usmul u P) = P := by
  rw [← usmul_mul hP, inv_mul_cancel, usmul_one hP]

variable (H : Subgroup (ZMod M)ˣ)

abbrev Hpm : Subgroup (ZMod M)ˣ := H ⊔ Subgroup.zpowers (-1)

theorem neg_one_mem_Hpm : (-1 : (ZMod M)ˣ) ∈ Hpm H :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem neg_mem_Hpm {u : (ZMod M)ˣ} (hu : u ∈ Hpm H) : -u ∈ Hpm H := by
  rw [← neg_one_mul]; exact Subgroup.mul_mem _ (neg_one_mem_Hpm H) hu

def orbH {A : Type*} [AddCommGroup A] (P : A) : Set A :=
  {T | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧ T = (u : ZMod M).val • P}

theorem mem_orbH_iff {A : Type*} [AddCommGroup A] (P T : A) :
    T ∈ orbH H P ↔ ∃ u : (ZMod M)ˣ, u ∈ Hpm H ∧ T = usmul u P := Iff.rfl

theorem self_mem_orbH {A : Type*} [AddCommGroup A] {P : A} (hP : M • P = 0) : P ∈ orbH H P :=
  ⟨1, one_mem _, (usmul_one hP).symm⟩

theorem torsion_of_mem_orbH {A : Type*} [AddCommGroup A] {P T : A} (hP : M • P = 0)
    (hT : T ∈ orbH H P) : M • T = 0 := by
  obtain ⟨u, -, rfl⟩ := hT
  exact torsion_usmul hP u

theorem orbH_eq_of_mem {A : Type*} [AddCommGroup A] {P T : A} (hP : M • P = 0)
    (hT : T ∈ orbH H P) : orbH H T = orbH H P := by
  rw [mem_orbH_iff] at hT
  obtain ⟨u₀, hu₀, rfl⟩ := hT
  ext Q
  rw [mem_orbH_iff, mem_orbH_iff]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u * u₀, Subgroup.mul_mem _ hu hu₀, (usmul_mul hP u u₀).symm⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u * u₀⁻¹, Subgroup.mul_mem _ hu (Subgroup.inv_mem _ hu₀), ?_⟩
    rw [usmul_mul (torsion_usmul hP u₀), usmul_inv_usmul hP]

theorem neg_mem_orbH {A : Type*} [AddCommGroup A] {P T : A} (hP : M • P = 0)
    (hT : T ∈ orbH H P) : -T ∈ orbH H P := by
  obtain ⟨u, hu, rfl⟩ := hT
  exact ⟨-u, neg_mem_Hpm H hu, (usmul_neg hP u).symm⟩

theorem image_orbH {A B : Type*} [AddCommGroup A] [AddCommGroup B] (φ : A →+ B) (P : A) :
    φ '' orbH H P = orbH H (φ P) := by
  ext Q
  simp only [Set.mem_image, mem_orbH_iff, usmul_def]
  constructor
  · rintro ⟨T, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, by rw [map_nsmul]⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨(u : ZMod M).val • P, ⟨u, hu, rfl⟩, by rw [map_nsmul]⟩

variable (K M) in

abbrev XH : Type _ :=
  {s : Set (E₀ K).toAffine.Point // ∃ P : (E₀ K).toAffine.Point, addOrderOf P = M ∧
    s = {T | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧ T = (u : ZMod M).val • P}}

theorem torsion_of_addOrderOf {A : Type*} [AddCommGroup A] {P : A} (hP : addOrderOf P = M) :
    M • P = 0 := by
  rw [← hP]; exact addOrderOf_nsmul_eq_zero P

def smulX (γ : Γ K) (s : XH K M H) : XH K M H :=
  ⟨act γ '' s.1, by
    obtain ⟨P, hP, hs⟩ := s.2
    refine ⟨act γ P, ?_, ?_⟩
    · rw [← hP]; exact addOrderOf_injective (act γ) (act_injective γ) P
    · rw [hs]; exact image_orbH H (act γ) P⟩

theorem coe_smulX (γ : Γ K) (s : XH K M H) : (smulX H γ s).1 = act γ '' s.1 := rfl

scoped instance XHMulAction : MulAction (Γ K) (XH K M H) where
  smul := smulX H
  one_smul s := by
    apply Subtype.ext
    show act 1 '' s.1 = s.1
    have : (act (1 : Γ K) : (E₀ K).toAffine.Point → (E₀ K).toAffine.Point) = id :=
      funext act_one
    rw [this, Set.image_id]
  mul_smul γ γ' s := by
    apply Subtype.ext
    show act (γ * γ') '' s.1 = act γ '' (act γ' '' s.1)
    rw [Set.image_image]
    exact Set.image_congr fun P _ => act_mul γ γ' P

theorem coe_smul_XH (γ : Γ K) (s : XH K M H) : ((γ • s : XH K M H) : Set _) = act γ '' s.1 := rfl

theorem mem_smul_XH_iff (γ : Γ K) (s : XH K M H) (Q : (E₀ K).toAffine.Point) :
    Q ∈ (γ • s : XH K M H).1 ↔ ∃ T ∈ s.1, act γ T = Q := by
  rw [coe_smul_XH, Set.mem_image]

theorem εΓ_smul_XH (s : XH K M H) : (εΓ : Γ K) • s = s := by
  obtain ⟨P, hP, hs⟩ := s.2
  have hPM := torsion_of_addOrderOf hP
  apply Subtype.ext
  rw [coe_smul_XH]
  ext Q
  rw [Set.mem_image]
  have hs' : s.1 = orbH H P := hs
  constructor
  · rintro ⟨T, hT, rfl⟩
    rw [← smul_pt_def, εΓ_smul_pt]
    rw [hs'] at hT ⊢
    exact neg_mem_orbH H hPM hT
  · intro hQ
    refine ⟨-Q, ?_, by rw [← smul_pt_def, εΓ_smul_pt, neg_neg]⟩
    rw [hs'] at hQ ⊢
    exact neg_mem_orbH H hPM hQ

theorem forall_exists_heq_iff (γ : Γ K) (s s' : XH K M H) :
    (∀ T ∈ s.1, ∃ T' ∈ s'.1, HEq (Point.vcInvFun γ.1 (E₀ K).toAffine T) T') ↔ γ • s = s' := by
  constructor
  · intro h
    obtain ⟨P, hP, hs⟩ := s.2
    obtain ⟨P', hP', hs'⟩ := s'.2
    have hPM := torsion_of_addOrderOf hP
    have hPM' := torsion_of_addOrderOf hP'

    have hmem : act γ P ∈ s'.1 := by
      have hPs : P ∈ s.1 := by rw [hs]; exact self_mem_orbH H hPM
      obtain ⟨T', hT', hh⟩ := h P hPs
      have : act γ P = T' := eq_of_heq ((heq_act γ P).symm.trans hh)
      rw [this]; exact hT'
    apply Subtype.ext
    have h1 : (act γ) '' s.1 = orbH H (act γ P) := by rw [hs]; exact image_orbH H (act γ) P
    have h2 : act γ P ∈ orbH H P' := by rw [hs'] at hmem; exact hmem
    rw [coe_smul_XH, h1, hs', orbH_eq_of_mem H hPM' h2]
    rfl
  · rintro rfl T hT
    exact ⟨act γ T, (mem_smul_XH_iff H γ s _).2 ⟨T, hT, rfl⟩, heq_act γ T⟩

theorem exists_variableChange_iff_mem_orbit (s s' : XH K M H) :
    (∃ γ : VariableChange K, γ • E₀ K = E₀ K ∧
      ∀ T ∈ s.1, ∃ T' ∈ s'.1, HEq (Point.vcInvFun γ (E₀ K).toAffine T) T') ↔
    s' ∈ MulAction.orbit (Γ K) s := by
  constructor
  · rintro ⟨γ, hγ, h⟩
    have := (forall_exists_heq_iff H (⟨γ, (mem_Γ_iff γ).2 hγ⟩ : Γ K) s s').1 h
    exact ⟨⟨γ, (mem_Γ_iff γ).2 hγ⟩, this⟩
  · rintro ⟨γ, rfl⟩
    exact ⟨γ.1, (mem_Γ_iff _).1 γ.2, (forall_exists_heq_iff H γ s (γ • s)).2 rfl⟩

theorem exists_pow_forall_exists_heq_iff (γ : Γ K) (s s' : XH K M H) :
    (∃ k : ℕ, ∀ T ∈ s.1, ∃ T' ∈ s'.1, HEq (Point.vcInvFun (γ.1 ^ k) (E₀ K).toAffine T) T') ↔
      ∃ k : ℕ, γ ^ k • s = s' := by
  refine exists_congr fun k => ?_
  rw [← forall_exists_heq_iff H (γ ^ k) s s']
  rfl

theorem Zε_le_ker_XH : Zε K ≤ (MulAction.toPermHom (Γ K) (XH K M H)).ker := by
  rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
  ext s
  simp [εΓ_smul_XH]

scoped instance GMulActionXH : MulAction (G K) (XH K M H) :=
  MulAction.compHom (XH K M H)
    (QuotientGroup.lift (Zε K) (MulAction.toPermHom (Γ K) (XH K M H)) (Zε_le_ker_XH H))

theorem mk_smul_XH (γ : Γ K) (s : XH K M H) : (QuotientGroup.mk γ : G K) • s = γ • s := by
  rw [MulAction.compHom_smul_def, QuotientGroup.lift_mk]; rfl

theorem mk_pow_smul_XH (γ : Γ K) (k : ℕ) (s : XH K M H) :
    (QuotientGroup.mk γ : G K) ^ k • s = γ ^ k • s := by
  rw [← QuotientGroup.mk_pow, mk_smul_XH]

theorem orbit_G_eq (s : XH K M H) : MulAction.orbit (G K) s = MulAction.orbit (Γ K) s := by
  ext s'
  constructor
  · rintro ⟨g, rfl⟩
    induction g using QuotientGroup.induction_on with
    | H γ => exact ⟨γ, (mk_smul_XH H γ s).symm⟩
  · rintro ⟨γ, rfl⟩
    exact ⟨(QuotientGroup.mk γ : G K), mk_smul_XH H γ s⟩

end Level

end Action

section Census

open MulAction AlgebraicCurve ModularCurve

variable {K : Type*} [Field K] [CharP K 2] [DecidableEq K]
variable (ω : K) (hω : ω ^ 2 + ω + 1 = 0)
variable {M : ℕ} [NeZero M] (H : Subgroup (ZMod M)ˣ)
variable {F : Type*} [Field F] [Algebra K F]

def αΓ : Γ K := ⟨αv ω, (mem_Γ_iff _).2 (αv_smul ω hω)⟩

def βΓ : Γ K := ⟨βv (Units.mk0 ω (omega_ne_zero ω hω)), (mem_Γ_iff _).2
  (βv_smul _ (by simpa using omega_pow_three ω hω))⟩

theorem mk_αΓ_ne_one : (QuotientGroup.mk (αΓ ω hω) : G K) ≠ 1 := by
  rw [Ne, QuotientGroup.eq_one_iff, mem_Zε_iff, not_or]
  exact ⟨αv_ne_one ω hω, αv_ne_ε ω hω⟩

theorem mk_αΓ_sq : (QuotientGroup.mk (αΓ ω hω) : G K) ^ 2 = 1 := by
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_Zε_iff]
  right; exact αv_sq ω hω

theorem mk_βΓ_ne_one : (QuotientGroup.mk (βΓ ω hω) : G K) ≠ 1 := by
  rw [Ne, QuotientGroup.eq_one_iff, mem_Zε_iff, not_or]
  exact ⟨βv_ne_one _ (by simpa using omega_ne_one ω hω), βv_ne_ε _ (by simpa using omega_ne_one ω hω)⟩

theorem mk_βΓ_pow_three : (QuotientGroup.mk (βΓ ω hω) : G K) ^ 3 = 1 := by
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_Zε_iff]
  left; exact βv_pow_three _ (by simpa using omega_pow_three ω hω)

theorem natCard_fixedBy_orbit (γ : Γ K) (s : XH K M H) :
    Nat.card (fixedBy (orbit (G K) s) (QuotientGroup.mk γ : G K)) =
      Nat.card {s' : XH K M H // s' ∈ orbit (G K) s ∧ γ • s' = s'} := by
  refine Nat.card_congr ((Equiv.subtypeEquivRight ?_).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun s' => s' ∈ orbit (G K) s) (fun s' => γ • s' = s')))
  intro y
  rw [mem_fixedBy, Subtype.ext_iff, orbit.coe_smul, mk_smul_XH]

section Burnside

variable {G₀ : Type*} [Group G₀] [Finite G₀] {X : Type*} [MulAction G₀ X] [Finite X]

theorem card_orbits_mul_orderOf (g : G₀) :
    Nat.card (Quotient (orbitRel (Subgroup.zpowers g) X)) * orderOf g =
      ∑ i ∈ Finset.range (orderOf g), Nat.card (fixedBy X (g ^ i)) := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  letI : Fintype G₀ := Fintype.ofFinite G₀
  have hg : IsOfFinOrder g := isOfFinOrder_of_finite g
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (Subgroup.zpowers g) X
  have hz : Fintype.card (Subgroup.zpowers g) = orderOf g := by
    rw [Fintype.card_eq_nat_card, Nat.card_zpowers]
  rw [hz, Fintype.card_eq_nat_card] at hB
  rw [← hB]
  rw [← Fintype.sum_equiv (finEquivZPowers hg)
    (fun i => Fintype.card (fixedBy X ((finEquivZPowers hg i : Subgroup.zpowers g))))
    (fun a => Fintype.card (fixedBy X a)) (fun i => rfl)]
  have hterm : ∀ i : Fin (orderOf g),
      Fintype.card (fixedBy X ((finEquivZPowers hg i : Subgroup.zpowers g))) =
        Nat.card (fixedBy X (g ^ (i : ℕ))) := by
    intro i
    rw [Fintype.card_eq_nat_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by
      rw [mem_fixedBy, mem_fixedBy, finEquivZPowers_apply]
      exact Iff.rfl)
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  exact Fin.sum_univ_eq_sum_range (fun n => Nat.card (fixedBy X (g ^ n))) (orderOf g)

theorem fixedBy_one_eq : fixedBy X (1 : G₀) = Set.univ := by
  ext x; simp

theorem two_mul_card_orbits (g : G₀) (hg1 : g ≠ 1) (hg2 : g ^ 2 = 1) :
    2 * Nat.card (Quotient (orbitRel (Subgroup.zpowers g) X)) =
      Nat.card X + Nat.card (fixedBy X g) := by
  have ho : orderOf g = 2 := orderOf_eq_prime hg2 hg1
  have h := card_orbits_mul_orderOf (X := X) g
  rw [ho] at h
  rw [mul_comm, h, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, pow_one, fixedBy_one_eq, Nat.card_univ]

theorem three_mul_card_orbits (g : G₀) (hg1 : g ≠ 1) (hg3 : g ^ 3 = 1) :
    3 * Nat.card (Quotient (orbitRel (Subgroup.zpowers g) X)) =
      Nat.card X + 2 * Nat.card (fixedBy X g) := by
  have ho : orderOf g = 3 := orderOf_eq_prime hg3 hg1
  have h := card_orbits_mul_orderOf (X := X) g
  rw [ho] at h
  have hfix : fixedBy X (g ^ 2) = fixedBy X g := by
    ext x
    rw [mem_fixedBy, mem_fixedBy]
    constructor
    · intro hx
      have h4 : g = g ^ 2 * g ^ 2 := by
        rw [← pow_add]
        calc g = g ^ 3 * g := by rw [hg3, one_mul]
          _ = g ^ (2 + 2) := by rw [← pow_succ]
      calc g • x = (g ^ 2 * g ^ 2) • x := by rw [← h4]
        _ = x := by rw [mul_smul, hx, hx]
    · intro hx
      rw [sq, mul_smul, hx, hx]
  rw [mul_comm, h, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, pow_zero, pow_one, fixedBy_one_eq, Nat.card_univ, hfix]
  ring

theorem card_orbits_eq_of_classifying (g : G₀) (hg : IsOfFinOrder g) {D : Type*} (c : X → D)
    (hcs : Function.Surjective c) (hc : ∀ x x', c x = c x' ↔ ∃ k : ℕ, g ^ k • x = x') :
    Nat.card (Quotient (orbitRel (Subgroup.zpowers g) X)) = Nat.card D := by
  have hker : orbitRel (Subgroup.zpowers g) X = Setoid.ker c := by
    apply Setoid.ext
    intro x' x
    rw [orbitRel_apply, Setoid.ker_def, eq_comm, hc, mem_orbit_iff]
    constructor
    · rintro ⟨⟨y, hy⟩, rfl⟩
      rw [Subgroup.mem_zpowers_iff] at hy
      obtain ⟨z, rfl⟩ := hy
      refine ⟨(z % (orderOf g : ℤ)).toNat, ?_⟩
      rw [Subgroup.mk_smul]
      congr 1
      have ho : (0 : ℤ) < orderOf g := by exact_mod_cast hg.orderOf_pos
      conv_lhs => rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ ho.ne'), zpow_mod_orderOf]
    · rintro ⟨k, rfl⟩
      exact ⟨⟨g ^ k, Subgroup.npow_mem_zpowers g k⟩, rfl⟩
  rw [hker]
  exact Nat.card_congr (Setoid.quotientKerEquivOfSurjective c hcs)

end Burnside

include hω in

theorem census_core (j : F) (S : Finset (Place K F)) (f : XH K M H → Place K F)
    (hf1 : ∀ s, f s ∈ S) (hf2 : ∀ P ∈ S, ∃ s, f s = P)
    (hf3 : ∀ s s', f s = f s' ↔ ∃ γ : VariableChange K, γ • E₀ K = E₀ K ∧
      ∀ T ∈ s.1, ∃ T' ∈ s'.1, HEq (Point.vcInvFun γ (E₀ K).toAffine T) T')
    (hf4 : ∀ s, (f s).ord j = (Nat.card {s' : XH K M H // f s' = f s} : ℤ))
    (m : ℕ) (hm : Nat.card (XH K M H) = m)
    {D₀ D₁ : Type*} (c₃ : XH K M H → D₀) (hc₃s : Function.Surjective c₃)
    (hc₃ : ∀ s s', c₃ s = c₃ s' ↔ ∃ k : ℕ, βΓ ω hω ^ k • s = s')
    (c₂ : XH K M H → D₁) (hc₂s : Function.Surjective c₂)
    (hc₂ : ∀ s s', c₂ s = c₂ s' ↔ ∃ k : ℕ, αΓ ω hω ^ k • s = s') :
    (∀ P ∈ S, P.ord j = 1 ∨ P.ord j = 3 ∨ P.ord j = 4 ∨ P.ord j = 6 ∨ P.ord j = 12) ∧
    (∑ P ∈ S, P.ord j = (m : ℤ)) ∧
    ((S.filter fun P => P.ord j = 1).card + (S.filter fun P => P.ord j = 3).card +
        2 * (S.filter fun P => P.ord j = 4).card + 2 * (S.filter fun P => P.ord j = 6).card +
        4 * (S.filter fun P => P.ord j = 12).card = Nat.card D₀) ∧
    ((S.filter fun P => P.ord j = 1).card + 3 * (S.filter fun P => P.ord j = 3).card +
        2 * (S.filter fun P => P.ord j = 4).card + 4 * (S.filter fun P => P.ord j = 6).card +
        6 * (S.filter fun P => P.ord j = 12).card = Nat.card D₁) := by
  haveI : Finite (Γ K) := finite_Γ' ω hω
  haveI : Finite (G K) := finite_G ω hω

  have horb : ∀ s s' : XH K M H, f s = f s' ↔ s' ∈ orbit (Γ K) s := fun s s' =>
    (hf3 s s').trans (exists_variableChange_iff_mem_orbit H s s')
  have he : ∀ s : XH K M H, (f s).ord j = (Nat.card (orbit (G K) s) : ℤ) := by
    intro s
    rw [hf4]
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight fun s' => by
      rw [eq_comm, horb, ← orbit_G_eq])

  have hfin : ∀ P : Place K F, {s : XH K M H | f s = P}.Finite := by
    intro P
    by_cases hP : ∃ s₀, f s₀ = P
    · obtain ⟨s₀, rfl⟩ := hP
      have : {s : XH K M H | f s = f s₀} = orbit (Γ K) s₀ := by
        ext s'
        rw [Set.mem_setOf_eq, eq_comm]
        exact horb s₀ s'
      rw [this]
      exact Set.finite_range _
    · refine Set.Finite.subset Set.finite_empty ?_
      rintro s rfl
      exact hP ⟨s, rfl⟩
  haveI : Finite (XH K M H) := by
    rw [← Set.finite_univ_iff]
    refine Set.Finite.subset (Set.Finite.biUnion S.finite_toSet fun P _ => hfin P) ?_
    intro s _
    exact Set.mem_biUnion (hf1 s) rfl
  classical
  letI : Fintype (XH K M H) := Fintype.ofFinite _

  have hMk : ∀ s : XH K M H, _ := fun s =>
    haveI : Nonempty (orbit (G K) s) := ⟨⟨s, mem_orbit_self s⟩⟩
    MulAction.natCard_fixedBy_of_isPretransitive_of_card_eq_twelve (natCard_G ω hω) G_sq_or_cube
      (orbit (G K) s)

  have h1 : ∀ P ∈ S, P.ord j = 1 ∨ P.ord j = 3 ∨ P.ord j = 4 ∨ P.ord j = 6 ∨ P.ord j = 12 := by
    intro P hP
    obtain ⟨s, rfl⟩ := hf2 P hP
    rw [he s]
    rcases (hMk s).1 with h | h | h | h | h <;> rw [h] <;> norm_num

  have hsum : ∀ (μ : ℤ → ℕ) (p : XH K M H → Prop),
      (∀ s : XH K M H, Nat.card {s' : XH K M H // s' ∈ orbit (G K) s ∧ p s'} = μ ((f s).ord j)) →
      ∑ P ∈ S, μ (P.ord j) = Nat.card {s : XH K M H // p s} := by
    intro μ p hμ
    have hRHS : Nat.card {s : XH K M H // p s} = (Finset.univ.filter fun s : XH K M H => p s).card :=
      Nat.subtype_card _ (fun s => by simp)
    rw [hRHS, Finset.card_eq_sum_card_fiberwise (t := S) (f := f) (fun s _ => hf1 s)]
    refine Finset.sum_congr rfl fun P hP => ?_
    obtain ⟨s₀, rfl⟩ := hf2 P hP
    rw [← hμ s₀]
    refine Nat.subtype_card _ fun s' => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [orbit_G_eq, ← horb, eq_comm]
    tauto

  have hX : ∑ P ∈ S, ((if P.ord j = 1 then 1 else 0) + (if P.ord j = 3 then 3 else 0) +
      (if P.ord j = 4 then 4 else 0) + (if P.ord j = 6 then 6 else 0) +
      (if P.ord j = 12 then 12 else 0)) = Nat.card (XH K M H) := by
    have : Nat.card (XH K M H) = Nat.card {s : XH K M H // True} :=
      (Nat.card_congr (Equiv.Set.univ (XH K M H))).symm.trans
        (Nat.card_congr (Equiv.subtypeEquivRight fun s => by simp))
    rw [this]
    apply hsum (fun e => (if e = 1 then 1 else 0) + (if e = 3 then 3 else 0) +
      (if e = 4 then 4 else 0) + (if e = 6 then 6 else 0) + (if e = 12 then 12 else 0)) (fun _ => True)
    intro s
    have hc : Nat.card {s' : XH K M H // s' ∈ orbit (G K) s ∧ True} = Nat.card (orbit (G K) s) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun s' => by simp)
    rw [hc, he s]
    rcases (hMk s).1 with h | h | h | h | h <;> rw [h] <;> norm_num

  have h2 : ∑ P ∈ S, ((if P.ord j = 1 then 1 else 0) + (if P.ord j = 3 then 3 else 0) +
      (if P.ord j = 6 then 2 else 0)) = Nat.card {s : XH K M H // αΓ ω hω • s = s} := by
    apply hsum (fun e => (if e = 1 then 1 else 0) + (if e = 3 then 3 else 0) +
      (if e = 6 then 2 else 0)) (fun s => αΓ ω hω • s = s)
    intro s
    rw [← natCard_fixedBy_orbit, he s]
    obtain ⟨hsize, hinv, -⟩ := hMk s
    obtain ⟨c1, c3, c4, c6, c12⟩ := hinv _ (mk_αΓ_ne_one ω hω) (mk_αΓ_sq ω hω)
    rcases hsize with h | h | h | h | h
    · rw [c1 h, h]; norm_num
    · rw [c3 h, h]; norm_num
    · rw [c4 h, h]; norm_num
    · rw [c6 h, h]; norm_num
    · rw [c12 h, h]; norm_num

  have h3 : ∑ P ∈ S, ((if P.ord j = 1 then 1 else 0) + (if P.ord j = 4 then 1 else 0)) =
      Nat.card {s : XH K M H // βΓ ω hω • s = s} := by
    apply hsum (fun e => (if e = 1 then 1 else 0) + (if e = 4 then 1 else 0)) (fun s => βΓ ω hω • s = s)
    intro s
    rw [← natCard_fixedBy_orbit, he s]
    obtain ⟨hsize, -, hord⟩ := hMk s
    obtain ⟨c1, c3, c4, c6, c12⟩ := hord _ (mk_βΓ_ne_one ω hω) (mk_βΓ_pow_three ω hω)
    rcases hsize with h | h | h | h | h
    · rw [c1 h, h]; norm_num
    · rw [c3 h, h]; norm_num
    · rw [c4 h, h]; norm_num
    · rw [c6 h, h]; norm_num
    · rw [c12 h, h]; norm_num

  set n1 := (S.filter fun P => P.ord j = 1).card with hn1
  set n3 := (S.filter fun P => P.ord j = 3).card with hn3
  set n4 := (S.filter fun P => P.ord j = 4).card with hn4
  set n6 := (S.filter fun P => P.ord j = 6).card with hn6
  set n12 := (S.filter fun P => P.ord j = 12).card with hn12
  have ind : ∀ (e : ℤ) (a : ℕ), ∑ P ∈ S, (if P.ord j = e then a else 0) = a * (S.filter fun P => P.ord j = e).card := by
    intro e a
    rw [Finset.card_filter, Finset.mul_sum]
    exact Finset.sum_congr rfl fun P _ => by split_ifs <;> simp
  have hX' : Nat.card (XH K M H) = n1 + 3 * n3 + 4 * n4 + 6 * n6 + 12 * n12 := by
    rw [← hX, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ind, ind, ind, ind, ind]
    ring
  have h2' : Nat.card {s : XH K M H // αΓ ω hω • s = s} = n1 + 3 * n3 + 2 * n6 := by
    rw [← h2, Finset.sum_add_distrib, Finset.sum_add_distrib, ind, ind, ind]
    ring
  have h3' : Nat.card {s : XH K M H // βΓ ω hω • s = s} = n1 + n4 := by
    rw [← h3, Finset.sum_add_distrib, ind, ind]
    ring

  have hsumZ : ∑ P ∈ S, P.ord j = (Nat.card (XH K M H) : ℤ) := by
    rw [hX']
    push_cast
    rw [hn1, hn3, hn4, hn6, hn12]
    have : ∀ P ∈ S, P.ord j = ((if P.ord j = 1 then 1 else 0) + (if P.ord j = 3 then 3 else 0) +
        (if P.ord j = 4 then 4 else 0) + (if P.ord j = 6 then 6 else 0) +
        (if P.ord j = 12 then 12 else 0) : ℤ) := by
      intro P hP
      rcases h1 P hP with h | h | h | h | h <;> rw [h] <;> norm_num
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_add_distrib]
    have indZ : ∀ (e a : ℤ), ∑ P ∈ S, (if P.ord j = e then a else 0) =
        a * ((S.filter fun P => P.ord j = e).card : ℤ) := by
      intro e a
      rw [Finset.card_filter]
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun P _ => by split_ifs <;> simp
    rw [indZ, indZ, indZ, indZ, indZ]
    ring

  have hfixβ : Nat.card (fixedBy (XH K M H) (QuotientGroup.mk (βΓ ω hω) : G K)) =
      Nat.card {s : XH K M H // βΓ ω hω • s = s} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun s => by rw [mem_fixedBy, mk_smul_XH])
  have hfixα : Nat.card (fixedBy (XH K M H) (QuotientGroup.mk (αΓ ω hω) : G K)) =
      Nat.card {s : XH K M H // αΓ ω hω • s = s} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun s => by rw [mem_fixedBy, mk_smul_XH])
  have hd₀ := three_mul_card_orbits (X := XH K M H) _ (mk_βΓ_ne_one ω hω) (mk_βΓ_pow_three ω hω)
  have hd₁ := two_mul_card_orbits (X := XH K M H) _ (mk_αΓ_ne_one ω hω) (mk_αΓ_sq ω hω)
  rw [hfixβ, card_orbits_eq_of_classifying (X := XH K M H) _
    (isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, mk_βΓ_pow_three ω hω⟩) c₃ hc₃s
    (fun s s' => by simp only [mk_pow_smul_XH]; exact hc₃ s s')] at hd₀
  rw [hfixα, card_orbits_eq_of_classifying (X := XH K M H) _
    (isOfFinOrder_iff_pow_eq_one.2 ⟨2, by norm_num, mk_αΓ_sq ω hω⟩) c₂ hc₂s
    (fun s s' => by simp only [mk_pow_smul_XH]; exact hc₂ s s')] at hd₁
  refine ⟨h1, by rw [hsumZ, hm], ?_, ?_⟩
  · rw [hX', h3'] at hd₀
    omega
  · rw [hX', h2'] at hd₁
    omega

end Census

section Main

open AlgebraicCurve ModularCurve MulAction

theorem exists_omega (K : Type*) [Field K] [IsAlgClosed K] : ∃ ω : K, ω ^ 2 + ω + 1 = 0 := by
  obtain ⟨ω, hω⟩ := IsAlgClosed.exists_root (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial K)
    (by
      have : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial K).degree = 2 := by compute_degree!
      rw [this]; norm_num)
  exact ⟨ω, by simpa using hω⟩

set_option maxHeartbeats 3200000 in
theorem census (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (hM : ¬ 2 ∣ M)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K 2]
    (x : qExpFunctionFieldC K (CohCarrier.GammaH M H))
    (hx : (x : LaurentSeries K) = jqModC K)
    (S : Finset (Place K (qExpFunctionFieldC K (CohCarrier.GammaH M H))))
    (hS : ∀ Q, Q ∈ S ↔ 0 < Q.ord x) :
    (∀ Q ∈ S, Q.ord x = 1 ∨ Q.ord x = 3 ∨ Q.ord x = 4 ∨ Q.ord x = 6 ∨ Q.ord x = 12) ∧
    (∑ Q ∈ S, Q.ord x = ((CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)).index : ℤ)) ∧
    ((S.filter fun Q => Q.ord x = 1).card + (S.filter fun Q => Q.ord x = 3).card +
        2 * (S.filter fun Q => Q.ord x = 4).card + 2 * (S.filter fun Q => Q.ord x = 6).card +
        4 * (S.filter fun Q => Q.ord x = 12).card =
      Nat.card (DoubleCoset.Quotient
        (CohCarrier.GammaH M H : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
        (Subgroup.zpowers (ModularGroup.S * ModularGroup.T) :
          Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)))) ∧
    ((S.filter fun Q => Q.ord x = 1).card + 3 * (S.filter fun Q => Q.ord x = 3).card +
        2 * (S.filter fun Q => Q.ord x = 4).card + 4 * (S.filter fun Q => Q.ord x = 6).card +
        6 * (S.filter fun Q => Q.ord x = 12).card =
      Nat.card (DoubleCoset.Quotient
        (CohCarrier.GammaH M H : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
        (Subgroup.zpowers ModularGroup.S : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)))) := by
  classical
  obtain ⟨ω, hω⟩ := exists_omega K
  have hMK : (M : K) ≠ 0 := fun h => hM ((CharP.cast_eq_zero_iff K 2 M).mp h)

  have hS' : ∀ Q, Q ∈ S ↔
      0 < Q.ord (x - algebraMap K (qExpFunctionFieldC K (CohCarrier.GammaH M H)) 0) := by
    intro Q; rw [map_zero, sub_zero]; exact hS Q
  obtain ⟨f, hf1, hf2, hf3, hf4⟩ :=
    ModularCurve.exists_orbitMap_torsionOrbit_places_qExpFunctionFieldC_gammaH K M hMK H 0 (E₀ K)
      (E₀_j K) x hx S hS'
  simp only [map_zero, sub_zero] at hf4

  obtain ⟨hcardX, ⟨c₃, hc₃s, hc₃⟩, ⟨c₂, hc₂s, hc₂⟩⟩ :=
    WeierstrassCurve.natCard_torsionOrbit_and_exists_surjective_doubleCoset_of_char_two
      (Units.mk0 ω (omega_ne_zero ω hω)) (by simpa using omega_pow_three ω hω)
      (by simpa using omega_ne_one ω hω) M hMK H

  have hc₃' : ∀ s s' : XH K M H, c₃ s = c₃ s' ↔ ∃ k : ℕ, βΓ ω hω ^ k • s = s' := by
    intro s s'
    rw [hc₃, ← exists_pow_forall_exists_heq_iff H (βΓ ω hω) s s']
    rfl
  have hc₂' : ∀ s s' : XH K M H, c₂ s = c₂ s' ↔ ∃ k : ℕ, αΓ ω hω ^ k • s = s' := by
    intro s s'
    rw [hc₂, ← exists_pow_forall_exists_heq_iff H (αΓ ω hω) s s']
    rfl
  exact census_core ω hω H x S f hf1 hf2 hf3 hf4 _ hcardX c₃ hc₃s hc₃' c₂ hc₂s hc₂'

end Main

end P2MKcCENH2
p2m_reactivate "P2MW.S_ModularCurve_ord_census_qExpFunctionFieldC_gammaH_of_char_two.P2MKcCENH2"

open AlgebraicCurve ModularCurve
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (hM : ¬ 2 ∣ M)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K 2]
    (x : qExpFunctionFieldC K (CohCarrier.GammaH M H))
    (hx : (x : LaurentSeries K) = jqModC K)
    (S : Finset (Place K (qExpFunctionFieldC K (CohCarrier.GammaH M H))))
    (hS : ∀ Q, Q ∈ S ↔ 0 < Q.ord x) :
    (∀ Q ∈ S, Q.ord x = 1 ∨ Q.ord x = 3 ∨ Q.ord x = 4 ∨ Q.ord x = 6 ∨ Q.ord x = 12) ∧
    (∑ Q ∈ S, Q.ord x = ((CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)).index : ℤ)) ∧
    ((S.filter fun Q => Q.ord x = 1).card + (S.filter fun Q => Q.ord x = 3).card +
        2 * (S.filter fun Q => Q.ord x = 4).card + 2 * (S.filter fun Q => Q.ord x = 6).card +
        4 * (S.filter fun Q => Q.ord x = 12).card =
      Nat.card (DoubleCoset.Quotient
        (CohCarrier.GammaH M H : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
        (Subgroup.zpowers (ModularGroup.S * ModularGroup.T) :
          Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)))) ∧
    ((S.filter fun Q => Q.ord x = 1).card + 3 * (S.filter fun Q => Q.ord x = 3).card +
        2 * (S.filter fun Q => Q.ord x = 4).card + 4 * (S.filter fun Q => Q.ord x = 6).card +
        6 * (S.filter fun Q => Q.ord x = 12).card =
      Nat.card (DoubleCoset.Quotient
        (CohCarrier.GammaH M H : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
        (Subgroup.zpowers ModularGroup.S : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)))) :=
  P2MKcCENH2.census M H hM K x hx S hS

end S_ModularCurve_ord_census_qExpFunctionFieldC_gammaH_of_char_two
end P2MW
export P2MW.S_ModularCurve_ord_census_qExpFunctionFieldC_gammaH_of_char_two (solution)
