-- Prove2me | solution 1 for ModularCurve.ord_census_qExpFunctionFieldC_gammaH_of_char_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/9c0c8dd3-c07e-5fee-965d-43998d670be9

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_ModularCurve_exists_orbitMap_torsionOrbit_places_qExpFunctionFieldC_gammaH
import Theorems.Thm_WeierstrassCurve_exists_addMonoidHom_i_tau_vcInvFun_of_char_three
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Theorems.Thm_Function_orbitCensus_of_dihedralThree_relations
import Theorems.Thm_MulAction_card_mul_natCard_orbitRel_quotient_eq_of_natCard_eq_prime
import Theorems.Thm_CohCarrier_exists_bottomRow_eq_and_torsionOrbit_bottomRow_eq_iff
import Theorems.Thm_AddCommGroup_exists_torsionBy_coords_of_dicyclic_relations
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_census_qExpFunctionFieldC_gammaH_of_char_three
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
set_option synthInstance.maxHeartbeats 1600000

open WeierstrassCurve WeierstrassCurve.Affine ModularCurve AlgebraicCurve
open scoped MatrixGroups

noncomputable section

namespace P2MKcCEN3H

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

theorem val_sub_nsmul {P : A} (hP : M • P = 0) (u v : ZMod M) :
    (u - v).val • P = u.val • P - v.val • P := by
  rw [sub_eq_add_neg, val_add_nsmul hP, val_neg_nsmul hP, ← sub_eq_add_neg]

theorem val_one_nsmul {P : A} (hP : M • P = 0) : (1 : ZMod M).val • P = P := by
  have := val_natCast_nsmul hP 1
  rwa [Nat.cast_one, one_nsmul] at this

theorem nsmul_of_addOrderOf_eq {P : A} (hP : addOrderOf P = M) : M • P = 0 := by
  rw [← hP]; exact addOrderOf_nsmul_eq_zero P

theorem nsmul_val_nsmul {P : A} (hP : M • P = 0) (n : ℕ) (u : ZMod M) :
    n • (u.val • P) = ((n : ZMod M) * u).val • P := by
  rw [val_mul_nsmul hP, val_natCast_nsmul (by rw [nsmul_left_comm, hP, nsmul_zero])]

variable (H : Subgroup (ZMod M)ˣ)

abbrev orb (P : A) : Set A :=
  {T | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧ T = (u : ZMod M).val • P}

abbrev XH (A : Type*) [AddCommGroup A] (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Type _ :=
  {s : Set A // ∃ P : A, addOrderOf P = M ∧ s = orb H P}

theorem neg_one_mem_Hpm : (-1 : (ZMod M)ˣ) ∈ H ⊔ Subgroup.zpowers (-1) :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem mem_orb_self {P : A} (hP : M • P = 0) : P ∈ orb H P :=
  ⟨1, Subgroup.one_mem _, by rw [Units.val_one, val_one_nsmul hP]⟩

theorem nsmul_mem_orb {P : A} (hP : M • P = 0) {T : A} (hT : T ∈ orb H P) : M • T = 0 := by
  obtain ⟨u, -, rfl⟩ := hT
  rw [nsmul_left_comm, hP, nsmul_zero]

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
  rw [Units.val_mul, val_mul_nsmul hP, Units.val_neg, Units.val_one, val_neg_nsmul, val_one_nsmul]
  all_goals rw [nsmul_left_comm, hP, nsmul_zero]

theorem orb_neg {P : A} (hP : M • P = 0) : orb H (-P) = orb H P :=
  orb_eq_of_mem H hP (neg_mem_orb H hP (mem_orb_self H hP))

theorem image_orb {B : Type*} [AddCommGroup B] (m : A →+ B) (P : A) :
    m '' orb H P = orb H (m P) := by
  ext W
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨T, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, by rw [map_nsmul]⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨(u : ZMod M).val • P, ⟨u, hu, rfl⟩, by rw [map_nsmul]⟩

variable {H}

theorem XH.nsmul_eq_zero (s : XH A M H) {T : A} (hT : T ∈ s.1) : M • T = 0 := by
  obtain ⟨P, hP, hs⟩ := s.2
  rw [hs] at hT
  exact nsmul_mem_orb H (nsmul_of_addOrderOf_eq hP) hT

theorem XH.eq_orb_of_mem (s : XH A M H) {T : A} (hT : T ∈ s.1) : s.1 = orb H T := by
  obtain ⟨P, hP, hs⟩ := s.2
  rw [hs] at hT ⊢
  exact (orb_eq_of_mem H (nsmul_of_addOrderOf_eq hP) hT).symm

theorem XH.neg_mem (s : XH A M H) {T : A} (hT : T ∈ s.1) : -T ∈ s.1 := by
  obtain ⟨P, hP, hs⟩ := s.2
  rw [hs] at hT ⊢
  exact neg_mem_orb H (nsmul_of_addOrderOf_eq hP) hT

theorem XH.ext' {s s' : XH A M H} (h : s.1 = s'.1) : s = s' := Subtype.ext h

def mapX {B : Type*} [AddCommGroup B] (m : A →+ B) (hm : Function.Injective m) (s : XH A M H) :
    XH B M H :=
  ⟨m '' s.1, by
    obtain ⟨P, hP, hs⟩ := s.2
    exact ⟨m P, by rw [addOrderOf_injective m hm, hP], by rw [hs, image_orb]⟩⟩

@[scoped simp] theorem mapX_val {B : Type*} [AddCommGroup B] (m : A →+ B) (hm : Function.Injective m)
    (s : XH A M H) : (mapX m hm s).1 = m '' s.1 := rfl

theorem mapX_mapX {B C : Type*} [AddCommGroup B] [AddCommGroup C] (m : B →+ C) (m' : A →+ B)
    (hm : Function.Injective m) (hm' : Function.Injective m') (s : XH A M H) :
    mapX m hm (mapX m' hm' s) = mapX (m.comp m') (hm.comp hm') s :=
  XH.ext' (by simp [Set.image_image])

theorem mapX_congr {B : Type*} [AddCommGroup B] {m m' : A →+ B} (hm : Function.Injective m)
    (hm' : Function.Injective m') (h : m = m') (s : XH A M H) : mapX m hm s = mapX m' hm' s := by
  subst h; rfl

theorem mapX_id' {m : A →+ A} (hm : Function.Injective m) (h : ∀ a, m a = a) (s : XH A M H) :
    mapX m hm s = s := by
  apply XH.ext'
  have : (m : A → A) = id := funext h
  simp [this]

theorem mapX_neg' {m : A →+ A} (hm : Function.Injective m) (h : ∀ a, m a = -a) (s : XH A M H) :
    mapX m hm s = s := by
  apply XH.ext'
  obtain ⟨P, hP, hs⟩ := s.2
  rw [mapX_val, hs, image_orb, h, orb_neg H (nsmul_of_addOrderOf_eq hP)]

theorem mapX_eq_of_forall_mem {B : Type*} [AddCommGroup B] (m : A →+ B) (hm : Function.Injective m)
    (s : XH A M H) (s' : XH B M H) (h : ∀ T ∈ s.1, m T ∈ s'.1) : mapX m hm s = s' := by
  apply XH.ext'
  obtain ⟨P, hP, hs⟩ := s.2
  have hPs : P ∈ s.1 := by rw [hs]; exact mem_orb_self H (nsmul_of_addOrderOf_eq hP)
  rw [mapX_val, hs, image_orb, XH.eq_orb_of_mem s' (h P hPs)]

theorem mapX_injective {B : Type*} [AddCommGroup B] (m : A →+ B) (hm : Function.Injective m) :
    Function.Injective (mapX (M := M) (H := H) m hm) := fun s s' h =>
  XH.ext' ((Set.image_injective.mpr hm) (congrArg Subtype.val h))

theorem finite_XH [Finite (Submodule.torsionBy ℤ A M)] : Finite (XH A M H) := by
  have hsub : ∀ (s : XH A M H) (x : A), x ∈ s.1 → x ∈ Submodule.torsionBy ℤ A M := by
    intro s x hx
    rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
    exact XH.nsmul_eq_zero s hx
  refine Finite.of_injective
    (fun s : XH A M H => ({x : Submodule.torsionBy ℤ A M | (x : A) ∈ s.1} : Set _)) ?_
  intro s s' h
  simp only at h
  apply XH.ext'
  ext x
  constructor
  · intro hx
    have : (⟨x, hsub s x hx⟩ : Submodule.torsionBy ℤ A M) ∈
        ({x : Submodule.torsionBy ℤ A M | (x : A) ∈ s'.1} : Set _) := by
      rw [← h]; exact hx
    exact this
  · intro hx
    have : (⟨x, hsub s' x hx⟩ : Submodule.torsionBy ℤ A M) ∈
        ({x : Submodule.torsionBy ℤ A M | (x : A) ∈ s.1} : Set _) := by
      rw [h]; exact hx
    exact this

end Orb

section Operators

variable {A : Type*} [AddCommGroup A] {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}
  (α β : A →+ A) (hαα : ∀ T, α (α T) = -T) (hβ : ∀ T, β (β T) + β T + T = 0)
  (hαβ : ∀ T, α (β T) = β (β (α T)))

include hαα in
theorem α_injective : Function.Injective α := fun a b h => by
  have h' := congrArg α h
  rwa [hαα, hαα, neg_inj] at h'

include hβ in
theorem βββ (T : A) : β (β (β T)) = T := by
  have h1 := hβ (β T)
  have h3 := hβ T
  have : β (β (β T)) - T = (β (β (β T)) + β (β T) + β T) - (β (β T) + β T + T) := by abel
  rw [h1, h3, sub_zero] at this
  exact sub_eq_zero.mp this

include hβ in
theorem β_injective : Function.Injective β := fun a b h => by
  have h' := congrArg (fun x => β (β x)) h
  simp only [βββ β hβ] at h'
  exact h'

def aX (s : XH A M H) : XH A M H := mapX α (α_injective α hαα) s

def bX (s : XH A M H) : XH A M H := mapX β (β_injective β hβ) s

theorem aX_val (s : XH A M H) : (aX α hαα s).1 = α '' s.1 := rfl
theorem bX_val (s : XH A M H) : (bX β hβ s).1 = β '' s.1 := rfl

theorem aX_aX (s : XH A M H) : aX α hαα (aX α hαα s) = s := by
  unfold aX
  rw [mapX_mapX]
  exact mapX_neg' _ (fun a => by simp [hαα]) s

theorem bX_bX_bX (s : XH A M H) : bX β hβ (bX β hβ (bX β hβ s)) = s := by
  unfold bX
  rw [mapX_mapX, mapX_mapX]
  exact mapX_id' _ (fun a => by simp [βββ β hβ]) s

include hαβ in
theorem aX_bX (s : XH A M H) : aX α hαα (bX β hβ s) = bX β hβ (bX β hβ (aX α hαα s)) := by
  unfold aX bX
  rw [mapX_mapX, mapX_mapX, mapX_mapX]
  exact mapX_congr _ _ (AddMonoidHom.ext fun T => by simp [hαβ]) s

theorem mapX_six {m : A →+ A} (hm : m = AddMonoidHom.id _ ∨ m = α ∨ m = β ∨ m = β.comp β ∨
      m = α.comp β ∨ m = α.comp (β.comp β)) (hminj : Function.Injective m) (s : XH A M H) :
    mapX m hminj s = s ∨ mapX m hminj s = aX α hαα s ∨ mapX m hminj s = bX β hβ s ∨
      mapX m hminj s = bX β hβ (bX β hβ s) ∨ mapX m hminj s = aX α hαα (bX β hβ s) ∨
      mapX m hminj s = aX α hαα (bX β hβ (bX β hβ s)) := by
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (mapX_id' _ (fun _ => rfl) s)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    unfold bX; rw [mapX_mapX]
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
    unfold aX bX; rw [mapX_mapX]
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
    unfold aX bX; rw [mapX_mapX, mapX_mapX]
    exact mapX_congr _ _ (by ext; rfl) s

include hαα hβ in
theorem injective_six {m : A →+ A} (hm : m = AddMonoidHom.id _ ∨ m = α ∨ m = β ∨ m = β.comp β ∨
      m = α.comp β ∨ m = α.comp (β.comp β)) : Function.Injective m := by
  have hαi := α_injective α hαα
  have hβi := β_injective β hβ
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun a b h => h
  · exact hαi
  · exact hβi
  · exact hβi.comp hβi
  · exact hαi.comp hβi
  · exact hαi.comp (hβi.comp hβi)

theorem exists_six_of_mem (s s' : XH A M H)
    (h : s' = s ∨ s' = aX α hαα s ∨ s' = bX β hβ s ∨ s' = bX β hβ (bX β hβ s) ∨
      s' = aX α hαα (bX β hβ s) ∨ s' = aX α hαα (bX β hβ (bX β hβ s))) :
    ∃ (m : A →+ A) (hm : m = AddMonoidHom.id _ ∨ m = α ∨ m = β ∨ m = β.comp β ∨
      m = α.comp β ∨ m = α.comp (β.comp β)), s'.1 = m '' s.1 := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨AddMonoidHom.id _, Or.inl rfl, by simp⟩
  · exact ⟨α, Or.inr (Or.inl rfl), rfl⟩
  · exact ⟨β, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
  · exact ⟨β.comp β, Or.inr (Or.inr (Or.inr (Or.inl rfl))), by simp [bX_val, Set.image_image]⟩
  · exact ⟨α.comp β, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
      by simp [aX_val, bX_val, Set.image_image]⟩
  · exact ⟨α.comp (β.comp β), Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))),
      by simp [aX_val, bX_val, Set.image_image]⟩

end Operators

section CharThree

variable {K : Type*} [Field K] [DecidableEq K]

abbrev E0 (K : Type*) [Field K] : WeierstrassCurve K := ⟨0, 0, 0, -1, 0⟩

theorem three_eq_zero [CharP K 3] : (3 : K) = 0 := by simpa using CharP.cast_eq_zero K 3

theorem E0_Δ : (E0 K).Δ = 64 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

theorem E0_c₄ : (E0 K).c₄ = 48 := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

theorem isElliptic_E0 [CharP K 3] : (E0 K).IsElliptic := by
  refine ⟨?_⟩
  rw [E0_Δ, isUnit_iff_ne_zero]
  have h3 : (3 : K) = 0 := three_eq_zero
  intro h
  have : (1 : K) = 0 := by linear_combination h - 21 * h3
  exact one_ne_zero this

theorem E0_j [CharP K 3] : letI := isElliptic_E0 (K := K); (E0 K).j = 0 := by
  letI := isElliptic_E0 (K := K)
  rw [WeierstrassCurve.j_eq_zero_iff, E0_c₄]
  have h3 : (3 : K) = 0 := three_eq_zero
  linear_combination 16 * h3

theorem baseChange_self (W : WeierstrassCurve K) : (W⁄K) = W.toAffine := by
  show (W.baseChange K).toAffine = W.toAffine
  rw [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]

theorem eq_of_heq_heq {W : WeierstrassCurve K} {γ : VariableChange K} {T : W.toAffine.Point}
    {X Y : W.toAffine.Point} (h1 : HEq (Point.vcInvFun γ W.toAffine T) X)
    (h2 : HEq (Point.vcInvFun γ W.toAffine T) Y) : X = Y :=
  eq_of_heq (h1.symm.trans h2)

theorem forall_mem_of_forall_exists_heq {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}
    {W : WeierstrassCurve K} (γ : VariableChange K)
    (φ : W.toAffine.Point →+ W.toAffine.Point)
    (hφ : (∀ T, HEq (Point.vcInvFun γ W.toAffine T) (φ T)) ∨
      (∀ T, HEq (Point.vcInvFun γ W.toAffine T) (-(φ T))))
    (s s' : XH W.toAffine.Point M H)
    (h : ∀ T ∈ s.1, ∃ T' ∈ s'.1, HEq (Point.vcInvFun γ W.toAffine T) T') :
    ∀ T ∈ s.1, φ T ∈ s'.1 := by
  intro T hT
  obtain ⟨T', hT', hheq⟩ := h T hT
  rcases hφ with hφ | hφ
  · rwa [eq_of_heq_heq (hφ T) hheq]
  · have : -(φ T) = T' := eq_of_heq_heq (hφ T) hheq
    have h' : φ T = -T' := by rw [← this, neg_neg]
    rw [h']
    exact XH.neg_mem s' hT'

end CharThree

section Level

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

abbrev V (M : ℕ) : Type := ZMod M × ZMod M

abbrev ent (M : ℕ) (g : SL(2, ℤ)) (i j : Fin 2) : ZMod M := ((g i j : ℤ) : ZMod M)

abbrev row (M : ℕ) (g : SL(2, ℤ)) : V M := (ent M g 1 0, ent M g 1 1)

def ract (v : V M) (g : SL(2, ℤ)) : V M :=
  (v.1 * ent M g 0 0 + v.2 * ent M g 1 0, v.1 * ent M g 0 1 + v.2 * ent M g 1 1)

theorem ent_mul (g h : SL(2, ℤ)) (i j : Fin 2) :
    ent M (g * h) i j = ent M g i 0 * ent M h 0 j + ent M g i 1 * ent M h 1 j := by
  simp only [ent, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  ring

theorem ent_one (i j : Fin 2) : ent M 1 i j = if i = j then 1 else 0 := by
  simp only [ent, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]
  split_ifs <;> simp

theorem ent_neg (g : SL(2, ℤ)) (i j : Fin 2) : ent M (-g) i j = -ent M g i j := by
  simp only [ent, Matrix.SpecialLinearGroup.coe_neg]
  rw [Matrix.neg_apply]
  push_cast
  rfl

theorem ract_one (v : V M) : ract v 1 = v := by
  simp only [ract, ent_one]
  simp

theorem ract_mul (v : V M) (g h : SL(2, ℤ)) : ract v (g * h) = ract (ract v g) h := by
  simp only [ract, ent_mul]
  ext <;> ring

theorem ract_neg_one (v : V M) : ract v (-1) = -v := by
  simp only [ract, ent_neg, ent_one]
  ext <;> simp

theorem row_eq_ract (g : SL(2, ℤ)) : row M g = ract ((0 : ZMod M), (1 : ZMod M)) g := by
  simp [ract]

theorem row_one : row M 1 = ((0 : ZMod M), (1 : ZMod M)) := by
  rw [row_eq_ract, ract_one]

def ractHom (M : ℕ) (g : SL(2, ℤ)) : V M →+ V M where
  toFun v := ract v g
  map_zero' := by simp [ract]
  map_add' v w := by simp only [ract]; ext <;> simp <;> ring

@[scoped simp] theorem ractHom_apply (g : SL(2, ℤ)) (v : V M) : ractHom M g v = ract v g := rfl

theorem ract_injective (g : SL(2, ℤ)) : Function.Injective (fun v : V M => ract v g) := by
  intro v w h
  have := congrArg (fun z => ract z g⁻¹) h
  simpa only [← ract_mul, mul_inv_cancel, ract_one] using this

theorem ractHom_injective (g : SL(2, ℤ)) : Function.Injective (ractHom M g) := ract_injective g

theorem ractHom_comp (g h : SL(2, ℤ)) :
    (ractHom M h).comp (ractHom M g) = ractHom M (g * h) := by
  ext v <;> simp [ract_mul]

variable (H)

scoped instance actXV : MulAction SL(2, ℤ) (XH (V M) M H) where
  smul g s := mapX (ractHom M g⁻¹) (ractHom_injective g⁻¹) s
  one_smul s := mapX_id' _ (fun v => by simp [ract_one]) s
  mul_smul g h s := by
    show mapX (ractHom M (g * h)⁻¹) _ s = mapX (ractHom M g⁻¹) _ (mapX (ractHom M h⁻¹) _ s)
    rw [mapX_mapX]
    exact mapX_congr _ _ (by rw [ractHom_comp, mul_inv_rev]) s

variable {H}

private theorem _root_.P2MKcCEN3H.smul_def (g : SL(2, ℤ)) (s : XH (V M) M H) :
    g • s = mapX (ractHom M g⁻¹) (ractHom_injective g⁻¹) s := rfl

p2m_export "P2MKcCEN3H" "smul_def"
theorem smul_val (g : SL(2, ℤ)) (s : XH (V M) M H) :
    (g • s).1 = (fun v => ract v g⁻¹) '' s.1 := rfl

theorem neg_one_smul' (s : XH (V M) M H) : (-1 : SL(2, ℤ)) • s = s := by
  rw [smul_def]
  refine mapX_neg' _ (fun v => ?_) s
  rw [ractHom_apply]
  have : (-1 : SL(2, ℤ))⁻¹ = -1 := by rw [inv_eq_iff_mul_eq_one, neg_mul_neg, one_mul]
  rw [this, ract_neg_one]

theorem neg_smul' (g : SL(2, ℤ)) (s : XH (V M) M H) : (-g) • s = g • s := by
  rw [← neg_one_mul, mul_smul, neg_one_smul']

section WithLevel

variable (hL1 : ∀ v : V M, addOrderOf v = M →
      ∃ a : SL(2, ℤ), ((a 1 0 : ℤ) : ZMod M) = v.1 ∧ ((a 1 1 : ℤ) : ZMod M) = v.2)
  (hL2 : ∀ a : SL(2, ℤ), addOrderOf (row M a) = M)
  (hL3 : ∀ a b : SL(2, ℤ), orb H (row M a) = orb H (row M b) ↔
      b * a⁻¹ ∈ CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1))

def X0 (H : Subgroup (ZMod M)ˣ) (hL2 : ∀ a : SL(2, ℤ), addOrderOf (row M a) = M) : XH (V M) M H :=
  ⟨orb H ((0 : ZMod M), (1 : ZMod M)), _, by simpa [row_one] using hL2 1, rfl⟩

theorem X0_val : (X0 H hL2).1 = orb H (row M 1) := by rw [row_one]; rfl

theorem smul_X0_val (g : SL(2, ℤ)) : (g • X0 H hL2).1 = orb H (row M g⁻¹) := by
  rw [smul_val, show (X0 H hL2).1 = orb H ((0 : ZMod M), 1) from rfl,
    show (fun v : V M => ract v g⁻¹) = ractHom M g⁻¹ from rfl, image_orb, ractHom_apply, ← row_eq_ract]

include hL1 in
theorem exists_smul_X0_eq (s : XH (V M) M H) : ∃ g : SL(2, ℤ), g • X0 H hL2 = s := by
  obtain ⟨v, hv, hs⟩ := s.2
  obtain ⟨a, ha1, ha2⟩ := hL1 v hv
  refine ⟨a⁻¹, XH.ext' ?_⟩
  rw [smul_X0_val, inv_inv, hs]
  congr 1
  exact Prod.ext ha1 ha2

include hL3 in
theorem stabilizer_X0 :
    MulAction.stabilizer SL(2, ℤ) (X0 H hL2) = CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1) := by
  ext g
  have h3 := hL3 1 g⁻¹
  rw [inv_one, mul_one] at h3
  rw [MulAction.mem_stabilizer_iff, ← Subgroup.inv_mem_iff (x := g), ← h3, ← X0_val (hL2 := hL2),
    ← smul_X0_val (hL2 := hL2)]
  exact ⟨fun h => congrArg Subtype.val h.symm, fun h => (XH.ext' h).symm⟩

include hL1 hL2 hL3 in

theorem natCard_XV :
    Nat.card (XH (V M) M H) = (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)).index := by
  haveI : MulAction.IsPretransitive SL(2, ℤ) (XH (V M) M H) := ⟨fun s t => by
    obtain ⟨g, rfl⟩ := exists_smul_X0_eq hL1 hL2 s
    obtain ⟨h, rfl⟩ := exists_smul_X0_eq hL1 hL2 t
    exact ⟨h * g⁻¹, by rw [mul_smul, inv_smul_smul]⟩⟩
  rw [Subgroup.index_eq_card, ← stabilizer_X0 hL2 hL3]
  have e1 : XH (V M) M H ≃ MulAction.orbit SL(2, ℤ) (X0 H hL2) :=
    (Equiv.Set.univ _).symm.trans (Equiv.setCongr (MulAction.orbit_eq_univ SL(2, ℤ) (X0 H hL2)).symm)
  exact Nat.card_congr (e1.trans (MulAction.orbitEquivQuotientStabilizer SL(2, ℤ) (X0 H hL2)))

theorem mem_zpowers_neg_one_iff (n : SL(2, ℤ)) :
    n ∈ Subgroup.zpowers (-1 : SL(2, ℤ)) ↔ n = 1 ∨ n = -1 := by
  have hord : orderOf (-1 : SL(2, ℤ)) = 2 := orderOf_eq_prime (by rw [neg_one_sq]) (by decide)
  constructor
  · rintro ⟨k, rfl⟩
    dsimp only
    rw [← zpow_mod_orderOf, hord]
    have h0 : (0 : ℤ) ≤ k % 2 := Int.emod_nonneg _ (by norm_num)
    have h1 : k % 2 < 2 := Int.emod_lt_of_pos _ (by norm_num)
    interval_cases (k % 2)
    · exact Or.inl (by simp)
    · exact Or.inr (by simp)
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

scoped instance normal_zpowers_neg_one : (Subgroup.zpowers (-1 : SL(2, ℤ))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rcases (mem_zpowers_neg_one_iff n).mp hn with rfl | rfl
  · rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
  · rw [mul_neg_one, neg_mul, mul_inv_cancel]; exact Subgroup.mem_zpowers _

theorem mem_sup_zpowers_neg_one_iff (Γ : Subgroup SL(2, ℤ)) (σ : SL(2, ℤ)) :
    σ ∈ Γ ⊔ Subgroup.zpowers (-1) ↔ σ ∈ Γ ∨ -σ ∈ Γ := by
  constructor
  · intro h
    have h' : σ ∈ ((Γ ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) : Set SL(2, ℤ)) := h
    rw [Subgroup.mul_normal] at h'
    obtain ⟨γ, hγ, n, hn, rfl⟩ := h'
    rcases (mem_zpowers_neg_one_iff n).mp hn with rfl | rfl
    · exact Or.inl (by simpa using hγ)
    · exact Or.inr (by simpa using hγ)
  · rintro (h | h)
    · exact Subgroup.mem_sup_left h
    · have : σ = -σ * -1 := by rw [mul_neg_one, neg_neg]
      rw [this]
      exact Subgroup.mul_mem_sup h (Subgroup.mem_zpowers _)

include hL1 hL2 hL3 in

theorem natCard_doubleCoset_eq (K : Subgroup SL(2, ℤ)) (hK : (-1 : SL(2, ℤ)) ∈ K) :
    Nat.card (DoubleCoset.Quotient (CohCarrier.GammaH M H : Set SL(2, ℤ)) (K : Set SL(2, ℤ))) =
      Nat.card (MulAction.orbitRel.Quotient K (XH (V M) M H)) := by
  set x0 := X0 H hL2 with hx0
  have hstab : ∀ σ : SL(2, ℤ), σ • x0 = x0 → σ ∈ CohCarrier.GammaH M H ∨ -σ ∈ CohCarrier.GammaH M H := by
    intro σ hσ
    have : σ ∈ MulAction.stabilizer SL(2, ℤ) x0 := hσ
    rw [hx0, stabilizer_X0 hL2 hL3] at this
    exact (mem_sup_zpowers_neg_one_iff _ σ).mp this
  let ψ : DoubleCoset.Quotient (CohCarrier.GammaH M H : Set SL(2, ℤ)) (K : Set SL(2, ℤ)) →
      MulAction.orbitRel.Quotient K (XH (V M) M H) :=
    Quotient.lift (fun a => (Quotient.mk _ (a⁻¹ • x0) : MulAction.orbitRel.Quotient K (XH (V M) M H)))
      (by
        intro a b hab
        obtain ⟨h, hh, k, hk, rfl⟩ := DoubleCoset.rel_iff.mp hab
        apply Quotient.sound

        change (MulAction.orbitRel K (XH (V M) M H)) (a⁻¹ • x0) ((h * a * k)⁻¹ • x0)
        rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
        refine ⟨⟨k, hk⟩, ?_⟩
        rw [Subgroup.mk_smul, mul_inv_rev, mul_inv_rev, mul_smul, mul_smul, smul_inv_smul]
        have hh' : h⁻¹ ∈ MulAction.stabilizer SL(2, ℤ) x0 := by
          rw [hx0, stabilizer_X0 hL2 hL3]
          exact Subgroup.mem_sup_left (Subgroup.inv_mem _ hh)
        rw [MulAction.mem_stabilizer_iff.mp hh'])
  refine Nat.card_eq_of_bijective ψ ⟨?_, ?_⟩
  · intro p q hpq
    induction p using Quotient.inductionOn with
    | h a =>
    induction q using Quotient.inductionOn with
    | h b =>
    have h1 : (Quotient.mk _ (a⁻¹ • x0) : MulAction.orbitRel.Quotient K (XH (V M) M H)) =
        Quotient.mk _ (b⁻¹ • x0) := hpq
    obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp (Quotient.exact h1))

    rw [Subgroup.smul_def] at hk
    have hσ : (a * (k : SL(2, ℤ)) * b⁻¹) • x0 = x0 := by
      rw [mul_smul, mul_smul, hk, smul_inv_smul]
    apply Quotient.sound
    change (DoubleCoset.setoid _ _) a b
    rw [DoubleCoset.rel_iff]
    rcases hstab _ hσ with h | h
    · refine ⟨(a * k * b⁻¹)⁻¹, Subgroup.inv_mem _ h, k, k.2, ?_⟩
      group
    · refine ⟨(-(a * k * b⁻¹))⁻¹, Subgroup.inv_mem _ h, -k, ?_, ?_⟩
      · rw [← neg_one_mul]; exact Subgroup.mul_mem _ hK k.2
      · have e1 : (-(a * (k : SL(2, ℤ)) * b⁻¹))⁻¹ = -((a * (k : SL(2, ℤ)) * b⁻¹)⁻¹) := by
          rw [inv_eq_iff_mul_eq_one, neg_mul_neg, mul_inv_cancel]
        rw [e1]
        simp only [neg_mul, mul_neg, neg_neg]
        group
  · intro q
    induction q using Quotient.inductionOn with
    | h s =>
    obtain ⟨g, hg⟩ := exists_smul_X0_eq hL1 hL2 s
    refine ⟨Quotient.mk _ g⁻¹, ?_⟩
    change (Quotient.mk _ (g⁻¹⁻¹ • x0) : MulAction.orbitRel.Quotient K (XH (V M) M H)) = _
    rw [inv_inv, hg]

end WithLevel

section CycAct

variable {X : Type*} [MulAction SL(2, ℤ) X] (p : ℕ) [hp : Fact p.Prime] (g₀ : SL(2, ℤ))
  (htriv : ∀ s : X, (g₀ ^ p) • s = s)

include htriv in
theorem pow_smul_eq_pow_mod_smul (m : ℕ) (s : X) : (g₀ ^ m) • s = (g₀ ^ (m % p)) • s := by
  have key : ∀ q : ℕ, ((g₀ ^ p) ^ q) • s = s := by
    intro q
    induction q with
    | zero => rw [pow_zero, one_smul]
    | succ q ih => rw [pow_succ, mul_smul, htriv, ih]
  conv_lhs => rw [← Nat.mod_add_div m p, pow_add, pow_mul, mul_smul, key]

def cycHom : Multiplicative (ZMod p) →* Equiv.Perm X where
  toFun n := MulAction.toPerm (g₀ ^ (Multiplicative.toAdd n).val)
  map_one' := by
    ext s
    simp
  map_mul' a b := by
    ext s
    simp only [toAdd_mul, Equiv.Perm.coe_mul, Function.comp_apply, MulAction.toPerm_apply]
    rw [ZMod.val_add, ← pow_smul_eq_pow_mod_smul p g₀ htriv, pow_add, mul_smul]

@[reducible] def cycAct : MulAction (Multiplicative (ZMod p)) X := MulAction.compHom X (cycHom p g₀ htriv)

theorem cycAct_smul (n : Multiplicative (ZMod p)) (s : X) :
    (letI := cycAct p g₀ htriv; n • s) = (g₀ ^ (Multiplicative.toAdd n).val) • s := rfl

include htriv in
theorem fixedPoints_cycAct :
    (letI := cycAct p g₀ htriv; MulAction.fixedPoints (Multiplicative (ZMod p)) X) = {s | g₀ • s = s} := by
  letI := cycAct p g₀ htriv
  ext s
  rw [MulAction.mem_fixedPoints, Set.mem_setOf_eq]
  constructor
  · intro h
    have := h (Multiplicative.ofAdd 1)
    rw [cycAct_smul, toAdd_ofAdd, @ZMod.val_one p ⟨hp.out.one_lt⟩, pow_one] at this
    exact this
  · intro h n
    rw [cycAct_smul]
    induction (Multiplicative.toAdd n).val with
    | zero => rw [pow_zero, one_smul]
    | succ k ih => rw [pow_succ, mul_smul, h, ih]

include htriv in
theorem orbitRel_cycAct_eq :
    (letI := cycAct p g₀ htriv; MulAction.orbitRel (Multiplicative (ZMod p)) X) =
      MulAction.orbitRel (Subgroup.zpowers g₀) X := by
  letI := cycAct p g₀ htriv
  have hz : ∀ (z : ℤ) (s : X), ∃ m : ℕ, (g₀ ^ z) • s = (g₀ ^ m) • s := by
    intro z s
    have hinvtriv : ∀ t : X, (g₀ ^ p)⁻¹ • t = t := fun t => by
      rw [inv_smul_eq_iff, htriv]
    have key : ∀ (q : ℤ) (t : X), ((g₀ ^ p) ^ q) • t = t := by
      intro q t
      induction q using Int.induction_on with
      | zero => rw [zpow_zero, one_smul]
      | succ n ih => rw [zpow_add_one, mul_smul, htriv, ih]
      | pred n ih => rw [zpow_sub_one, mul_smul, hinvtriv, ih]
    refine ⟨(z % p).toNat, ?_⟩
    have h0 : 0 ≤ z % p := Int.emod_nonneg _ (by exact_mod_cast hp.out.ne_zero)
    conv_lhs => rw [← Int.emod_add_mul_ediv z p, zpow_add, zpow_mul, zpow_natCast, mul_smul, key,
      ← Int.toNat_of_nonneg h0, zpow_natCast]
  ext a b
  rw [MulAction.orbitRel_apply, MulAction.orbitRel_apply, MulAction.mem_orbit_iff,
    MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨⟨g₀ ^ ((Multiplicative.toAdd n).val : ℤ), Subgroup.zpow_mem_zpowers _ _⟩, ?_⟩
    rw [Subgroup.mk_smul, zpow_natCast, cycAct_smul]
  · rintro ⟨⟨k, hk⟩, rfl⟩
    obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    obtain ⟨m, hm⟩ := hz z b
    refine ⟨Multiplicative.ofAdd (m : ZMod p), ?_⟩
    rw [cycAct_smul, toAdd_ofAdd, ZMod.val_natCast, ← pow_smul_eq_pow_mod_smul p g₀ htriv,
      Subgroup.mk_smul, hm]

include htriv in

theorem card_mul_natCard_orbits [Finite X] :
    p * Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers g₀) X) =
      Nat.card X + (p - 1) * Nat.card {s : X // g₀ • s = s} := by
  letI := cycAct p g₀ htriv
  have h := MulAction.card_mul_natCard_orbitRel_quotient_eq_of_natCard_eq_prime
    (Multiplicative (ZMod p)) (X := X) hp.out
    (by rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card])
  have h1 : MulAction.orbitRel.Quotient (Multiplicative (ZMod p)) X =
      MulAction.orbitRel.Quotient (Subgroup.zpowers g₀) X := by
    unfold MulAction.orbitRel.Quotient
    rw [orbitRel_cycAct_eq p g₀ htriv]
  rw [h1, fixedPoints_cycAct p g₀ htriv] at h
  exact h

end CycAct

end Level

section Transport

variable {A : Type*} [AddCommGroup A] {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}
  (φ : A →+ A) (P : A) (hP : M • P = 0)

def iota : V M →+ A where
  toFun c := c.1.val • P + c.2.val • φ P
  map_zero' := by simp
  map_add' c d := by
    have hφP : M • φ P = 0 := by rw [← map_nsmul, hP, map_zero]
    simp only [Prod.fst_add, Prod.snd_add, val_add_nsmul hP, val_add_nsmul hφP]
    abel

theorem iota_apply (c : V M) : iota φ P hP c = c.1.val • P + c.2.val • φ P := rfl

theorem nsmul_iota (c : V M) : M • iota φ P hP c = 0 := by
  have hφP : M • φ P = 0 := by rw [← map_nsmul, hP, map_zero]
  rw [iota_apply, nsmul_add, nsmul_left_comm, hP, nsmul_zero, nsmul_left_comm, hφP, nsmul_zero,
    add_zero]

theorem iota_injective
    (hcoord : ∀ T : A, (M : ℤ) • T = 0 → ∃! c : ZMod M × ZMod M, c.1.val • P + c.2.val • φ P = T) :
    Function.Injective (iota φ P hP) := by
  intro c d h
  have hT : (M : ℤ) • iota φ P hP c = 0 := by rw [natCast_zsmul, nsmul_iota]
  exact (hcoord _ hT).unique rfl h.symm

theorem exists_iota_eq
    (hcoord : ∀ T : A, (M : ℤ) • T = 0 → ∃! c : ZMod M × ZMod M, c.1.val • P + c.2.val • φ P = T)
    (T : A) (hT : M • T = 0) : ∃ c : V M, iota φ P hP c = T := by
  obtain ⟨c, hc, -⟩ := hcoord T (by rw [natCast_zsmul, hT])
  exact ⟨c, hc⟩

def theta (hinj : Function.Injective (iota φ P hP)) (s : XH (V M) M H) : XH A M H :=
  mapX (iota φ P hP) hinj s

theorem theta_bijective
    (hcoord : ∀ T : A, (M : ℤ) • T = 0 → ∃! c : ZMod M × ZMod M, c.1.val • P + c.2.val • φ P = T) :
    Function.Bijective (theta (H := H) φ P hP (iota_injective φ P hP hcoord)) := by
  refine ⟨mapX_injective (iota φ P hP) (iota_injective φ P hP hcoord), fun t => ?_⟩
  obtain ⟨Q, hQ, ht⟩ := t.2
  obtain ⟨c, rfl⟩ := exists_iota_eq φ P hP hcoord Q (nsmul_of_addOrderOf_eq hQ)
  refine ⟨⟨orb H c, c, ?_, rfl⟩, XH.ext' ?_⟩
  · rwa [addOrderOf_injective _ (iota_injective φ P hP hcoord)] at hQ
  · show iota φ P hP '' orb H c = t.1
    rw [image_orb, ht]

theorem mapX_theta (hinj : Function.Injective (iota φ P hP)) (hφ : Function.Injective φ) (g₀ : SL(2, ℤ))
    (hequiv : ∀ v : V M, φ (iota φ P hP v) = iota φ P hP (ract v g₀)) (s : XH (V M) M H) :
    mapX φ hφ (theta φ P hP hinj s) = theta φ P hP hinj (g₀⁻¹ • s) := by
  unfold theta
  rw [smul_def, mapX_mapX, mapX_mapX]
  refine mapX_congr _ _ ?_ s
  ext v
  show φ (iota φ P hP v) = iota φ P hP (ract v g₀⁻¹⁻¹)
  rw [inv_inv, hequiv]

include hP in
theorem natCard_XH_eq
    (hcoord : ∀ T : A, (M : ℤ) • T = 0 → ∃! c : ZMod M × ZMod M, c.1.val • P + c.2.val • φ P = T) :
    Nat.card (XH A M H) = Nat.card (XH (V M) M H) :=
  (Nat.card_eq_of_bijective _ (theta_bijective (H := H) φ P hP hcoord)).symm

theorem natCard_fixed_eq
    (hcoord : ∀ T : A, (M : ℤ) • T = 0 → ∃! c : ZMod M × ZMod M, c.1.val • P + c.2.val • φ P = T)
    (hφ : Function.Injective φ) (g₀ : SL(2, ℤ))
    (hequiv : ∀ v : V M, φ (iota φ P hP v) = iota φ P hP (ract v g₀)) :
    Nat.card {t : XH A M H // mapX φ hφ t = t} = Nat.card {s : XH (V M) M H // g₀ • s = s} := by
  symm
  refine Nat.card_congr ((Equiv.ofBijective _ (theta_bijective (H := H) φ P hP hcoord)).subtypeEquiv ?_)
  intro s
  rw [Equiv.ofBijective_apply, mapX_theta φ P hP _ hφ g₀ hequiv,
    (theta_bijective (H := H) φ P hP hcoord).1.eq_iff, inv_smul_eq_iff, eq_comm]

end Transport

section Numerics

theorem natCard_subtype_eq_card_filter {X : Type*} [Fintype X] (p : X → Prop) [DecidablePred p] :
    Nat.card {x // p x} = (Finset.univ.filter p).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem sum_eq_of_mem_four {ι : Type*} (S : Finset ι) (g : ι → ℕ)
    (hg : ∀ p ∈ S, g p = 1 ∨ g p = 2 ∨ g p = 3 ∨ g p = 6) :
    ∑ p ∈ S, g p = (S.filter fun p => g p = 1).card + 2 * (S.filter fun p => g p = 2).card +
      3 * (S.filter fun p => g p = 3).card + 6 * (S.filter fun p => g p = 6).card := by
  classical
  simp only [Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rcases hg p hp with h | h | h | h <;> simp [h]

end Numerics

section Matrices

variable {M : ℕ} [NeZero M]

def nST : SL(2, ℤ) := ⟨!![0, 1; -1, -1], by norm_num [Matrix.det_fin_two_of]⟩

def nS : SL(2, ℤ) := ⟨!![0, 1; -1, 0], by norm_num [Matrix.det_fin_two_of]⟩

theorem nST_eq : nST = -(ModularGroup.S * ModularGroup.T) := by decide
theorem nS_eq : nS = -ModularGroup.S := by decide
theorem ST_pow_three : (ModularGroup.S * ModularGroup.T) ^ 3 = -1 := by decide
theorem S_pow_two : ModularGroup.S ^ 2 = -1 := by decide

theorem ract_nST (v : V M) : ract v nST = (-v.2, v.1 - v.2) := by
  simp only [ract, ent, nST]
  ext <;> simp <;> ring

theorem ract_nS (v : V M) : ract v nS = (-v.2, v.1) := by
  simp only [ract, ent, nS]
  ext <;> simp

variable {A : Type*} [AddCommGroup A]

theorem β_iota (β : A →+ A) (hβ : ∀ T, β (β T) + β T + T = 0) (P : A) (hP : M • P = 0) (v : V M) :
    β (iota β P hP v) = iota β P hP (ract v nST) := by
  have hβP : M • β P = 0 := by rw [← map_nsmul, hP, map_zero]
  have hββ : β (β P) = -(β P) - P := by
    have := hβ P
    rw [← sub_eq_zero]; rw [← this]; abel
  rw [ract_nST, iota_apply, iota_apply, map_add, map_nsmul, map_nsmul, hββ, val_neg_nsmul hP,
    val_sub_nsmul hβP, smul_sub, smul_neg]
  abel

theorem α_iota (α : A →+ A) (hαα : ∀ T, α (α T) = -T) (P : A) (hP : M • P = 0) (v : V M) :
    α (iota α P hP v) = iota α P hP (ract v nS) := by
  rw [ract_nS, iota_apply, iota_apply, map_add, map_nsmul, map_nsmul, hαα, val_neg_nsmul hP, smul_neg]
  abel

end Matrices

end P2MKcCEN3H
p2m_reactivate "P2MW.S_ModularCurve_ord_census_qExpFunctionFieldC_gammaH_of_char_three.P2MKcCEN3H"

open P2MKcCEN3H in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (hM : ¬ 3 ∣ M)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K 3]
    (x : qExpFunctionFieldC K (CohCarrier.GammaH M H))
    (hx : (x : LaurentSeries K) = jqModC K)
    (S : Finset (Place K (qExpFunctionFieldC K (CohCarrier.GammaH M H))))
    (hS : ∀ Q, Q ∈ S ↔ 0 < Q.ord x) :
    (∀ Q ∈ S, Q.ord x = 1 ∨ Q.ord x = 2 ∨ Q.ord x = 3 ∨ Q.ord x = 6) ∧
    (∑ Q ∈ S, Q.ord x = ((CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)).index : ℤ)) ∧
    ((S.filter fun Q => Q.ord x = 1).card + 2 * (S.filter fun Q => Q.ord x = 2).card +
        (S.filter fun Q => Q.ord x = 3).card + 2 * (S.filter fun Q => Q.ord x = 6).card =
      Nat.card (DoubleCoset.Quotient
        (CohCarrier.GammaH M H : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
        (Subgroup.zpowers (ModularGroup.S * ModularGroup.T) :
          Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)))) ∧
    ((S.filter fun Q => Q.ord x = 1).card + (S.filter fun Q => Q.ord x = 2).card +
        2 * (S.filter fun Q => Q.ord x = 3).card + 3 * (S.filter fun Q => Q.ord x = 6).card =
      Nat.card (DoubleCoset.Quotient
        (CohCarrier.GammaH M H : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
        (Subgroup.zpowers ModularGroup.S : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)))) := by
  classical

  have hMK : (M : K) ≠ 0 := fun h => hM ((CharP.cast_eq_zero_iff K 3 M).mp h)
  obtain ⟨i0, hi0⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : K) two_pos
  have hi0ne : i0 ≠ 0 := by
    rintro rfl
    norm_num at hi0
  set i : Kˣ := Units.mk0 i0 hi0ne with hidef
  have hi : (i : K) ^ 2 = -1 := by rw [hidef, Units.val_mk0, hi0]
  haveI hE : (E0 K).IsElliptic := isElliptic_E0
  have hj : (E0 K).j = 0 := E0_j

  have hS' : ∀ Q, Q ∈ S ↔ 0 < Q.ord (x - algebraMap K (qExpFunctionFieldC K (CohCarrier.GammaH M H)) (0 : K)) := by
    intro Q; rw [map_zero, sub_zero]; exact hS Q
  obtain ⟨f, hfS, hSf, hff, hord⟩ :=
    ModularCurve.exists_orbitMap_torsionOrbit_places_qExpFunctionFieldC_gammaH K M hMK H 0 (E0 K) hj
      x hx S hS'
  simp only [map_zero, sub_zero] at hord

  obtain ⟨α, β, hα, hβv, hαα, hβ, hαβ, hstab, hsix⟩ :=
    WeierstrassCurve.exists_addMonoidHom_i_tau_vcInvFun_of_char_three i hi

  obtain ⟨e⟩ : Nonempty (ZMod M × ZMod M ≃+ Submodule.torsionBy ℤ (E0 K).toAffine.Point M) := by
    have h := (E0 K).nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := K) hMK
    rwa [baseChange_self] at h
  haveI : Finite (Submodule.torsionBy ℤ (E0 K).toAffine.Point M) := Finite.of_equiv _ e.toEquiv
  haveI : Finite (XH (E0 K).toAffine.Point M H) := finite_XH
  letI : Fintype (XH (E0 K).toAffine.Point M H) := Fintype.ofFinite _
  haveI : Finite (XH (V M) M H) := finite_XH
  letI : Fintype (XH (V M) M H) := Fintype.ofFinite _

  have hc : ∀ s s' : XH (E0 K).toAffine.Point M H, f s = f s' ↔
      (s' = s ∨ s' = aX α hαα s ∨ s' = bX β hβ s ∨ s' = bX β hβ (bX β hβ s) ∨
        s' = aX α hαα (bX β hβ s) ∨ s' = aX α hαα (bX β hβ (bX β hβ s))) := by
    intro s s'
    rw [hff]
    constructor
    · rintro ⟨γ, hγ, hss'⟩
      obtain ⟨m, hm, hmγ⟩ := hstab γ hγ
      have hminj : Function.Injective m := injective_six α β hαα hβ hm
      have hmem := forall_mem_of_forall_exists_heq γ m hmγ s s' hss'
      have hEq : mapX m hminj s = s' := mapX_eq_of_forall_mem m hminj s s' hmem
      rw [← hEq]
      exact mapX_six α β hαα hβ hm hminj s
    · intro h
      obtain ⟨m, hm, hs'⟩ := exists_six_of_mem α β hαα hβ s s' h
      obtain ⟨γ, hγ, hmγ⟩ := hsix m hm
      refine ⟨γ, hγ, fun T hT => ⟨m T, ?_, hmγ T⟩⟩
      rw [hs']; exact Set.mem_image_of_mem _ hT

  have hSG : ∀ p, p ∈ S ↔ ∃ s, f s = p :=
    fun p => ⟨fun hp => hSf p hp, fun ⟨s, hs⟩ => hs ▸ hfS s⟩
  obtain ⟨hsize, hodd, h12⟩ := Function.orbitCensus_of_dihedralThree_relations
    (aX α hαα) (bX β hβ) (aX_aX α hαα) (bX_bX_bX β hβ) (aX_bX α β hαα hβ hαβ) f hc S hSG

  set fib : Place K (qExpFunctionFieldC K (CohCarrier.GammaH M H)) → ℕ :=
    fun p => (Finset.univ.filter fun s' => f s' = p).card with hfib
  have hordF : ∀ s : XH (E0 K).toAffine.Point M H, (f s).ord x = (fib (f s) : ℤ) := by
    intro s
    rw [hord s, natCard_subtype_eq_card_filter]
  have hcongr' : ∀ n : ℕ, (S.filter fun Q => Q.ord x = (n : ℤ)) = S.filter fun p => fib p = n := by
    intro n
    apply Finset.filter_congr
    intro Q hQ
    obtain ⟨s, rfl⟩ := hSf Q hQ
    rw [hordF]; norm_cast
  have hcongr1 := hcongr' 1
  have hcongr2 := hcongr' 2
  have hcongr3 := hcongr' 3
  have hcongr6 := hcongr' 6
  simp only [Nat.cast_one, Nat.cast_ofNat] at hcongr1 hcongr2 hcongr3 hcongr6

  obtain ⟨hL1, hL2, hL3⟩ := CohCarrier.exists_bottomRow_eq_and_torsionOrbit_bottomRow_eq_iff M H
  have hXV : Nat.card (XH (V M) M H) = (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)).index :=
    natCard_XV hL1 hL2 hL3
  have hDC3 := natCard_doubleCoset_eq hL1 hL2 hL3 (Subgroup.zpowers (ModularGroup.S * ModularGroup.T))
    (by rw [← ST_pow_three]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 3)
  have hDC2 := natCard_doubleCoset_eq hL1 hL2 hL3 (Subgroup.zpowers ModularGroup.S)
    (by rw [← S_pow_two]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2)
  have hB3 := card_mul_natCard_orbits (X := XH (V M) M H) 3 (ModularGroup.S * ModularGroup.T)
    (fun s => by rw [ST_pow_three, neg_one_smul'])
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB2 := card_mul_natCard_orbits (X := XH (V M) M H) 2 ModularGroup.S
    (fun s => by rw [S_pow_two, neg_one_smul'])

  obtain ⟨⟨P₁, hP₁, hcoβ⟩, ⟨P₂, hP₂, hcoα⟩⟩ :=
    AddCommGroup.exists_torsionBy_coords_of_dicyclic_relations M hM e α β hαα hβ hαβ
  have hP₁' : M • P₁ = 0 := by rw [← natCast_zsmul]; exact hP₁
  have hP₂' : M • P₂ = 0 := by rw [← natCast_zsmul]; exact hP₂
  have hcardX : Nat.card (XH (E0 K).toAffine.Point M H) = Nat.card (XH (V M) M H) :=
    natCard_XH_eq (H := H) β P₁ hP₁' hcoβ
  have hfixB : Nat.card {t : XH (E0 K).toAffine.Point M H // bX β hβ t = t} =
      Nat.card {s : XH (V M) M H // (ModularGroup.S * ModularGroup.T) • s = s} := by
    have h := natCard_fixed_eq (H := H) β P₁ hP₁' hcoβ (β_injective β hβ) nST (β_iota β hβ P₁ hP₁')
    simp only [nST_eq, neg_smul'] at h
    exact h
  have hfixA : Nat.card {t : XH (E0 K).toAffine.Point M H // aX α hαα t = t} =
      Nat.card {s : XH (V M) M H // ModularGroup.S • s = s} := by
    have h := natCard_fixed_eq (H := H) α P₂ hP₂' hcoα (α_injective α hαα) nS (α_iota α hαα P₂ hP₂')
    simp only [nS_eq, neg_smul'] at h
    exact h

  have htot : (Finset.univ : Finset (XH (E0 K).toAffine.Point M H)).card = ∑ p ∈ S, fib p :=
    Finset.card_eq_sum_card_fiberwise fun s _ => hfS s
  have hfour : ∀ p ∈ S, fib p = 1 ∨ fib p = 2 ∨ fib p = 3 ∨ fib p = 6 := by
    intro p hp
    obtain ⟨s, rfl⟩ := hSf p hp
    exact hsize s
  have hsum := sum_eq_of_mem_four S fib hfour
  have hNX : Nat.card (XH (E0 K).toAffine.Point M H) =
      (S.filter fun p => fib p = 1).card + 2 * (S.filter fun p => fib p = 2).card +
        3 * (S.filter fun p => fib p = 3).card + 6 * (S.filter fun p => fib p = 6).card := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ, htot, hsum]
  have hFB : Nat.card {t : XH (E0 K).toAffine.Point M H // bX β hβ t = t} =
      (S.filter fun p => fib p = 1).card + 2 * (S.filter fun p => fib p = 2).card := by
    rw [natCard_subtype_eq_card_filter, ← h12]
  have hFA : Nat.card {t : XH (E0 K).toAffine.Point M H // aX α hαα t = t} =
      (S.filter fun p => fib p = 1).card + (S.filter fun p => fib p = 3).card := by
    rw [natCard_subtype_eq_card_filter, ← hodd, Finset.filter_or, Finset.card_union_of_disjoint]
    exact Finset.disjoint_filter.mpr fun p _ h1 h3 => by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro Q hQ
    obtain ⟨s, rfl⟩ := hSf Q hQ
    rw [hordF]
    rcases hsize s with h | h | h | h <;> simp [hfib] at h ⊢ <;> simp [h]
  ·
    rw [← hXV, ← hcardX, Nat.card_eq_fintype_card, ← Finset.card_univ, htot, Nat.cast_sum]
    refine Finset.sum_congr rfl fun Q hQ => ?_
    obtain ⟨s, rfl⟩ := hSf Q hQ
    exact hordF s
  ·
    rw [hcongr1, hcongr2, hcongr3, hcongr6, hDC3]
    rw [← hcardX, ← hfixB, hNX, hFB] at hB3
    omega
  ·
    rw [hcongr1, hcongr2, hcongr3, hcongr6, hDC2]
    rw [← hcardX, ← hfixA, hNX, hFA] at hB2
    omega

end
end S_ModularCurve_ord_census_qExpFunctionFieldC_gammaH_of_char_three
end P2MW
export P2MW.S_ModularCurve_ord_census_qExpFunctionFieldC_gammaH_of_char_three (solution)
