-- Prove2me | solution 1 for ModularCurve.exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/11469b86-9156-519b-93b3-4ec1cddbd767

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_XHDiamondModL
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_ModularCurve_exists_natural_diamond_algHom_qExpFunctionFieldC_gammaH_of_transcendental_j
import Theorems.Thm_ModularCurve_coe_mem_modularFunctionFieldFullC_of_forall_diamondPullbackModL_apply_eq
import Theorems.Thm_WeierstrassCurve_exists_j_eq_zero_torsion_basis_heq_vcInvFun_of_order_three
import Theorems.Thm_WeierstrassCurve_exists_j_eq_1728_torsion_basis_heq_vcInvFun_of_order_four
import Theorems.Thm_CohCarrier_exists_bottomRow_eq_and_torsionOrbit_bottomRow_eq_iff
import Theorems.Thm_ModularCurve_exists_equiv_algHom_modularFunctionFieldFullC_of_transcendental_j
import Theorems.Thm_ModularCurve_exists_equivariant_torsion_reduction_ofJ
import Theorems.Thm_AlgebraicCurve_Place_ord_restrictAlong_eq_natCard_algHom_of_isGalois
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_pos
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂"
p2m_attr_erase "simp" "TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero"
p2m_attr_erase "simp" "ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open WeierstrassCurve WeierstrassCurve.Affine ModularCurve AlgebraicCurve CongruenceSubgroup
open scoped IntermediateField MatrixGroups ModularForm

noncomputable section

namespace P2MKcLOCELL

section Rows

variable (M : ℕ)

def red (a : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) (ZMod M) := (a : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod M))

def row (a : SL(2, ℤ)) : Fin 2 → ZMod M := fun i => (((a : Matrix (Fin 2) (Fin 2) ℤ) 1 i : ℤ) : ZMod M)

theorem red_mul (a b : SL(2, ℤ)) : red M (a * b) = red M a * red M b := by
  rw [red, red, red, Matrix.SpecialLinearGroup.coe_mul, Matrix.map_mul]

theorem red_one : red M 1 = 1 := by
  rw [red, Matrix.SpecialLinearGroup.coe_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem red_pow (a : SL(2, ℤ)) (n : ℕ) : red M (a ^ n) = red M a ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, red_one]
  | succ n ih => rw [pow_succ, pow_succ, red_mul, ih]

theorem row_apply (a : SL(2, ℤ)) (i : Fin 2) : row M a i = red M a 1 i := rfl

theorem row_mul (a b : SL(2, ℤ)) : row M (a * b) = Matrix.vecMul (row M a) (red M b) := by
  funext i
  rw [row_apply, red_mul, Matrix.mul_apply, Matrix.vecMul, dotProduct]
  rfl

theorem row_gamma0_mul (γ : Gamma0 M) (a : SL(2, ℤ)) :
    row M ((γ : SL(2, ℤ)) * a) = ((((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod M) • row M a := by
  have h10 : ((((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp γ.2
  funext i
  rw [row_mul, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul, row_apply,
    row_apply, row_apply]
  simp only [red, Matrix.map_apply, eq_intCast] at h10 ⊢
  rw [h10, zero_mul, zero_add]

def dU (γ : Gamma0 M) : (ZMod M)ˣ := CohCarrier.gamma0Units M γ

theorem coe_dU (γ : Gamma0 M) :
    ((dU M γ : (ZMod M)ˣ) : ZMod M) = ((((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod M) := rfl

theorem dU_conj (γ γ₁ : Gamma0 M) : dU M (γ₁⁻¹ * γ * γ₁) = dU M γ := by
  rw [dU, dU, map_mul, map_mul, mul_right_comm, map_inv, inv_mul_cancel, one_mul]

theorem inv_apply_zero_zero (γ : SL(2, ℤ)) :
    ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl γ]
  rfl

theorem coe_dU_inv (γ : Gamma0 M) :
    ((dU M γ⁻¹ : (ZMod M)ˣ) : ZMod M) = ((((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod M) := by
  rw [coe_dU]
  have : ((γ⁻¹ : Gamma0 M) : SL(2, ℤ)) = (γ : SL(2, ℤ))⁻¹ := rfl
  rw [this, Matrix.SpecialLinearGroup.SL2_inv_expl]
  rfl

end Rows

section AutPt

variable {L : Type*} [Field L] [DecidableEq L]

def castPt {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) : W₁.toAffine.Point ≃+ W₂.toAffine.Point := by
  subst e; exact AddEquiv.refl _

theorem castPt_eq_iff_heq {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) (P : W₁.toAffine.Point)
    (Q : W₂.toAffine.Point) : castPt e P = Q ↔ HEq P Q := by
  subst e; exact Iff.rfl.trans heq_iff_eq.symm

def autPt {W : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • W = W) :
    W.toAffine.Point →+ W.toAffine.Point :=
  (castPt hγ).toAddMonoidHom.comp
    (AddMonoidHom.mk' (Point.vcInvFun γ W.toAffine) (Point.vcInvFun_add γ W.toAffine))

theorem autPt_apply {W : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • W = W)
    (P : W.toAffine.Point) : autPt γ hγ P = castPt hγ (Point.vcInvFun γ W.toAffine P) := rfl

theorem autPt_eq_iff_heq {W : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • W = W)
    (P Q : W.toAffine.Point) : autPt γ hγ P = Q ↔ HEq (Point.vcInvFun γ W.toAffine P) Q := by
  rw [autPt_apply, castPt_eq_iff_heq]

end AutPt

section Tors

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

theorem val_sub_nsmul {P : A} (hP : M • P = 0) (u v : ZMod M) :
    (u - v).val • P = u.val • P - v.val • P := by
  rw [sub_eq_add_neg, val_add_nsmul hP, val_neg_nsmul hP, sub_eq_add_neg]

theorem val_one_nsmul {P : A} (hP : M • P = 0) : (1 : ZMod M).val • P = P := by
  have := val_natCast_nsmul hP 1
  rwa [Nat.cast_one, one_nsmul] at this

theorem zmod_smul_eq_val_nsmul {P : A} (hP : M • P = 0) (u : ZMod M) (n : ℕ) (hn : (n : ZMod M) = u) :
    n • P = u.val • P := by
  rw [← hn, val_natCast_nsmul hP]

theorem nsmul_of_addOrderOf_eq {P : A} (hP : addOrderOf P = M) : M • P = 0 := by
  rw [← hP]; exact addOrderOf_nsmul_eq_zero P

theorem nsmul_nsmul_eq_zero {P : A} (hP : M • P = 0) (n : ℕ) : M • (n • P) = 0 := by
  rw [nsmul_left_comm, hP, nsmul_zero]

theorem addOrderOf_units_nsmul {P : A} (hP : addOrderOf P = M) (u : (ZMod M)ˣ) :
    addOrderOf ((u : ZMod M).val • P) = M := by
  have hMP := nsmul_of_addOrderOf_eq hP
  refine Nat.dvd_antisymm (addOrderOf_dvd_of_nsmul_eq_zero (nsmul_nsmul_eq_zero hMP _)) ?_
  have h : P = ((u⁻¹ : (ZMod M)ˣ) : ZMod M).val • ((u : ZMod M).val • P) := by
    rw [← val_mul_nsmul hMP, ← Units.val_mul, inv_mul_cancel, Units.val_one, val_one_nsmul hMP]
  have hdvd : addOrderOf P ∣ addOrderOf ((u : ZMod M).val • P) := by
    apply addOrderOf_dvd_of_nsmul_eq_zero
    have : addOrderOf ((u : ZMod M).val • P) •
        (((u⁻¹ : (ZMod M)ˣ) : ZMod M).val • ((u : ZMod M).val • P)) = 0 := by
      rw [nsmul_left_comm, addOrderOf_nsmul_eq_zero, nsmul_zero]
    rwa [← h] at this
  rwa [hP] at hdvd

theorem addOrderOf_neg_eq {P : A} (hP : addOrderOf P = M) : addOrderOf (-P) = M := by
  rw [addOrderOf_neg]; exact hP

theorem addOrderOf_map_of_injOn (φ : A →+ B)
    (hφ : ∀ P Q : A, M • P = 0 → M • Q = 0 → φ P = φ Q → P = Q) {P : A}
    (hP : addOrderOf P = M) : addOrderOf (φ P) = M := by
  refine Nat.dvd_antisymm ?_ ?_
  · rw [← hP]; exact addOrderOf_map_dvd φ P
  · rw [← hP, addOrderOf_dvd_iff_nsmul_eq_zero]
    have h1 : addOrderOf (φ P) • φ P = 0 := addOrderOf_nsmul_eq_zero _
    exact hφ _ _ (nsmul_nsmul_eq_zero (nsmul_of_addOrderOf_eq hP) _) (nsmul_zero _)
      (by rw [map_nsmul, h1, map_zero])

theorem exists_units_of_mem_zmultiples {P Q : A} (hP : addOrderOf P = M) (hQ : addOrderOf Q = M)
    (h : Q ∈ AddSubgroup.zmultiples P) : ∃ u : (ZMod M)ˣ, Q = (u : ZMod M).val • P := by
  have hMP := nsmul_of_addOrderOf_eq hP
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp h

  have hM0 : (M : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hk : k • P = (k % (M : ℤ)).toNat • P := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k M]
    rw [add_zsmul, mul_comm, mul_zsmul, natCast_zsmul, hMP, zsmul_zero, add_zero]
    conv_lhs => rw [← Int.toNat_of_nonneg (Int.emod_nonneg k hM0), natCast_zsmul]
  set n : ℕ := (k % (M : ℤ)).toNat with hn
  rw [hk] at hQ ⊢

  have hcop : Nat.Coprime n M := by
    set g : ℕ := Nat.gcd n M with hg
    obtain ⟨c, hc⟩ : g ∣ M := Nat.gcd_dvd_right n M
    obtain ⟨n', hn'⟩ : g ∣ n := Nat.gcd_dvd_left n M
    have hMpos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
    have hcpos : 0 < c := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hc; omega

    have hcQ : c • (n • P) = 0 := by
      rw [← mul_nsmul', show c * n = n' * M by rw [hn', hc]; ring, mul_nsmul', hMP, nsmul_zero]
    have hMc : M ∣ c := by
      rw [← hQ]; exact addOrderOf_dvd_of_nsmul_eq_zero hcQ

    have hg1 : g * c ∣ 1 * c := by rw [one_mul, ← hc]; exact hMc
    have : g ∣ 1 := (Nat.mul_dvd_mul_iff_right hcpos).mp hg1
    exact Nat.dvd_one.mp this
  refine ⟨ZMod.unitOfCoprime n hcop, ?_⟩
  rw [ZMod.coe_unitOfCoprime, val_natCast_nsmul hMP]

theorem zmultiples_units_nsmul {P : A} (hP : M • P = 0) (u : (ZMod M)ˣ) :
    AddSubgroup.zmultiples ((u : ZMod M).val • P) = AddSubgroup.zmultiples P := by
  apply le_antisymm
  · rw [AddSubgroup.zmultiples_le]
    exact (AddSubgroup.zmultiples P).nsmul_mem (AddSubgroup.mem_zmultiples P) _
  · rw [AddSubgroup.zmultiples_le]
    have h : P = ((u⁻¹ : (ZMod M)ˣ) : ZMod M).val • ((u : ZMod M).val • P) := by
      rw [← val_mul_nsmul hP, ← Units.val_mul, inv_mul_cancel, Units.val_one, val_one_nsmul hP]
    have hmem : ((u⁻¹ : (ZMod M)ˣ) : ZMod M).val • ((u : ZMod M).val • P) ∈
        AddSubgroup.zmultiples ((u : ZMod M).val • P) :=
      (AddSubgroup.zmultiples _).nsmul_mem (AddSubgroup.mem_zmultiples _) _
    rwa [← h] at hmem

end Tors

section Core

def PM {A : Type*} [AddCommGroup A] (a b : A) : Prop := a = b ∨ a = -b

namespace PM

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

theorem rfl' (a : A) : PM a a := Or.inl rfl

theorem trans {a b c : A} (h₁ : PM a b) (h₂ : PM b c) : PM a c := by
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl (neg_neg c)

theorem symm {a b : A} (h : PM a b) : PM b a := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (neg_neg b).symm

theorem map (f : A →+ B) {a b : A} (h : PM a b) : PM (f a) (f b) := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (map_neg f b)

theorem neg_left {a b : A} (h : PM a b) : PM (-a) b := by
  rcases h with rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl (neg_neg b)

theorem nsmul (n : ℕ) {a b : A} (h : PM a b) : PM (n • a) (n • b) := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (smul_neg n b)

end PM

variable (M : ℕ) [NeZero M]

abbrev OrdM (Pt : Type*) [AddCommGroup Pt] : Type _ := {R : Pt // addOrderOf R = M}

structure Setup (Pt A₀ G X X₀ PlF Pl0 : Type*) [AddCommGroup Pt] [AddCommGroup A₀] [Group G] where
  g₀ : SL(2, ℤ)
  D : Subgroup G
  act : G → Pt →+ Pt
  θ : Pt →+ A₀
  σ₀ : AddMonoid.End A₀
  ιb : (Fin 2 → ZMod M) →+ A₀
  res : X → X₀
  actX : G → X → X
  actX₀ : G → X₀ → X₀
  πF : X → PlF
  π₀ : X₀ → Pl0
  ovr : PlF → Pl0
  pF : PlF → Prop
  p0 : Pl0 → Prop
  Ψ : OrdM M Pt → X
  dia : Gamma0 M → PlF → PlF
  g₀_fin : IsOfFinOrder g₀
  act_one : ∀ P, act 1 P = P
  act_mul : ∀ σ τ P, act (σ * τ) P = act σ (act τ P)
  θ_inj : ∀ P Q, M • P = 0 → M • Q = 0 → θ P = θ Q → P = Q
  ιb_inj : Function.Injective ιb
  ιb_surj : ∀ T, M • T = 0 → ∃ v, ιb v = T
  σ_ιb : ∀ v, σ₀ (ιb v) = -ιb (Matrix.vecMul v (red M g₀))
  shadow : ∃ τ ∈ D, ∀ P, PM (θ (act τ P)) (σ₀ (θ P))
  res_act : ∀ σ ψ, res (actX σ ψ) = actX₀ σ (res ψ)
  ovr_π : ∀ ψ, ovr (πF ψ) = π₀ (res ψ)
  p_ovr : ∀ Q, p0 (ovr Q) → pF Q
  F3 : ∀ Q, pF Q → ∃ ψ, πF ψ = Q
  F4 : ∀ ψ ψ', πF ψ = πF ψ' ↔ ∃ σ ∈ D, ψ' = actX σ ψ
  O3 : ∀ P, p0 P → ∃ ψ₀, π₀ ψ₀ = P
  O4 : ∀ ψ₀ ψ₀', π₀ ψ₀ = π₀ ψ₀' ↔ ∃ σ ∈ D, ψ₀' = actX₀ σ ψ₀
  Ψnat : ∀ (σ : G) (R R' : OrdM M Pt), R'.1 = act σ R.1 → Ψ R' = actX σ (Ψ R)
  Ψres : ∀ (u : (ZMod M)ˣ) (R R' : OrdM M Pt), R'.1 = (u : ZMod M).val • R.1 → res (Ψ R') = res (Ψ R)
  Ψneg : ∀ R R' : OrdM M Pt, R'.1 = -R.1 → Ψ R' = Ψ R
  Ψsep0 : ∀ R R' : OrdM M Pt, res (Ψ R) = res (Ψ R') → ∃ u : (ZMod M)ˣ, R'.1 = (u : ZMod M).val • R.1
  Ψexh : ∀ ψ, ∃ R, Ψ R = ψ
  tors_fin : Finite {P : Pt // M • P = 0}
  X₀_fin : Finite X₀
  cardX₀ : Nat.card X₀ = Nat.card {C : AddSubgroup Pt // IsAddCyclic C ∧ Nat.card C = M}
  dia_Ψ : ∀ (γ : Gamma0 M) (R R' : OrdM M Pt),
    R'.1 = ((dU M γ : (ZMod M)ˣ) : ZMod M).val • R.1 → dia γ (πF (Ψ R)) = πF (Ψ R')

namespace Setup

variable {M}
variable {Pt A₀ G X X₀ PlF Pl0 : Type*} [AddCommGroup Pt] [AddCommGroup A₀] [Group G]
variable (S : Setup M Pt A₀ G X X₀ PlF Pl0)

theorem act_injective (σ : G) : Function.Injective (S.act σ) := by
  intro P Q h
  have := congrArg (S.act σ⁻¹) h
  rwa [← S.act_mul, ← S.act_mul, inv_mul_cancel, S.act_one, S.act_one] at this

theorem act_inv_act (σ : G) (P : Pt) : S.act σ⁻¹ (S.act σ P) = P := by
  rw [← S.act_mul, inv_mul_cancel, S.act_one]

theorem act_act_inv (σ : G) (P : Pt) : S.act σ (S.act σ⁻¹ P) = P := by
  rw [← S.act_mul, mul_inv_cancel, S.act_one]

def mkU (u : (ZMod M)ˣ) (R : OrdM M Pt) : OrdM M Pt := ⟨(u : ZMod M).val • R.1, addOrderOf_units_nsmul R.2 u⟩

def mkA (σ : G) (R : OrdM M Pt) : OrdM M Pt :=
  ⟨S.act σ R.1, by rw [addOrderOf_injective (S.act σ) (S.act_injective σ)]; exact R.2⟩

def mkN (R : OrdM M Pt) : OrdM M Pt := ⟨-R.1, addOrderOf_neg_eq R.2⟩

@[scoped simp] theorem mkU_val (u : (ZMod M)ˣ) (R : OrdM M Pt) : (mkU u R).1 = (u : ZMod M).val • R.1 := rfl
@[scoped simp] theorem mkA_val (σ : G) (R : OrdM M Pt) : (S.mkA σ R).1 = S.act σ R.1 := rfl
@[scoped simp] theorem mkN_val (R : OrdM M Pt) : (mkN (M := M) R).1 = -R.1 := rfl

theorem tors (R : OrdM M Pt) : M • R.1 = 0 := nsmul_of_addOrderOf_eq R.2

theorem Ψ_mkA (σ : G) (R : OrdM M Pt) : S.Ψ (S.mkA σ R) = S.actX σ (S.Ψ R) := S.Ψnat σ R _ rfl

theorem res_Ψ_mkU (u : (ZMod M)ˣ) (R : OrdM M Pt) : S.res (S.Ψ (mkU u R)) = S.res (S.Ψ R) := S.Ψres u R _ rfl

theorem Ψ_mkN (R : OrdM M Pt) : S.Ψ (mkN R) = S.Ψ R := S.Ψneg R _ rfl

theorem Ψ_eq_of_PM {R R' : OrdM M Pt} {T : Pt} (hT : PM R'.1 T) (u : (ZMod M)ˣ) (hu : T = (u : ZMod M).val • R.1) :
    S.res (S.Ψ R') = S.res (S.Ψ R) := by
  rcases hT with h | h
  · rw [hu] at h
    exact S.Ψres u R R' h
  · rw [hu] at h
    have h1 : S.Ψ R' = S.Ψ (mkU u R) := S.Ψneg (mkU u R) R' h
    rw [h1]
    exact S.res_Ψ_mkU u R

theorem addOrderOf_θ (R : OrdM M Pt) : addOrderOf (S.θ R.1) = M :=
  addOrderOf_map_of_injOn S.θ S.θ_inj R.2

theorem tors_θ (R : OrdM M Pt) : M • S.θ R.1 = 0 := by
  rw [← map_nsmul, tors R, map_zero]

def vco (R : OrdM M Pt) : Fin 2 → ZMod M := Classical.choose (S.ιb_surj _ (S.tors_θ R))

theorem ιb_vco (R : OrdM M Pt) : S.ιb (S.vco R) = S.θ R.1 := Classical.choose_spec (S.ιb_surj _ (S.tors_θ R))

theorem addOrderOf_vco (R : OrdM M Pt) : addOrderOf (S.vco R) = M := by
  rw [← addOrderOf_injective S.ιb S.ιb_inj, S.ιb_vco, S.addOrderOf_θ]

def pairEquiv : (Fin 2 → ZMod M) ≃+ ZMod M × ZMod M :=
  AddEquiv.mk' (piFinTwoEquiv fun _ => ZMod M) (fun _ _ => rfl)

theorem exists_row_eq (v : Fin 2 → ZMod M) (hv : addOrderOf v = M) : ∃ a : SL(2, ℤ), row M a = v := by
  have hv' : addOrderOf (pairEquiv (M := M) v) = M := by rw [AddEquiv.addOrderOf_eq]; exact hv
  obtain ⟨a, ha0, ha1⟩ :=
    (CohCarrier.exists_bottomRow_eq_and_torsionOrbit_bottomRow_eq_iff M ⊤).1 (pairEquiv (M := M) v) hv'
  refine ⟨a, funext fun i => ?_⟩
  fin_cases i
  · exact ha0
  · exact ha1

def gmat (R : OrdM M Pt) : SL(2, ℤ) := Classical.choose (exists_row_eq (S.vco R) (S.addOrderOf_vco R))

theorem row_gmat (R : OrdM M Pt) : row M (S.gmat R) = S.vco R :=
  Classical.choose_spec (exists_row_eq (S.vco R) (S.addOrderOf_vco R))

abbrev C : Subgroup SL(2, ℤ) := Subgroup.zpowers S.g₀

def dc (R : OrdM M Pt) : DoubleCoset.Quotient (Gamma0 M : Set SL(2, ℤ)) (S.C : Set SL(2, ℤ)) :=
  DoubleCoset.mk (Gamma0 M) S.C (S.gmat R)

theorem mem_C_iff (c : SL(2, ℤ)) : c ∈ S.C ↔ ∃ m : ℕ, S.g₀ ^ m = c := by
  rw [← S.g₀_fin.mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff]

theorem shadow_pow (m : ℕ) : ∃ τ ∈ S.D, ∀ P, PM (S.θ (S.act τ P)) ((S.σ₀ ^ m) (S.θ P)) := by
  induction m with
  | zero => exact ⟨1, S.D.one_mem, fun P => Or.inl (by rw [S.act_one, pow_zero]; rfl)⟩
  | succ m ih =>
    obtain ⟨τ, hτ, h⟩ := ih
    obtain ⟨τ₀, hτ₀, h₀⟩ := S.shadow
    refine ⟨τ₀ * τ, S.D.mul_mem hτ₀ hτ, fun P => ?_⟩
    rw [S.act_mul, pow_succ']
    exact (h₀ _).trans ((h P).map (S.σ₀ : A₀ →+ A₀))

theorem ιb_vecMul_pow (v : Fin 2 → ZMod M) (m : ℕ) :
    PM (S.ιb (Matrix.vecMul v (red M (S.g₀ ^ m)))) ((S.σ₀ ^ m) (S.ιb v)) := by
  induction m with
  | zero =>
    left
    rw [pow_zero, red_one, Matrix.vecMul_one, pow_zero]
    rfl
  | succ m ih =>
    rw [pow_succ, red_mul, ← Matrix.vecMul_vecMul, pow_succ']
    have h1 : S.ιb (Matrix.vecMul (Matrix.vecMul v (red M (S.g₀ ^ m))) (red M S.g₀)) =
        -S.σ₀ (S.ιb (Matrix.vecMul v (red M (S.g₀ ^ m)))) := by
      rw [S.σ_ιb, neg_neg]
    rw [h1]
    exact (ih.map (S.σ₀ : A₀ →+ A₀)).neg_left

theorem ιb_smul (d : ZMod M) (v : Fin 2 → ZMod M) : S.ιb (d • v) = d.val • S.ιb v := by
  have : d • v = d.val • v := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, ZMod.natCast_zmod_val]
  rw [this, map_nsmul]

theorem exists_act_PM (R : OrdM M Pt) (a : SL(2, ℤ)) (ha : row M a = S.vco R) (γ : Gamma0 M) (m : ℕ)
    (h : (γ : SL(2, ℤ)) * a = a * S.g₀ ^ m) :
    ∃ τ ∈ S.D, PM (S.act τ R.1) (((dU M γ : (ZMod M)ˣ) : ZMod M).val • R.1) := by

  have hrow : ((dU M γ : (ZMod M)ˣ) : ZMod M) • S.vco R = Matrix.vecMul (S.vco R) (red M (S.g₀ ^ m)) := by
    rw [coe_dU, ← ha, ← row_gamma0_mul, h, row_mul]

  have hθ : ((dU M γ : (ZMod M)ˣ) : ZMod M).val • S.θ R.1 = S.ιb (Matrix.vecMul (S.vco R) (red M (S.g₀ ^ m))) := by
    rw [← S.ιb_vco, ← S.ιb_smul, hrow]
  obtain ⟨τ, hτ, hshadow⟩ := S.shadow_pow m
  refine ⟨τ, hτ, ?_⟩

  have h1 : PM (S.θ (S.act τ R.1)) (S.θ (((dU M γ : (ZMod M)ˣ) : ZMod M).val • R.1)) := by
    rw [map_nsmul, hθ]
    have h2 := S.ιb_vecMul_pow (S.vco R) m
    rw [S.ιb_vco] at h2
    exact (hshadow R.1).trans h2.symm
  have ht1 : M • S.act τ R.1 = 0 := by rw [← map_nsmul, tors R, map_zero]
  have ht2 : M • (((dU M γ : (ZMod M)ˣ) : ZMod M).val • R.1) = 0 := nsmul_nsmul_eq_zero (tors R) _
  rcases h1 with h1 | h1
  · exact Or.inl (S.θ_inj _ _ ht1 ht2 h1)
  · refine Or.inr (S.θ_inj _ _ ht1 (by rw [neg_nsmul, ht2, neg_zero]) ?_)
    rw [h1, map_neg]

abbrev Cyc (Pt : Type*) [AddCommGroup Pt] (M : ℕ) : Type _ := {C : AddSubgroup Pt // IsAddCyclic C ∧ Nat.card C = M}

def cyc (R : OrdM M Pt) : Cyc Pt M :=
  ⟨AddSubgroup.zmultiples R.1, inferInstance, by rw [Nat.card_zmultiples, R.2]⟩

theorem cyc_surjective : Function.Surjective (cyc (M := M) (Pt := Pt)) := by
  rintro ⟨C, hC, hcard⟩
  haveI := hC
  obtain ⟨g, hg⟩ := IsAddCyclic.exists_generator (α := C)
  have hord : addOrderOf (g : Pt) = M := by
    change addOrderOf (C.subtype g) = M
    rw [addOrderOf_injective C.subtype Subtype.val_injective g, ← Nat.card_zmultiples]
    have htop : AddSubgroup.zmultiples g = ⊤ := by
      rw [eq_top_iff]; intro x _; exact hg x
    rw [htop, Nat.card_congr (AddSubgroup.topEquiv (G := C)).toEquiv, hcard]
  refine ⟨⟨g, hord⟩, Subtype.ext ?_⟩
  show AddSubgroup.zmultiples (g : Pt) = C
  apply le_antisymm
  · rw [AddSubgroup.zmultiples_le]; exact g.2
  · intro x hx
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (hg ⟨x, hx⟩)
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem finite_cyc (hfin : Finite {P : Pt // M • P = 0}) : Finite (Cyc Pt M) := by
  haveI := hfin
  let f : Cyc Pt M → Set {P : Pt // M • P = 0} := fun C => {P | P.1 ∈ C.1}
  refine Finite.of_injective f fun C C' h => Subtype.ext ?_
  have key : ∀ (C : Cyc Pt M) (x : Pt), x ∈ C.1 → M • x = 0 := by
    intro C x hx
    have h1 : Nat.card C.1 • (⟨x, hx⟩ : C.1) = 0 := card_nsmul_eq_zero'
    rw [C.2.2] at h1
    exact congrArg Subtype.val h1
  ext x
  constructor
  · intro hx
    have := congrArg (fun s => (⟨x, key C x hx⟩ : {P : Pt // M • P = 0}) ∈ s) h
    simpa [f, hx] using this
  · intro hx
    have := congrArg (fun s => (⟨x, key C' x hx⟩ : {P : Pt // M • P = 0}) ∈ s) h
    simpa [f, hx] using this

theorem cyc_eq_iff (R R' : OrdM M Pt) : cyc R = cyc R' ↔ ∃ u : (ZMod M)ˣ, R'.1 = (u : ZMod M).val • R.1 := by
  constructor
  · intro h
    have h1 : AddSubgroup.zmultiples R.1 = AddSubgroup.zmultiples R'.1 := congrArg Subtype.val h
    have hmem : R'.1 ∈ AddSubgroup.zmultiples R.1 := by rw [h1]; exact AddSubgroup.mem_zmultiples _
    exact exists_units_of_mem_zmultiples R.2 R'.2 hmem
  · rintro ⟨u, hu⟩
    apply Subtype.ext
    show AddSubgroup.zmultiples R.1 = AddSubgroup.zmultiples R'.1
    rw [hu, zmultiples_units_nsmul (tors R)]

def gen (C : Cyc Pt M) : OrdM M Pt := Classical.choose (cyc_surjective C)

theorem cyc_gen (C : Cyc Pt M) : cyc (gen C) = C := Classical.choose_spec (cyc_surjective C)

theorem exh0 (ψ₀ : X₀) : ∃ R : OrdM M Pt, S.res (S.Ψ R) = ψ₀ := by
  haveI : Finite (Cyc Pt M) := finite_cyc S.tors_fin
  haveI : Finite X₀ := S.X₀_fin
  let f : Cyc Pt M → X₀ := fun C => S.res (S.Ψ (gen C))
  have hf : Function.Injective f := by
    intro C C' h
    obtain ⟨u, hu⟩ := S.Ψsep0 _ _ h
    rw [← cyc_gen C, ← cyc_gen C']
    exact (cyc_eq_iff _ _).mpr ⟨u, hu⟩
  have hbij := hf.bijective_of_nat_card_le (le_of_eq S.cardX₀)
  obtain ⟨C, hC⟩ := hbij.2 ψ₀
  exact ⟨gen C, hC⟩

theorem exists_RP (P : {P : Pl0 // S.p0 P}) : ∃ R : OrdM M Pt, S.π₀ (S.res (S.Ψ R)) = P.1 := by
  obtain ⟨ψ₀, hψ₀⟩ := S.O3 P.1 P.2
  obtain ⟨R, hR⟩ := S.exh0 ψ₀
  exact ⟨R, by rw [hR, hψ₀]⟩

def RP (P : {P : Pl0 // S.p0 P}) : OrdM M Pt := Classical.choose (S.exists_RP P)

theorem π₀_RP (P : {P : Pl0 // S.p0 P}) : S.π₀ (S.res (S.Ψ (S.RP P))) = P.1 :=
  Classical.choose_spec (S.exists_RP P)

def ι (P : {P : Pl0 // S.p0 P}) : DoubleCoset.Quotient (Gamma0 M : Set SL(2, ℤ)) (S.C : Set SL(2, ℤ)) :=
  S.dc (S.RP P)

theorem π₀_res_Ψ_mkA {τ : G} (hτ : τ ∈ S.D) (R : OrdM M Pt) :
    S.π₀ (S.res (S.Ψ (S.mkA τ R))) = S.π₀ (S.res (S.Ψ R)) := by
  rw [S.Ψ_mkA, S.res_act]
  exact ((S.O4 _ _).mpr ⟨τ, hτ, rfl⟩).symm

theorem πF_Ψ_mkA {τ : G} (hτ : τ ∈ S.D) (R : OrdM M Pt) : S.πF (S.Ψ (S.mkA τ R)) = S.πF (S.Ψ R) := by
  rw [S.Ψ_mkA]
  exact ((S.F4 _ _).mpr ⟨τ, hτ, rfl⟩).symm

theorem ι_injective : Function.Injective S.ι := by
  intro P₁ P₂ h

  obtain ⟨γ, hγ, c, hc, hgc⟩ := (DoubleCoset.eq _ _ _ _).mp h
  obtain ⟨m, rfl⟩ := (S.mem_C_iff c).mp hc
  set R₁ := S.RP P₁
  set R₂ := S.RP P₂
  set γ' : Gamma0 M := ⟨γ, hγ⟩
  set d : ZMod M := ((dU M γ' : (ZMod M)ˣ) : ZMod M) with hd

  have hrow : S.vco R₂ = d • Matrix.vecMul (S.vco R₁) (red M (S.g₀ ^ m)) := by
    have h1 := S.row_gmat R₂
    rw [hgc, row_mul, show γ = (γ' : SL(2, ℤ)) from rfl, row_gamma0_mul, S.row_gmat,
      Matrix.smul_vecMul] at h1
    rw [← h1, hd, coe_dU]

  obtain ⟨τ, hτ, hshadow⟩ := S.shadow_pow m
  have hPM : PM (S.θ R₂.1) (S.θ (d.val • S.act τ R₁.1)) := by
    rw [← S.ιb_vco R₂, hrow, S.ιb_smul, map_nsmul]
    refine PM.nsmul d.val ?_
    have h2 := S.ιb_vecMul_pow (S.vco R₁) m
    rw [S.ιb_vco] at h2
    exact h2.trans (hshadow R₁.1).symm

  have ht2 : M • R₂.1 = 0 := tors R₂
  have ht1 : M • (d.val • S.act τ R₁.1) = 0 := nsmul_nsmul_eq_zero (tors (S.mkA τ R₁)) _
  have hR : PM R₂.1 (d.val • S.act τ R₁.1) := by
    rcases hPM with h1 | h1
    · exact Or.inl (S.θ_inj _ _ ht2 ht1 h1)
    · exact Or.inr (S.θ_inj _ _ ht2 (by rw [neg_nsmul, ht1, neg_zero]) (by rw [h1, map_neg]))
  have hres : S.res (S.Ψ R₂) = S.res (S.Ψ (S.mkA τ R₁)) :=
    S.Ψ_eq_of_PM (R := S.mkA τ R₁) hR (dU M γ') rfl
  apply Subtype.ext
  rw [← S.π₀_RP P₁, ← S.π₀_RP P₂]
  change S.π₀ (S.res (S.Ψ R₁)) = S.π₀ (S.res (S.Ψ R₂))
  rw [hres, S.π₀_res_Ψ_mkA hτ]

theorem Ψ_eq_of_PM_mkU {R R' : OrdM M Pt} (u : (ZMod M)ˣ) (h : PM R'.1 ((u : ZMod M).val • R.1)) :
    S.Ψ R' = S.Ψ (mkU u R) := by
  rcases h with h | h
  · have : R' = mkU u R := Subtype.ext h
    rw [this]
  · exact S.Ψneg (mkU u R) R' h

theorem stab (P : {P : Pl0 // S.p0 P}) (g : SL(2, ℤ)) (hg : S.ι P = DoubleCoset.mk (Gamma0 M) S.C g)
    (γ : Gamma0 M) (hγ : g⁻¹ * (γ : SL(2, ℤ)) * g ∈ S.C) (Q : PlF) (hQ : S.ovr Q = P.1) :
    S.dia γ Q = Q := by
  set R₁ := S.RP P
  set a := S.gmat R₁

  obtain ⟨γ₁, hγ₁, c₁, hc₁, hgc⟩ := (DoubleCoset.eq _ _ _ _).mp hg
  set γ₁' : Gamma0 M := ⟨γ₁, hγ₁⟩
  set γ' : Gamma0 M := γ₁'⁻¹ * γ * γ₁'

  have hmem : a⁻¹ * (γ' : SL(2, ℤ)) * a ∈ S.C := by
    have h1 : a⁻¹ * (γ' : SL(2, ℤ)) * a = c₁ * (g⁻¹ * (γ : SL(2, ℤ)) * g) * c₁⁻¹ := by
      have hγ'coe : (γ' : SL(2, ℤ)) = γ₁⁻¹ * (γ : SL(2, ℤ)) * γ₁ := rfl
      rw [hgc, hγ'coe]
      simp only [mul_inv_rev, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
      rfl
    rw [h1]
    exact S.C.mul_mem (S.C.mul_mem hc₁ hγ) (S.C.inv_mem hc₁)
  obtain ⟨m, hm⟩ := (S.mem_C_iff _).mp hmem
  have hcomm : (γ' : SL(2, ℤ)) * a = a * S.g₀ ^ m := by
    rw [hm, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]

  obtain ⟨τ₀, hτ₀, h₀⟩ := S.exists_act_PM R₁ a (S.row_gmat R₁) γ' m hcomm
  have hd : dU M γ' = dU M γ := dU_conj M γ γ₁'
  rw [hd] at h₀
  set d : ZMod M := ((dU M γ : (ZMod M)ˣ) : ZMod M) with hdd

  have hpQ : S.pF Q := S.p_ovr Q (by rw [hQ]; exact P.2)
  obtain ⟨ψ, hψ⟩ := S.F3 Q hpQ
  obtain ⟨R, hR⟩ := S.Ψexh ψ
  rw [← hR] at hψ

  have hπ : S.π₀ (S.res (S.Ψ R₁)) = S.π₀ (S.res (S.Ψ R)) := by
    rw [S.π₀_RP P, ← S.ovr_π, hψ, hQ]
  obtain ⟨τ, hτ, hτeq⟩ := (S.O4 _ _).mp hπ
  rw [← S.res_act, ← S.Ψ_mkA] at hτeq
  obtain ⟨u, hu⟩ := S.Ψsep0 (S.mkA τ R₁) R hτeq.symm
  rw [mkA_val] at hu

  set τ' : G := τ * τ₀ * τ⁻¹
  have hτ' : τ' ∈ S.D := S.D.mul_mem (S.D.mul_mem hτ hτ₀) (S.D.inv_mem hτ)
  have hR' : PM (S.act τ' R.1) (d.val • R.1) := by
    have h1 : S.act τ' R.1 = S.act τ ((u : ZMod M).val • S.act τ₀ R₁.1) := by
      simp only [τ']
      rw [S.act_mul, S.act_mul, hu, map_nsmul, S.act_inv_act, map_nsmul]
    rw [h1, hu, smul_comm d.val (u : ZMod M).val, ← map_nsmul (S.act τ) d.val, ← map_nsmul (S.act τ)]
    exact ((h₀.nsmul (u : ZMod M).val).map (S.act τ))

  have hfix : S.πF (S.Ψ (S.mkA τ' R)) = Q := by rw [S.πF_Ψ_mkA hτ', hψ]
  have hΨ : S.Ψ (S.mkA τ' R) = S.Ψ (mkU (dU M γ) R) := S.Ψ_eq_of_PM_mkU (dU M γ) hR'
  rw [← hψ, S.dia_Ψ γ R (mkU (dU M γ) R) rfl, ← hΨ, hfix, hψ]

theorem core : ∃ ι : {P : Pl0 // S.p0 P} → DoubleCoset.Quotient (Gamma0 M : Set SL(2, ℤ)) (S.C : Set SL(2, ℤ)),
    Function.Injective ι ∧
    ∀ (P : {P : Pl0 // S.p0 P}) (g : SL(2, ℤ)), ι P = DoubleCoset.mk (Gamma0 M) S.C g →
      ∀ γ : Gamma0 M, g⁻¹ * (γ : SL(2, ℤ)) * g ∈ S.C → ∀ Q : PlF, S.ovr Q = P.1 → S.dia γ Q = Q :=
  ⟨S.ι, S.ι_injective, S.stab⟩

end Setup
p2m_reactivate "P2MW.S_ModularCurve_exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_pos.P2MKcLOCELL.Setup"

end Core
p2m_reactivate "P2MW.S_ModularCurve_exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_pos.P2MKcLOCELL.Setup"

section Concrete

variable {K : Type*} [Field K] {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

abbrev Fb (K : Type*) [Field K] (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Type _ :=
  ↥(qExpFunctionFieldC K (CohCarrier.GammaH M H))

abbrev F0 (K : Type*) [Field K] (M : ℕ) : Type _ := ↥(modularFunctionFieldFullC K M)

def jF0 (K : Type*) [Field K] (M : ℕ) : F0 K M := ⟨jqModC K, jqModC_mem_full K M⟩

variable (ρ : Gamma0 M →* (Fb K M H ≃ₐ[K] Fb K M H))

def fixedIF (e : Fb K M H ≃ₐ[K] Fb K M H) : IntermediateField K (Fb K M H) where
  carrier := {y | e y = y}
  mul_mem' {a b} ha hb := by simp only [Set.mem_setOf_eq, map_mul] at *; rw [ha, hb]
  one_mem' := map_one e
  add_mem' {a b} ha hb := by simp only [Set.mem_setOf_eq, map_add] at *; rw [ha, hb]
  zero_mem' := map_zero e
  algebraMap_mem' c := e.commutes c
  inv_mem' x hx := by simp only [Set.mem_setOf_eq, map_inv₀] at *; rw [hx]

theorem rho_eq_one_of_mem (hρ : IsDiamondPullbackModL K M H ρ) (γ : Gamma0 M)
    (hγ : (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H) : ρ γ = 1 := by

  have hgen : intFormRatiosC K (CohCarrier.GammaH M H) ⊆
      (IntermediateField.lift (fixedIF (ρ γ)) : Set (LaurentSeries K)) := by
    rintro z ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
    have hmem : intSeriesC K pf / intSeriesC K pg ∈ qExpFunctionFieldC K (CohCarrier.GammaH M H) :=
      div_mem_qExpFunctionFieldC f g hf hg hg0
    have ef : (⇑f : UpperHalfPlane → ℂ) = (⇑f : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ)) := by
      rw [ModularForm.SL_slash]
      exact (SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ)).symm
    have eg : (⇑g : UpperHalfPlane → ℂ) = (⇑g : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ)) := by
      rw [ModularForm.SL_slash]
      exact (SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ hγ)).symm
    have hfix : ρ γ ⟨_, hmem⟩ = ⟨_, hmem⟩ :=
      Subtype.ext (hρ γ k f g f g pf pg pf pg hf hg hf hg ef eg hg0 ⟨_, hmem⟩ rfl)
    exact (IntermediateField.mem_lift (⟨_, hmem⟩ : Fb K M H)).mpr hfix
  have hle : qExpFunctionFieldC K (CohCarrier.GammaH M H) ≤ IntermediateField.lift (fixedIF (ρ γ)) :=
    IntermediateField.adjoin_le_iff.mpr hgen
  exact AlgEquiv.ext fun y => (IntermediateField.mem_lift y).mp (hle y.2)

theorem rho_eq_of_dU_eq (hρ : IsDiamondPullbackModL K M H ρ) (γ γ' : Gamma0 M) (h : dU M γ = dU M γ') :
    ρ γ = ρ γ' := by
  have hmem : ((γ * γ'⁻¹ : Gamma0 M) : SL(2, ℤ)) ∈ CohCarrier.GammaH M H := by
    rw [CohCarrier.mem_GammaH_iff]
    refine ⟨(γ * γ'⁻¹).2, ?_⟩
    have : CohCarrier.gamma0Units M (γ * γ'⁻¹) = 1 := by
      rw [map_mul, map_inv, show CohCarrier.gamma0Units M γ = dU M γ from rfl, h, dU, mul_inv_cancel]
    rw [show (⟨((γ * γ'⁻¹ : Gamma0 M) : SL(2, ℤ)), (γ * γ'⁻¹).2⟩ : Gamma0 M) = γ * γ'⁻¹ from rfl, this]
    exact one_mem H
  have := rho_eq_one_of_mem ρ hρ _ hmem
  rwa [map_mul, map_inv, mul_inv_eq_one] at this

private theorem _root_.P2MKcLOCELL.finite_range (hρ : IsDiamondPullbackModL K M H ρ) : Finite ρ.range := by
  classical
  let f : (ZMod M)ˣ → (Fb K M H ≃ₐ[K] Fb K M H) := fun u =>
    if h : ∃ γ : Gamma0 M, dU M γ = u then ρ h.choose else 1
  have hf : ∀ γ, ρ γ = f (dU M γ) := by
    intro γ
    have h : ∃ γ' : Gamma0 M, dU M γ' = dU M γ := ⟨γ, rfl⟩
    simp only [f, dif_pos h]
    exact rho_eq_of_dU_eq ρ hρ _ _ h.choose_spec.symm
  have hsub : (ρ.range : Set (Fb K M H ≃ₐ[K] Fb K M H)) ⊆ Set.range f := by
    rintro _ ⟨γ, rfl⟩; exact ⟨dU M γ, (hf γ).symm⟩
  exact ((Set.finite_range f).subset hsub).to_subtype

p2m_export "P2MKcLOCELL" "finite_range"

variable (hle : modularFunctionFieldFullC K M ≤ qExpFunctionFieldC K (CohCarrier.GammaH M H))

abbrev incl : F0 K M →ₐ[K] Fb K M H := IntermediateField.inclusion hle

theorem coe_incl (y : F0 K M) : ((incl hle y : Fb K M H) : LaurentSeries K) = y :=
  IntermediateField.coe_inclusion hle y

theorem rho_incl (hfix : ∀ (γ : Gamma0 M) (x : Fb K M H), (x : LaurentSeries K) ∈ modularFunctionFieldFullC K M → ρ γ x = x)
    (γ : Gamma0 M) (y : F0 K M) : ρ γ (incl hle y) = incl hle y :=
  hfix γ _ (by rw [coe_incl]; exact y.2)

abbrev Fix : Subfield (Fb K M H) := FixedPoints.subfield ρ.range (Fb K M H)

theorem mem_Fix_iff (u : Fb K M H) : u ∈ Fix ρ ↔ ∀ γ : Gamma0 M, ρ γ u = u := by
  change (∀ g : ρ.range, g • u = u) ↔ _
  exact ⟨fun h γ => h ⟨ρ γ, γ, rfl⟩, fun h ⟨g, γ, hγ⟩ => hγ ▸ h γ⟩

section WithFix

variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] [IsAlgClosed K]
  (hfix : ∀ (γ : Gamma0 M) (x : Fb K M H), (x : LaurentSeries K) ∈ modularFunctionFieldFullC K M → ρ γ x = x)
  (hℓM : ¬ ℓ ∣ M) (hρ : IsDiamondPullbackModL K M H ρ)

include hℓM hρ hfix in

theorem exists_incl_eq_of_mem_Fix (u : Fb K M H) (hu : u ∈ Fix ρ) : ∃ y : F0 K M, incl hle y = u := by
  have hmem : (u : LaurentSeries K) ∈ modularFunctionFieldFullC K M :=
    ModularCurve.coe_mem_modularFunctionFieldFullC_of_forall_diamondPullbackModL_apply_eq M H hℓM K ρ hρ
      hfix u ((mem_Fix_iff ρ u).mp hu)
  exact ⟨⟨u, hmem⟩, Subtype.ext (coe_incl hle _)⟩

include hℓM hρ hfix in

theorem incl_isIntegral : (incl hle : F0 K M →ₐ[K] Fb K M H).toRingHom.IsIntegral := by
  haveI := finite_range ρ hρ
  intro u
  obtain ⟨p, hp, hpu⟩ := FixedPoints.isIntegral ρ.range (Fb K M H) u

  classical
  let ψ : Fix ρ → F0 K M := fun c => (exists_incl_eq_of_mem_Fix ρ hle hfix hℓM hρ c.1 c.2).choose
  have hψ : ∀ c : Fix ρ, incl hle (ψ c) = c.1 := fun c =>
    (exists_incl_eq_of_mem_Fix ρ hle hfix hℓM hρ c.1 c.2).choose_spec
  have hinj : Function.Injective (incl hle : F0 K M →ₐ[K] Fb K M H) := (incl hle).injective
  let ψh : Fix ρ →+* F0 K M :=
    { toFun := ψ
      map_one' := hinj (show incl hle (ψ 1) = incl hle 1 by rw [hψ, map_one]; rfl)
      map_mul' := fun a b => hinj (show incl hle (ψ (a * b)) = incl hle (ψ a * ψ b) by
        rw [hψ, map_mul, hψ, hψ]; rfl)
      map_zero' := hinj (show incl hle (ψ 0) = incl hle 0 by rw [hψ, map_zero]; rfl)
      map_add' := fun a b => hinj (show incl hle (ψ (a + b)) = incl hle (ψ a + ψ b) by
        rw [hψ, map_add, hψ, hψ]; rfl) }
  refine ⟨p.map ψh, hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have : (incl hle : F0 K M →ₐ[K] Fb K M H).toRingHom.comp ψh = algebraMap (Fix ρ) (Fb K M H) := by
    ext c : 1
    exact hψ c
  rw [this]
  exact hpu

include hℓM hρ hfix in

theorem exists_rho_of_comp_incl_eq {Ω : Type*} [Field Ω] [Algebra K Ω] (ψ ψ' : Fb K M H →ₐ[K] Ω)
    (h : ψ.comp (incl hle) = ψ'.comp (incl hle)) : ∃ γ : Gamma0 M, ψ' = ψ.comp (ρ γ : Fb K M H →ₐ[K] Fb K M H) := by
  haveI := finite_range ρ hρ

  have hagree : ∀ c : Fix ρ, ψ' c.1 = ψ c.1 := by
    intro c
    obtain ⟨y, hy⟩ := exists_incl_eq_of_mem_Fix ρ hle hfix hℓM hρ c.1 c.2
    rw [← hy]
    exact (AlgHom.congr_fun h y).symm
  letI iA1 : Algebra (Fix ρ) Ω := (ψ.toRingHom.comp (Fix ρ).subtype).toAlgebra
  letI iA2 : Algebra (Fb K M H) Ω := ψ.toRingHom.toAlgebra
  haveI iT : @IsScalarTower (Fix ρ) (Fb K M H) Ω _ iA2.toSMul iA1.toSMul :=
    @IsScalarTower.of_algebraMap_eq (Fix ρ) (Fb K M H) Ω _ _ _ _ iA2 iA1 fun c => rfl
  haveI : IsGalois (Fix ρ) (Fb K M H) := IsGalois.of_fixed_field (Fb K M H) ρ.range
  let ψ'F : Fb K M H →ₐ[Fix ρ] Ω := { ψ'.toRingHom with commutes' := fun c => hagree c }
  let g : Fb K M H →ₐ[Fix ρ] Fb K M H := @AlgHom.restrictNormal _ _ _ _ _ _ _ iA1 ψ'F (Fb K M H) _ _ _ iA2 _ iT _
  have hg : ∀ y, ψ (g y) = ψ' y := fun y =>
    @AlgHom.restrictNormal_commutes _ _ _ _ _ _ _ iA1 ψ'F (Fb K M H) _ _ _ iA2 _ iT _ y
  let ge : Fb K M H ≃ₐ[Fix ρ] Fb K M H := AlgEquiv.ofBijective g (Algebra.IsAlgebraic.algHom_bijective g)
  obtain ⟨gr, hgr⟩ := FixedPoints.toAlgAut_surjective ρ.range (Fb K M H) ge
  obtain ⟨γ, hγ⟩ := gr.2
  refine ⟨γ, AlgHom.ext fun y => ?_⟩
  rw [AlgHom.comp_apply, ← hg y]
  change ψ (ge y) = ψ ((ρ γ : Fb K M H →ₐ[K] Fb K M H) y)
  rw [← hgr, MulSemiringAction.toAlgAut_apply, AlgEquiv.coe_algHom, hγ]
  rfl

end WithFix
p2m_reactivate "P2MW.S_ModularCurve_exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_pos.P2MKcLOCELL.Setup"

theorem smul_restrictAlong {Ω : Type*} [Field Ω] [Algebra K Ω] (τ : Fb K M H ≃ₐ[K] Fb K M H) (W : Place K Ω)
    (ψ : Fb K M H →ₐ[K] Ω) (h : ψ.toRingHom.IsIntegral)
    (h' : (ψ.comp (τ.symm : Fb K M H →ₐ[K] Fb K M H)).toRingHom.IsIntegral) :
    τ • W.restrictAlong ψ h = W.restrictAlong (ψ.comp (τ.symm : Fb K M H →ₐ[K] Fb K M H)) h' := by
  apply Place.ext
  ext y
  rw [Place.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  letI := algebraAlong ψ
  letI := algebraAlong (ψ.comp (τ.symm : Fb K M H →ₐ[K] Fb K M H))
  rfl

theorem restrictAlong_restrictAlong {Ω : Type*} [Field Ω] [Algebra K Ω] (W : Place K Ω)
    (ψ : Fb K M H →ₐ[K] Ω) (h : ψ.toRingHom.IsIntegral) (hi : (incl hle : F0 K M →ₐ[K] Fb K M H).toRingHom.IsIntegral)
    (h' : (ψ.comp (incl hle)).toRingHom.IsIntegral) :
    (W.restrictAlong ψ h).restrictAlong (incl hle) hi = W.restrictAlong (ψ.comp (incl hle)) h' := by
  apply Place.ext
  letI := algebraAlong ψ
  letI := algebraAlong (incl hle : F0 K M →ₐ[K] Fb K M H)
  letI := algebraAlong (ψ.comp (incl hle))
  rfl

theorem comap_eq_iff (Q : Place K (Fb K M H)) (P : Place K (F0 K M))
    (hi : (incl hle : F0 K M →ₐ[K] Fb K M H).toRingHom.IsIntegral) :
    Q.toValuationSubring.comap (IntermediateField.inclusion hle).toRingHom = P.toValuationSubring ↔
      Q.restrictAlong (incl hle) hi = P := by
  rw [Place.ext_iff]
  letI := algebraAlong (incl hle : F0 K M →ₐ[K] Fb K M H)
  exact Iff.rfl

theorem isIntegral_of_apply_eq {F Ω : Type*} [Field F] [Field Ω] [Algebra K F]
    [Algebra K Ω] (x : F) (t : Ω) [FiniteDimensional K⟮t⟯ Ω] (ψ : F →ₐ[K] Ω) (hψ : ψ x = t) :
    ψ.toRingHom.IsIntegral := by
  intro y
  obtain ⟨q, hqm, hq0⟩ : IsIntegral K⟮t⟯ y := Algebra.IsIntegral.isIntegral y
  have hle : K⟮t⟯ ≤ ψ.fieldRange := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ rfl
    exact ⟨x, hψ⟩
  have hlifts : q.map (algebraMap K⟮t⟯ Ω) ∈ Polynomial.lifts ψ.toRingHom := by
    refine (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ?_
    rw [Polynomial.coeff_map]
    obtain ⟨f, hf⟩ := hle (q.coeff n).2
    exact ⟨f, hf⟩
  obtain ⟨q', hq'map, -, hq'monic⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts (hqm.map _)
  refine ⟨q', hq'monic, ?_⟩
  rw [← Polynomial.eval_map, hq'map, Polynomial.eval_map]
  exact hq0

theorem exists_gamma0_apply_eq (u : (ZMod M)ˣ) :
    ∃ γ : Gamma0 M, ((((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod M) = u := by

  have hord : addOrderOf (![0, ((u⁻¹ : (ZMod M)ˣ) : ZMod M)] : Fin 2 → ZMod M) = M := by
    rw [← AddEquiv.addOrderOf_eq (Setup.pairEquiv (M := M)), show Setup.pairEquiv (M := M) ![0, _] =
      ((0 : ZMod M), ((u⁻¹ : (ZMod M)ˣ) : ZMod M)) from rfl, Prod.addOrderOf_mk, addOrderOf_zero, Nat.lcm_one_left]
    have : ((u⁻¹ : (ZMod M)ˣ) : ZMod M) = ((((u⁻¹ : (ZMod M)ˣ) : ZMod M).val : ℕ) : ZMod M) :=
      (ZMod.natCast_zmod_val _).symm
    rw [this, ZMod.addOrderOf_coe _ (NeZero.ne M)]
    have hcop : Nat.Coprime (((u⁻¹ : (ZMod M)ˣ) : ZMod M).val) M := ZMod.val_coe_unit_coprime u⁻¹
    rw [Nat.Coprime] at hcop
    rw [Nat.gcd_comm, hcop, Nat.div_one]
  obtain ⟨a, ha⟩ := Setup.exists_row_eq _ hord
  have ha0 : (((a : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod M) = 0 := congrFun ha 0
  have ha1 : (((a : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod M) = ((u⁻¹ : (ZMod M)ˣ) : ZMod M) := congrFun ha 1
  refine ⟨⟨a, Gamma0_mem.mpr ha0⟩, ?_⟩
  have hdet := Matrix.SpecialLinearGroup.det_coe a
  rw [Matrix.det_fin_two] at hdet
  have hdet' := congrArg (fun z : ℤ => (z : ZMod M)) hdet
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, ha0, ha1, mul_zero, sub_zero] at hdet'
  change (((a : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod M) = u
  calc (((a : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod M)
      = (((a : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod M) * ((u⁻¹ : (ZMod M)ˣ) : ZMod M) * u := by
        rw [mul_assoc, Units.inv_mul, mul_one]
    _ = u := by rw [hdet', one_mul]

end Concrete
p2m_reactivate "P2MW.S_ModularCurve_exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_pos.P2MKcLOCELL.Setup"

section MainAt

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [DecidableEq K] {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}
  {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]

def ιbOf {A : Type*} [AddCommGroup A] (P Q : A) (hP : M • P = 0) (hQ : M • Q = 0) : (Fin 2 → ZMod M) →+ A where
  toFun v := (v 0).val • P + (v 1).val • Q
  map_zero' := by simp
  map_add' v w := by
    simp only [Pi.add_apply, val_add_nsmul hP, val_add_nsmul hQ]
    abel

theorem ιbOf_apply {A : Type*} [AddCommGroup A] (P Q : A) (hP : M • P = 0) (hQ : M • Q = 0) (v : Fin 2 → ZMod M) :
    ιbOf P Q hP hQ v = (v 0).val • P + (v 1).val • Q := rfl

set_option maxHeartbeats 12800000 in

theorem main_at (hℓM : ¬ ℓ ∣ M)
    (ρ : Gamma0 M →* (Fb K M H ≃ₐ[K] Fb K M H)) (hρ : IsDiamondPullbackModL K M H ρ)
    (hle : modularFunctionFieldFullC K M ≤ qExpFunctionFieldC K (CohCarrier.GammaH M H))
    (hfix : ∀ (γ : Gamma0 M) (x : Fb K M H), (x : LaurentSeries K) ∈ modularFunctionFieldFullC K M → ρ γ x = x)
    (j₀ : K) (g₀ : SL(2, ℤ)) (hg₀ : IsOfFinOrder g₀)
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic] (hE₀ : E₀.j = j₀) (σv : VariableChange K) (hσv : σv • E₀ = E₀)
    (Pb Qb : E₀.toAffine.Point) (hPb : M • Pb = 0) (hQb : M • Qb = 0)
    (hbasis : ∀ T : E₀.toAffine.Point, M • T = 0 → ∃! c : ZMod M × ZMod M, T = c.1.val • Pb + c.2.val • Qb)
    (hσιb : ∀ v : Fin 2 → ZMod M,
      autPt σv hσv (ιbOf Pb Qb hPb hQb v) = -ιbOf Pb Qb hPb hQb (Matrix.vecMul v (red M g₀))) :
    ∃ ι : {P : Place K (F0 K M) // 0 < P.ord (jF0 K M - algebraMap K (F0 K M) j₀)} →
        DoubleCoset.Quotient (Gamma0 M : Set SL(2, ℤ)) (Subgroup.zpowers g₀ : Set SL(2, ℤ)),
      Function.Injective ι ∧
      ∀ (P : {P : Place K (F0 K M) // 0 < P.ord (jF0 K M - algebraMap K (F0 K M) j₀)}) (g : SL(2, ℤ)),
        ι P = DoubleCoset.mk (Gamma0 M) (Subgroup.zpowers g₀) g →
        ∀ γ : Gamma0 M, g⁻¹ * (γ : SL(2, ℤ)) * g ∈ Subgroup.zpowers g₀ →
        ∀ Q : Place K (Fb K M H),
          Q.toValuationSubring.comap (IntermediateField.inclusion hle).toRingHom = P.1.toValuationSubring →
          ρ γ • Q = Q := by
  have hMK : (M : K) ≠ 0 := fun h => hℓM ((CharP.cast_eq_zero_iff K ℓ M).mp h)

  obtain ⟨𝕄, _iF, _iD, _iA, t, ht, hfin, hgal, W₀, hW₀, θ, ρD, hfull, hθinj, -, -, -, hsurjC, -⟩ :=
    ModularCurve.exists_equivariant_torsion_reduction_ofJ K ℓ M hMK j₀ E₀ hE₀
  haveI := hfin
  haveI := hgal

  let tk : K⟮t⟯ := ⟨t, IntermediateField.mem_adjoin_simple_self K t⟩
  let E : WeierstrassCurve K⟮t⟯ := WeierstrassCurve.ofJ tk
  have hEj : E.j = tk := WeierstrassCurve.ofJ_j tk
  have hjt : algebraMap K⟮t⟯ 𝕄 E.j = t := by rw [hEj]; rfl
  have hEtr : Transcendental K E.j := by
    rw [hEj]
    intro halg
    exact ht (by simpa using halg.algebraMap (A := 𝕄))

  let xH : Fb K M H := incl hle (jF0 K M)
  have hxH : (xH : LaurentSeries K) = jqModC K := coe_incl hle _

  obtain ⟨Ψ, hnat, hdia, hlev, hsep, hexh⟩ :=
    ModularCurve.exists_natural_diamond_algHom_qExpFunctionFieldC_gammaH_of_transcendental_j
      K M hMK H xH hxH K⟮t⟯ 𝕄 E hEtr hfull
  obtain ⟨Φ₀, -⟩ :=
    ModularCurve.exists_equiv_algHom_modularFunctionFieldFullC_of_transcendental_j K M hMK K⟮t⟯ 𝕄 E hEtr hfull
  have hΨt : ∀ R, ((Ψ R).1 : Fb K M H →ₐ[K] 𝕄) xH = t := fun R => by rw [(Ψ R).2, hjt]

  let Pt : Type u := (E.baseChange 𝕄).toAffine.Point
  let G : Type u := 𝕄 ≃ₐ[K⟮t⟯] 𝕄
  let X : Type u := {ψ : Fb K M H →ₐ[K] 𝕄 // ψ xH = t}
  let X₀ : Type u := {ψ₀ : F0 K M →ₐ[K] 𝕄 // ψ₀ (jF0 K M) = t}

  let toSA : G →* SemilinearAut K 𝕄 :=
    { toFun := fun σ => SemilinearAut.ofAlgAut (σ.restrictScalars K)
      map_one' := by rw [show (1 : G).restrictScalars K = 1 from AlgEquiv.ext fun _ => rfl, map_one]
      map_mul' := fun σ τ => by
        rw [show (σ * τ : G).restrictScalars K = σ.restrictScalars K * τ.restrictScalars K from
          AlgEquiv.ext fun _ => rfl, map_mul] }
  letI : MulAction G (Place K 𝕄) := MulAction.compHom (Place K 𝕄) toSA
  let D : Subgroup G := MulAction.stabilizer G W₀
  have hD : ∀ σ : G, σ ∈ D ↔ SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ := fun σ => Iff.rfl

  have hint : ∀ ψ : Fb K M H →ₐ[K] 𝕄, ψ xH = t → ψ.toRingHom.IsIntegral :=
    fun ψ hψ => isIntegral_of_apply_eq xH t ψ hψ
  have hint₀ : ∀ ψ₀ : F0 K M →ₐ[K] 𝕄, ψ₀ (jF0 K M) = t → ψ₀.toRingHom.IsIntegral :=
    fun ψ₀ hψ₀ => isIntegral_of_apply_eq (jF0 K M) t ψ₀ hψ₀
  have hincl : (incl hle : F0 K M →ₐ[K] Fb K M H).toRingHom.IsIntegral := incl_isIntegral ρ hle hfix hℓM hρ

  let ιb : (Fin 2 → ZMod M) →+ E₀.toAffine.Point := ιbOf Pb Qb hPb hQb
  have hιb_inj : Function.Injective ιb := by
    intro v w h
    have hT : M • ιb v = 0 := by rw [← map_nsmul, show M • v = 0 by ext i; simp, map_zero]
    obtain ⟨c, -, huniq⟩ := hbasis _ hT
    have h1 : (v 0, v 1) = c := huniq (v 0, v 1) rfl
    have h2 : (w 0, w 1) = c := huniq (w 0, w 1) (by rw [h]; rfl)
    have h12 := h1.trans h2.symm
    funext i
    fin_cases i
    · exact congrArg Prod.fst h12
    · exact congrArg Prod.snd h12
  have hιb_surj : ∀ T : E₀.toAffine.Point, M • T = 0 → ∃ v, ιb v = T := by
    intro T hT
    obtain ⟨c, hc, -⟩ := hbasis T hT
    exact ⟨![c.1, c.2], hc.symm⟩
  have hθ_inj : ∀ P Q : Pt, M • P = 0 → M • Q = 0 → θ P = θ Q → P = Q := by
    intro P Q hP hQ h
    have := hθinj M (P - Q) hℓM (by rw [nsmul_sub, hP, hQ, sub_zero]) (by rw [map_sub, h, sub_self])
    exact sub_eq_zero.mp this
  obtain ⟨R₁⟩ : Nonempty (OrdM M Pt) := by

    let v₀ : Fin 2 → ZMod M := ![1, 0]
    have hv₀ : addOrderOf v₀ = M := by
      rw [← AddEquiv.addOrderOf_eq (Setup.pairEquiv (M := M)),
        show Setup.pairEquiv (M := M) v₀ = ((1 : ZMod M), (0 : ZMod M)) from rfl, Prod.addOrderOf_mk,
        addOrderOf_zero, ZMod.addOrderOf_one, Nat.lcm_one_right]
    have hT₀ : addOrderOf (ιb v₀) = M := by rw [addOrderOf_injective ιb hιb_inj, hv₀]

    have hcardV : Nat.card (Fin 2 → ZMod M) = M ^ 2 := by
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
    let ιr : (Fin 2 → ZMod M) → {T : E₀.toAffine.Point // M • T = 0} :=
      fun v => ⟨ιb v, by rw [← map_nsmul, show M • v = 0 by ext i; simp, map_zero]⟩
    have hιr : Function.Bijective ιr :=
      ⟨fun v w h => hιb_inj (congrArg Subtype.val h), fun T => by
        obtain ⟨v, hv⟩ := hιb_surj T.1 T.2; exact ⟨v, Subtype.ext hv⟩⟩
    have hcard₀ : Nat.card {T : E₀.toAffine.Point // M • T = 0} = M ^ 2 := by
      rw [← Nat.card_eq_of_bijective ιr hιr, hcardV]
    let θr : {P : Pt // M • P = 0} → {T : E₀.toAffine.Point // M • T = 0} :=
      fun P => ⟨θ P.1, by rw [← map_nsmul, P.2, map_zero]⟩
    have hθr : Function.Injective θr := fun P Q h => Subtype.ext (hθ_inj _ _ P.2 Q.2 (congrArg Subtype.val h))
    haveI : Finite {T : E₀.toAffine.Point // M • T = 0} :=
      Nat.finite_of_card_ne_zero (by rw [hcard₀]; exact pow_ne_zero 2 (NeZero.ne M))
    obtain ⟨⟨R, hR⟩, hθR⟩ := (hθr.bijective_of_nat_card_le (by rw [hcard₀, hfull])).2 ⟨ιb v₀, nsmul_of_addOrderOf_eq hT₀⟩
    have hθR' : θ R = ιb v₀ := congrArg Subtype.val hθR
    refine ⟨⟨R, Nat.dvd_antisymm (addOrderOf_dvd_of_nsmul_eq_zero hR) ?_⟩⟩
    rw [← hT₀, ← hθR']
    exact addOrderOf_map_dvd θ R

  obtain ⟨-, hFi, hFii, hFiii, -⟩ :=
    AlgebraicCurve.Place.ord_restrictAlong_eq_natCard_algHom_of_isGalois K xH t j₀ (Ψ R₁).1 (hΨt R₁) hfin hgal
      hint W₀ hW₀
  obtain ⟨-, hOi, hOii, hOiii, -⟩ :=
    AlgebraicCurve.Place.ord_restrictAlong_eq_natCard_algHom_of_isGalois K (jF0 K M) t j₀
      (((Ψ R₁).1 : Fb K M H →ₐ[K] 𝕄).comp (incl hle)) (hΨt R₁) hfin hgal hint₀ W₀ hW₀

  have rA_congr : ∀ (φ φ' : Fb K M H →ₐ[K] 𝕄) (h : φ.toRingHom.IsIntegral) (h' : φ'.toRingHom.IsIntegral),
      φ = φ' → W₀.restrictAlong φ h = W₀.restrictAlong φ' h' := by
    rintro φ φ' h h' rfl; rfl

  have hρsymm : ∀ γ : Gamma0 M, ((ρ γ).symm : Fb K M H →ₐ[K] Fb K M H) = (ρ γ⁻¹ : Fb K M H →ₐ[K] Fb K M H) := by
    intro γ; rw [map_inv, AlgEquiv.aut_inv]

  let S : Setup M Pt E₀.toAffine.Point G X X₀ (Place K (Fb K M H)) (Place K (F0 K M)) :=
    { g₀ := g₀
      D := D
      act := fun σ => Point.map (σ : 𝕄 →ₐ[K⟮t⟯] 𝕄)
      θ := θ
      σ₀ := autPt σv hσv
      ιb := ιb
      res := fun ψ => ⟨ψ.1.comp (incl hle), ψ.2⟩
      actX := fun σ ψ => ⟨((σ : 𝕄 →ₐ[K⟮t⟯] 𝕄).restrictScalars K).comp ψ.1, by
        show σ (ψ.1 xH) = t
        rw [ψ.2]; exact σ.commutes tk⟩
      actX₀ := fun σ ψ₀ => ⟨((σ : 𝕄 →ₐ[K⟮t⟯] 𝕄).restrictScalars K).comp ψ₀.1, by
        show σ (ψ₀.1 (jF0 K M)) = t
        rw [ψ₀.2]; exact σ.commutes tk⟩
      πF := fun ψ => W₀.restrictAlong ψ.1 (hint ψ.1 ψ.2)
      π₀ := fun ψ₀ => W₀.restrictAlong ψ₀.1 (hint₀ ψ₀.1 ψ₀.2)
      ovr := fun Q => Q.restrictAlong (incl hle) hincl
      pF := fun Q => 0 < Q.ord (xH - algebraMap K (Fb K M H) j₀)
      p0 := fun P => 0 < P.ord (jF0 K M - algebraMap K (F0 K M) j₀)
      Ψ := fun R => ⟨(Ψ R).1, hΨt R⟩
      dia := fun γ Q => ρ γ • Q
      g₀_fin := hg₀
      act_one := fun P => by rcases P with _ | ⟨x, y, h⟩ <;> rfl
      act_mul := fun σ τ P => by
        show Point.map ((σ * τ : G) : 𝕄 →ₐ[K⟮t⟯] 𝕄) P =
          Point.map (σ : 𝕄 →ₐ[K⟮t⟯] 𝕄) (Point.map (τ : 𝕄 →ₐ[K⟮t⟯] 𝕄) P)
        rw [Point.map_map]; rfl
      θ_inj := hθ_inj
      ιb_inj := hιb_inj
      ιb_surj := hιb_surj
      σ_ιb := hσιb
      shadow := by
        obtain ⟨τ, hτ, hh⟩ := hsurjC σv hσv
        refine ⟨τ, (hD τ).mpr hτ, fun P => ?_⟩
        rcases hh with hh | hh
        · exact Or.inl ((autPt_eq_iff_heq σv hσv (θ P) _).mpr (hh P)).symm
        · right
          have h1 := (autPt_eq_iff_heq σv hσv (θ P) _).mpr (hh P)
          rw [← neg_eq_iff_eq_neg, ← h1]
          rfl
      res_act := fun σ ψ => rfl
      ovr_π := fun ψ => restrictAlong_restrictAlong hle W₀ ψ.1 (hint ψ.1 ψ.2) hincl (hint₀ _ ψ.2)
      p_ovr := fun Q hQ => by
        change 0 < Q.ord (xH - algebraMap K (Fb K M H) j₀)
        have h1 : xH - algebraMap K (Fb K M H) j₀ = incl hle (jF0 K M - algebraMap K (F0 K M) j₀) := by
          rw [map_sub, AlgHom.commutes]
        rw [h1, Place.ord_restrictAlong (incl hle) hincl]
        refine mul_pos ?_ hQ
        letI := algebraAlong (incl hle : F0 K M →ₐ[K] Fb K M H)
        haveI := isScalarTower_along (incl hle : F0 K M →ₐ[K] Fb K M H)
        haveI := isIntegral_along (incl hle : F0 K M →ₐ[K] Fb K M H) hincl
        exact_mod_cast Q.ramificationIndex_pos (F := F0 K M)
      F3 := fun Q hQ => by
        obtain ⟨ψ, hψ, h⟩ := hFii Q hQ
        exact ⟨⟨ψ, hψ⟩, h⟩
      F4 := fun ψ ψ' => by
        change W₀.restrictAlong ψ.1 (hint ψ.1 ψ.2) = W₀.restrictAlong ψ'.1 (hint ψ'.1 ψ'.2) ↔ _
        rw [hFiii ψ.1 ψ'.1 ψ.2 ψ'.2]
        refine exists_congr fun σ => ?_
        rw [Subtype.ext_iff]
        exact Iff.rfl
      O3 := fun P hP => by
        obtain ⟨ψ₀, hψ₀, h⟩ := hOii P hP
        exact ⟨⟨ψ₀, hψ₀⟩, h⟩
      O4 := fun ψ₀ ψ₀' => by
        change W₀.restrictAlong ψ₀.1 (hint₀ ψ₀.1 ψ₀.2) = W₀.restrictAlong ψ₀'.1 (hint₀ ψ₀'.1 ψ₀'.2) ↔ _
        rw [hOiii ψ₀.1 ψ₀'.1 ψ₀.2 ψ₀'.2]
        refine exists_congr fun σ => ?_
        rw [Subtype.ext_iff]
        exact Iff.rfl
      Ψnat := fun σ R R' h => Subtype.ext (hnat σ R R' h)
      Ψres := fun u R R' h => by
        obtain ⟨γ, hγ⟩ := exists_gamma0_apply_eq (M := M) u
        have h1 := hdia ρ hρ γ R R' (by rw [h, hγ])
        apply Subtype.ext
        change ((Ψ R').1 : Fb K M H →ₐ[K] 𝕄).comp (incl hle) = ((Ψ R).1 : Fb K M H →ₐ[K] 𝕄).comp (incl hle)
        rw [h1]
        exact AlgHom.ext fun y => congrArg ((Ψ R).1 : Fb K M H →ₐ[K] 𝕄) (rho_incl ρ hle hfix γ y)
      Ψneg := fun R R' h => by
        apply Subtype.ext
        change ((Ψ R').1 : Fb K M H →ₐ[K] 𝕄) = (Ψ R).1
        rw [hlev (-1) R R' (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))]
        rw [h, Units.val_neg, Units.val_one, val_neg_nsmul (nsmul_of_addOrderOf_eq R.2),
          val_one_nsmul (nsmul_of_addOrderOf_eq R.2)]
      Ψsep0 := fun R R' h => by
        have h1 : ((Ψ R).1 : Fb K M H →ₐ[K] 𝕄).comp (incl hle) = ((Ψ R').1 : Fb K M H →ₐ[K] 𝕄).comp (incl hle) :=
          congrArg Subtype.val h
        obtain ⟨γ, hγ⟩ := exists_rho_of_comp_incl_eq ρ hle hfix hℓM hρ _ _ h1
        let a : (ZMod M)ˣ := dU M γ⁻¹
        have h2 := hdia ρ hρ γ R (Setup.mkU a R) (by rw [Setup.mkU_val, coe_dU_inv])
        have h3 : Ψ R' = Ψ (Setup.mkU a R) := Subtype.ext (hγ.trans h2.symm)
        obtain ⟨w, -, hw⟩ := hsep (Setup.mkU a R) R' h3
        refine ⟨w * a, ?_⟩
        rw [hw, Setup.mkU_val, Units.val_mul, val_mul_nsmul (nsmul_of_addOrderOf_eq R.2)]
      Ψexh := fun ψ => by
        obtain ⟨R, hR⟩ := hexh ψ.1 (by rw [ψ.2, hjt])
        exact ⟨R, Subtype.ext hR⟩
      tors_fin := Nat.finite_of_card_ne_zero (by rw [hfull]; exact pow_ne_zero 2 (NeZero.ne M))
      X₀_fin := by
        haveI : Finite (Setup.Cyc Pt M) :=
          Setup.finite_cyc (Nat.finite_of_card_ne_zero (by rw [hfull]; exact pow_ne_zero 2 (NeZero.ne M)))
        exact Finite.of_equiv _ (Φ₀.trans (Equiv.subtypeEquivRight fun ψ₀ => by rw [hjt]; exact Iff.rfl))
      cardX₀ := by
        rw [Nat.card_congr (Φ₀.trans (Equiv.subtypeEquivRight fun ψ₀ => by rw [hjt]; exact Iff.rfl)).symm]
      dia_Ψ := fun γ R R' h => by
        change ρ γ • W₀.restrictAlong (Ψ R).1 (hint _ (hΨt R)) = W₀.restrictAlong (Ψ R').1 (hint _ (hΨt R'))
        have h' : R'.1 = ((((((γ⁻¹ : Gamma0 M) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod M).val) • R.1 := by
          rw [h, ← coe_dU_inv, inv_inv]
        have h2 := hdia ρ hρ γ⁻¹ R R' h'
        have hint' : (((Ψ R).1 : Fb K M H →ₐ[K] 𝕄).comp ((ρ γ).symm : Fb K M H →ₐ[K] Fb K M H)).toRingHom.IsIntegral := by
          rw [hρsymm, ← h2]; exact hint _ (hΨt R')
        rw [smul_restrictAlong (ρ γ) W₀ _ _ hint']
        exact rA_congr _ _ _ _ (by rw [hρsymm, ← h2]) }

  obtain ⟨ι, hι, hstab⟩ := S.core
  refine ⟨ι, hι, fun P g hg γ hγ Q hQ => hstab P g hg γ hγ Q ?_⟩
  exact (comap_eq_iff hle Q P.1 hincl).mp hQ

end MainAt
p2m_reactivate "P2MW.S_ModularCurve_exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_pos.P2MKcLOCELL.Setup"

section Values

variable (M : ℕ) [NeZero M]

theorem red_ST : red M (ModularGroup.S * ModularGroup.T) = !![0, -1; 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [red, ModularGroup.S, ModularGroup.T, Matrix.mul_apply, Fin.sum_univ_two]

theorem red_S : red M ModularGroup.S = !![0, -1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [red, ModularGroup.S]

theorem vecMul_red_ST (v : Fin 2 → ZMod M) :
    Matrix.vecMul v (red M (ModularGroup.S * ModularGroup.T)) = ![v 1, -v 0 + v 1] := by
  rw [red_ST]
  ext i
  fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem vecMul_red_S (v : Fin 2 → ZMod M) :
    Matrix.vecMul v (red M ModularGroup.S) = ![v 1, -v 0] := by
  rw [red_S]
  ext i
  fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem isOfFinOrder_ST : IsOfFinOrder (ModularGroup.S * ModularGroup.T) := by
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨6, by norm_num, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ModularGroup.S, ModularGroup.T, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

theorem isOfFinOrder_S : IsOfFinOrder ModularGroup.S := by
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨4, by norm_num, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ModularGroup.S, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

variable {M}
variable {L : Type*} [Field L] [DecidableEq L] {E₀ : WeierstrassCurve L} (σv : VariableChange L) (hσv : σv • E₀ = E₀)
  {Pb Qb : E₀.toAffine.Point} (hPb : M • Pb = 0) (hQb : M • Qb = 0)

theorem autPt_ιbOf_ST (h1 : HEq (Point.vcInvFun σv E₀.toAffine Pb) Qb)
    (h2 : HEq (Point.vcInvFun σv E₀.toAffine Qb) (-Pb - Qb)) (v : Fin 2 → ZMod M) :
    autPt σv hσv (ιbOf Pb Qb hPb hQb v) = -ιbOf Pb Qb hPb hQb (Matrix.vecMul v (red M (ModularGroup.S * ModularGroup.T))) := by
  have e1 : autPt σv hσv Pb = Qb := (autPt_eq_iff_heq σv hσv Pb Qb).mpr h1
  have e2 : autPt σv hσv Qb = -Pb - Qb := (autPt_eq_iff_heq σv hσv Qb _).mpr h2
  rw [vecMul_red_ST, ιbOf_apply, ιbOf_apply, map_add, map_nsmul, map_nsmul, e1, e2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [val_add_nsmul hQb, val_neg_nsmul hQb, nsmul_sub, smul_neg]
  abel

theorem autPt_ιbOf_S (h1 : HEq (Point.vcInvFun σv E₀.toAffine Pb) Qb)
    (h2 : HEq (Point.vcInvFun σv E₀.toAffine Qb) (-Pb)) (v : Fin 2 → ZMod M) :
    autPt σv hσv (ιbOf Pb Qb hPb hQb v) = -ιbOf Pb Qb hPb hQb (Matrix.vecMul v (red M ModularGroup.S)) := by
  have e1 : autPt σv hσv Pb = Qb := (autPt_eq_iff_heq σv hσv Pb Qb).mpr h1
  have e2 : autPt σv hσv Qb = -Pb := (autPt_eq_iff_heq σv hσv Qb _).mpr h2
  rw [vecMul_red_S, ιbOf_apply, ιbOf_apply, map_add, map_nsmul, map_nsmul, e1, e2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [val_neg_nsmul hQb, smul_neg]
  abel

end Values
p2m_reactivate "P2MW.S_ModularCurve_exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_pos.P2MKcLOCELL.Setup"

end P2MKcLOCELL
p2m_reactivate "P2MW.S_ModularCurve_exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_pos.P2MKcLOCELL.Setup P2MW.S_ModularCurve_exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_pos.P2MKcLOCELL"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_pos.P2MKcLOCELL.Setup P2MW.S_ModularCurve_exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_pos.P2MKcLOCELL"

open P2MKcLOCELL in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K ℓ]
    (ρ : CongruenceSubgroup.Gamma0 M →*
      (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H) ≃ₐ[K]
        ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)))
    (hρ : ModularCurve.IsDiamondPullbackModL K M H ρ)
    (hle : ModularCurve.modularFunctionFieldFullC K M ≤
      ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H))
    (hfix : ∀ (γ : CongruenceSubgroup.Gamma0 M)
      (x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)),
      (x : LaurentSeries K) ∈ ModularCurve.modularFunctionFieldFullC K M → ρ γ x = x) :
    (∃ ι : {P : AlgebraicCurve.Place K (ModularCurve.modularFunctionFieldFullC K M) //
              0 < P.ord (⟨ModularCurve.jqModC K, ModularCurve.jqModC_mem_full K M⟩ :
                ModularCurve.modularFunctionFieldFullC K M)} →
            DoubleCoset.Quotient
              (CongruenceSubgroup.Gamma0 M : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
              (Subgroup.zpowers (ModularGroup.S * ModularGroup.T) :
                Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)),
        Function.Injective ι ∧
        ∀ P (g : Matrix.SpecialLinearGroup (Fin 2) ℤ),
          ι P = DoubleCoset.mk (CongruenceSubgroup.Gamma0 M)
            (Subgroup.zpowers (ModularGroup.S * ModularGroup.T)) g →
          ∀ γ : CongruenceSubgroup.Gamma0 M,
            g⁻¹ * (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) * g ∈
              Subgroup.zpowers (ModularGroup.S * ModularGroup.T) →
            ∀ Q : AlgebraicCurve.Place K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)),
              Q.toValuationSubring.comap (IntermediateField.inclusion hle).toRingHom =
                P.1.toValuationSubring →
              ρ γ • Q = Q) ∧
    (∃ ι : {P : AlgebraicCurve.Place K (ModularCurve.modularFunctionFieldFullC K M) //
              0 < P.ord ((⟨ModularCurve.jqModC K, ModularCurve.jqModC_mem_full K M⟩ :
                ModularCurve.modularFunctionFieldFullC K M) -
                algebraMap K (ModularCurve.modularFunctionFieldFullC K M) 1728)} →
            DoubleCoset.Quotient
              (CongruenceSubgroup.Gamma0 M : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
              (Subgroup.zpowers ModularGroup.S : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)),
        Function.Injective ι ∧
        ∀ P (g : Matrix.SpecialLinearGroup (Fin 2) ℤ),
          ι P = DoubleCoset.mk (CongruenceSubgroup.Gamma0 M) (Subgroup.zpowers ModularGroup.S) g →
          ∀ γ : CongruenceSubgroup.Gamma0 M,
            g⁻¹ * (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) * g ∈ Subgroup.zpowers ModularGroup.S →
            ∀ Q : AlgebraicCurve.Place K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)),
              Q.toValuationSubring.comap (IntermediateField.inclusion hle).toRingHom =
                P.1.toValuationSubring →
              ρ γ • Q = Q) := by
  classical
  have hMK : (M : K) ≠ 0 := fun h => hℓM ((CharP.cast_eq_zero_iff K ℓ M).mp h)
  constructor
  ·
    obtain ⟨E₀, hE, σv, Pb, Qb, hj, hσv, hPb, hQb, hbasis, h1, h2⟩ :=
      WeierstrassCurve.exists_j_eq_zero_torsion_basis_heq_vcInvFun_of_order_three K M hMK
    haveI := hE
    have h0 := main_at hℓM ρ hρ hle hfix 0 (ModularGroup.S * ModularGroup.T) (isOfFinOrder_ST) E₀ hj σv hσv
      Pb Qb hPb hQb hbasis (autPt_ιbOf_ST σv hσv hPb hQb h1 h2)
    have e0 : jF0 K M - algebraMap K (F0 K M) 0 = jF0 K M := by rw [map_zero, sub_zero]
    rw [e0] at h0
    exact h0
  ·
    obtain ⟨E₀, hE, σv, Pb, Qb, hj, hσv, hPb, hQb, hbasis, h1, h2⟩ :=
      WeierstrassCurve.exists_j_eq_1728_torsion_basis_heq_vcInvFun_of_order_four K M hMK
    haveI := hE
    exact main_at hℓM ρ hρ hle hfix 1728 ModularGroup.S (isOfFinOrder_S) E₀ hj σv hσv
      Pb Qb hPb hQb hbasis (autPt_ιbOf_S σv hσv hPb hQb h1 h2)

end S_ModularCurve_exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_pos
end P2MW
export P2MW.S_ModularCurve_exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_pos (solution)
