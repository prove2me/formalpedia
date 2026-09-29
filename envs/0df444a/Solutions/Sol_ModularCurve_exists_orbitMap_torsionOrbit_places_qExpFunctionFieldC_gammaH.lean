-- Prove2me | solution 1 for ModularCurve.exists_orbitMap_torsionOrbit_places_qExpFunctionFieldC_gammaH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/73b3aa74-6b0f-58e3-89fa-d1ab3b0979ba

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_ModularCurve_exists_equiv_algHom_qExpFunctionFieldC_gammaH_of_transcendental_j
import Theorems.Thm_AlgebraicCurve_Place_ord_restrictAlong_eq_natCard_algHom_of_isGalois
import Theorems.Thm_ModularCurve_exists_equivariant_torsion_reduction_ofJ
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_orbitMap_torsionOrbit_places_qExpFunctionFieldC_gammaH
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂"
p2m_attr_erase "simp" "TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero"
p2m_attr_erase "simp" "ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open WeierstrassCurve WeierstrassCurve.Affine ModularCurve AlgebraicCurve
open scoped IntermediateField

noncomputable section

namespace P2MKcORBH

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

theorem autPt_injective {W : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • W = W) :
    Function.Injective (autPt γ hγ) := by
  intro P Q h
  rw [autPt_apply, autPt_apply] at h
  exact (Point.vcFun_rightInverse (C := γ) (W := W.toAffine)).injective ((castPt hγ).injective h)

end AutPt

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

theorem nsmul_of_addOrderOf_eq {P : A} (hP : addOrderOf P = M) : M • P = 0 := by
  rw [← hP]; exact addOrderOf_nsmul_eq_zero P

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

theorem image_orb (m : A →+ B) (P : A) : m '' orb H P = orb H (m P) := by
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

theorem XH.neg_image (s : XH A M H) : (fun T => -T) '' s.1 = s.1 := by
  obtain ⟨P, hP, hs⟩ := s.2
  rw [hs, show (fun T : A => -T) = (-(AddMonoidHom.id A) : A →+ A) from rfl, image_orb]
  exact orb_neg H (nsmul_of_addOrderOf_eq hP)

theorem XH.ext' {s s' : XH A M H} (h : s.1 = s'.1) : s = s' := Subtype.ext h

def tors (A : Type*) [AddCommGroup A] (M : ℕ) : Set A := {x | M • x = 0}

theorem XH.subset_tors (s : XH A M H) : s.1 ⊆ tors A M := fun _ hT => XH.nsmul_eq_zero s hT

theorem addOrderOf_map_of_injOn {φ : A →+ B} (hφ : Set.InjOn φ (tors A M)) {P : A}
    (hP : addOrderOf P = M) : addOrderOf (φ P) = M := by
  refine Nat.dvd_antisymm ?_ ?_
  · rw [← hP]; exact addOrderOf_map_dvd φ P
  · rw [← hP, addOrderOf_dvd_iff_nsmul_eq_zero]
    have h1 : addOrderOf (φ P) • φ P = 0 := addOrderOf_nsmul_eq_zero _
    have hmem : addOrderOf (φ P) • P ∈ tors A M := by
      show M • (addOrderOf (φ P) • P) = 0
      rw [nsmul_left_comm, nsmul_of_addOrderOf_eq hP, nsmul_zero]
    have h0 : (0 : A) ∈ tors A M := by show M • (0 : A) = 0; exact nsmul_zero _
    exact hφ hmem h0 (by rw [map_nsmul, h1, map_zero])

def mapX (φ : A →+ B) (hφ : Set.InjOn φ (tors A M)) (s : XH A M H) : XH B M H :=
  ⟨φ '' s.1, by
    obtain ⟨P, hP, hs⟩ := s.2
    exact ⟨φ P, addOrderOf_map_of_injOn hφ hP, by rw [hs, image_orb]⟩⟩

@[scoped simp] theorem mapX_val (φ : A →+ B) (hφ : Set.InjOn φ (tors A M)) (s : XH A M H) :
    (mapX φ hφ s).1 = φ '' s.1 := rfl

theorem mapX_injective {φ : A →+ B} (hφ : Set.InjOn φ (tors A M)) {s s' : XH A M H}
    (h : mapX φ hφ s = mapX φ hφ s') : s = s' := by
  have h1 : φ '' s.1 = φ '' s'.1 := congrArg Subtype.val h
  exact XH.ext' ((hφ.image_eq_image_iff (XH.subset_tors s) (XH.subset_tors s')).mp h1)

theorem mapX_surjective {φ : A →+ B} (hφ : Set.InjOn φ (tors A M))
    (hsurj : ∀ y ∈ tors B M, ∃ x ∈ tors A M, φ x = y) (s₀ : XH B M H) :
    ∃ s : XH A M H, mapX φ hφ s = s₀ := by
  obtain ⟨Q, hQ, hs₀⟩ := s₀.2
  obtain ⟨P, hPt, rfl⟩ := hsurj Q (nsmul_of_addOrderOf_eq hQ)
  have hordP : addOrderOf P = M := by
    refine Nat.dvd_antisymm (addOrderOf_dvd_of_nsmul_eq_zero hPt) ?_
    rw [← hQ]
    exact addOrderOf_map_dvd φ P
  refine ⟨⟨orb H P, P, hordP, rfl⟩, XH.ext' ?_⟩
  rw [mapX_val, hs₀]
  exact image_orb H φ P

theorem mapX_eq_of_forall_mem (φ : A →+ B) (hφ : Set.InjOn φ (tors A M))
    (s : XH A M H) (s' : XH B M H) (h : ∀ T ∈ s.1, φ T ∈ s'.1) : mapX φ hφ s = s' := by
  apply XH.ext'
  obtain ⟨P, hP, hs⟩ := s.2
  have hPs : P ∈ s.1 := by rw [hs]; exact mem_orb_self H (nsmul_of_addOrderOf_eq hP)
  rw [mapX_val, hs, image_orb, XH.eq_orb_of_mem s' (h P hPs)]

end Orb

section Assemble

variable {L : Type*} [Field L] [DecidableEq L] {E₀ : WeierstrassCurve L} {M : ℕ} [NeZero M]
variable {H : Subgroup (ZMod M)ˣ}
variable {Pt : Type*} [AddCommGroup Pt]
variable {G : Type*}
variable {X : Type*}
variable {Pl : Type*}

def Rel (E₀ : WeierstrassCurve L) (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (s s' : XH E₀.toAffine.Point M H) : Prop :=
  ∃ γ : VariableChange L, γ • E₀ = E₀ ∧
    ∀ T ∈ s.1, ∃ T' ∈ s'.1, HEq (Point.vcInvFun γ E₀.toAffine T) T'

theorem Rel_iff (s s' : XH E₀.toAffine.Point M H) :
    Rel E₀ M H s s' ↔ ∃ γ : VariableChange L, ∃ hγ : γ • E₀ = E₀, ∀ T ∈ s.1, autPt γ hγ T ∈ s'.1 := by
  unfold Rel
  constructor
  · rintro ⟨γ, hγ, h⟩
    refine ⟨γ, hγ, fun T hT => ?_⟩
    obtain ⟨T', hT', hh⟩ := h T hT
    rwa [(autPt_eq_iff_heq γ hγ T T').mpr hh]
  · rintro ⟨γ, hγ, h⟩
    exact ⟨γ, hγ, fun T hT => ⟨autPt γ hγ T, h T hT, (autPt_eq_iff_heq γ hγ T _).mp rfl⟩⟩

theorem Rel_iff_image_eq (s s' : XH E₀.toAffine.Point M H) :
    Rel E₀ M H s s' ↔ ∃ γ : VariableChange L, ∃ hγ : γ • E₀ = E₀, autPt γ hγ '' s.1 = s'.1 := by
  rw [Rel_iff]
  refine exists_congr fun γ => exists_congr fun hγ => ?_
  constructor
  · intro h
    exact congrArg Subtype.val
      (mapX_eq_of_forall_mem (autPt γ hγ) (autPt_injective γ hγ).injOn s s' h)
  · intro h T hT
    rw [← h]; exact Set.mem_image_of_mem _ hT

theorem assemble
    (θ : Pt →+ E₀.toAffine.Point) (hθ : Set.InjOn θ (tors Pt M))
    (hθs : ∀ y ∈ tors E₀.toAffine.Point M, ∃ x ∈ tors Pt M, θ x = y)
    (D : G → Prop) (act : G → (Pt →+ Pt)) (hact : ∀ σ, Function.Injective (act σ))
    (ρ : G → VariableChange L) (hρ : ∀ σ, D σ → ρ σ • E₀ = E₀)
    (hequiv : ∀ σ (hσ : D σ) (P : Pt), θ (act σ P) = autPt (ρ σ) (hρ σ hσ) (θ P))
    (hsurj : ∀ (γ : VariableChange L) (hγ : γ • E₀ = E₀), ∃ σ, D σ ∧
      ((∀ P, θ (act σ P) = autPt γ hγ (θ P)) ∨ (∀ P, θ (act σ P) = -autPt γ hγ (θ P))))
    (Φ : XH Pt M H ≃ X) (actX : G → X → X)
    (hnat : ∀ σ (s : XH Pt M H), Φ (mapX (act σ) (hact σ).injOn s) = actX σ (Φ s))
    (π : X → Pl) (S : Finset Pl) (hπS : ∀ x, π x ∈ S) (hπsurj : ∀ P ∈ S, ∃ x, π x = P)
    (hπfib : ∀ x x', π x = π x' ↔ ∃ σ, D σ ∧ x' = actX σ x)
    (e : Pl → ℤ) (hπe : ∀ x, e (π x) = Nat.card {x' // π x' = π x}) :
    ∃ f : XH E₀.toAffine.Point M H → Pl,
      (∀ s, f s ∈ S) ∧ (∀ P ∈ S, ∃ s, f s = P) ∧
      (∀ s s', f s = f s' ↔ Rel E₀ M H s s') ∧
      ∀ s, e (f s) = Nat.card {s' // f s' = f s} := by
  classical

  let Ξf : XH Pt M H → XH E₀.toAffine.Point M H := fun s => mapX θ hθ s
  have hΞ : Function.Bijective Ξf :=
    ⟨fun s s' h => mapX_injective hθ h, fun s₀ => mapX_surjective hθ hθs s₀⟩
  let Ξ : XH Pt M H ≃ XH E₀.toAffine.Point M H := Equiv.ofBijective Ξf hΞ
  have Ξ_val : ∀ s, (Ξ s).1 = θ '' s.1 := fun s => rfl

  let ε : XH E₀.toAffine.Point M H ≃ X := Ξ.symm.trans Φ
  refine ⟨fun s₀ => π (ε s₀), fun s₀ => hπS _, ?_, ?_, ?_⟩
  ·
    intro P hP
    obtain ⟨x, hx⟩ := hπsurj P hP
    exact ⟨ε.symm x, by simp only [Equiv.apply_symm_apply, hx]⟩
  ·
    intro s₀ s₀'
    rw [hπfib, Rel_iff_image_eq]

    have key : ∀ σ (hσ : D σ) (s : XH Pt M H),
        (Ξ (mapX (act σ) (hact σ).injOn s)).1 = autPt (ρ σ) (hρ σ hσ) '' (Ξ s).1 := by
      intro σ hσ s
      rw [Ξ_val, Ξ_val, mapX_val, Set.image_image, Set.image_image]
      exact Set.image_congr fun P _ => hequiv σ hσ P
    constructor
    · rintro ⟨σ, hσ, hx⟩
      have h1 : Φ (Ξ.symm s₀') = Φ (mapX (act σ) (hact σ).injOn (Ξ.symm s₀)) := by
        rw [hnat]; exact hx
      have h2 : Ξ.symm s₀' = mapX (act σ) (hact σ).injOn (Ξ.symm s₀) := Φ.injective h1
      refine ⟨ρ σ, hρ σ hσ, ?_⟩
      have h3 := key σ hσ (Ξ.symm s₀)
      rw [← h2, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h3
      exact h3.symm
    · rintro ⟨γ, hγ, hmap⟩
      obtain ⟨σ, hσ, hsgn⟩ := hsurj γ hγ
      refine ⟨σ, hσ, ?_⟩
      have h1 : (Ξ (mapX (act σ) (hact σ).injOn (Ξ.symm s₀))).1 = s₀'.1 := by
        rw [Ξ_val, mapX_val, Set.image_image]
        have hs₀ : θ '' (Ξ.symm s₀).1 = s₀.1 := by
          rw [← Ξ_val, Equiv.apply_symm_apply]
        rcases hsgn with h | h
        · rw [Set.image_congr fun P _ => h P, ← Set.image_image (autPt γ hγ) θ, hs₀, hmap]
        · rw [Set.image_congr fun P _ => h P,
            show (fun P => -autPt γ hγ (θ P)) = (fun T => -T) ∘ (autPt γ hγ) ∘ θ from rfl,
            Set.image_comp, Set.image_comp, hs₀, hmap, XH.neg_image]
      have h2 : Ξ (mapX (act σ) (hact σ).injOn (Ξ.symm s₀)) = s₀' := Subtype.ext h1
      show Φ (Ξ.symm s₀') = actX σ (Φ (Ξ.symm s₀))
      rw [← hnat, ← h2, Equiv.symm_apply_apply]
  ·
    intro s₀
    rw [hπe]
    congr 1
    exact Nat.card_congr ((Equiv.subtypeEquiv ε (fun s₀' => Iff.rfl)).symm)

end Assemble

section Supplies

theorem isIntegral_of_apply_eq {K F M : Type*} [Field K] [Field F] [Field M] [Algebra K F]
    [Algebra K M] (x : F) (t : M) [FiniteDimensional K⟮t⟯ M] (ψ : F →ₐ[K] M) (hψ : ψ x = t) :
    ψ.toRingHom.IsIntegral := by
  intro y
  have hy : IsIntegral K⟮t⟯ y := Algebra.IsIntegral.isIntegral y
  obtain ⟨q, hqm, hq0⟩ := hy
  have hle : K⟮t⟯ ≤ ψ.fieldRange := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ rfl
    exact ⟨x, hψ⟩
  have hlifts : q.map (algebraMap K⟮t⟯ M) ∈ Polynomial.lifts ψ.toRingHom := by
    refine (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ?_
    rw [Polynomial.coeff_map]
    obtain ⟨f, hf⟩ := hle (q.coeff n).2
    exact ⟨f, hf⟩
  obtain ⟨q', hq'map, -, hq'monic⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic hlifts (hqm.map _)
  refine ⟨q', hq'monic, ?_⟩
  rw [← Polynomial.eval_map, hq'map, Polynomial.eval_map]
  exact hq0

variable {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K]

theorem tors_facts (E₀ : WeierstrassCurve K) [E₀.IsElliptic] {M : ℕ} [NeZero M] (hM : (M : K) ≠ 0) :
    Nat.card (tors E₀.toAffine.Point M) = M ^ 2 ∧ ∃ g : E₀.toAffine.Point, addOrderOf g = M := by
  obtain ⟨eT⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
    (F := K) (K := K) E₀ hM
  have hb : (E₀⁄K) = E₀.toAffine := by
    show (E₀.baseChange K).toAffine = E₀.toAffine
    rw [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]
  rw [hb] at eT
  have hmem : ∀ P : E₀.toAffine.Point, P ∈ Submodule.torsionBy ℤ E₀.toAffine.Point M ↔ P ∈ tors _ M := by
    intro P
    rw [Submodule.mem_torsionBy_iff]
    show ((M : ℤ) • P = 0) ↔ M • P = 0
    rw [natCast_zsmul]
  have hset : (Submodule.torsionBy ℤ E₀.toAffine.Point M : Set E₀.toAffine.Point) = tors _ M :=
    Set.ext hmem
  constructor
  · have h1 : Nat.card (Submodule.torsionBy ℤ E₀.toAffine.Point M) = M ^ 2 := by
      rw [← Nat.card_congr eT.toEquiv, Nat.card_prod, Nat.card_zmod, sq]
    rw [← SetLike.coe_sort_coe, hset] at h1
    exact h1
  · refine ⟨(eT (1, 0)).1, ?_⟩
    have h1 : addOrderOf ((eT (1, 0)).1) = addOrderOf (eT (1, 0)) :=
      addOrderOf_injective (Submodule.torsionBy ℤ E₀.toAffine.Point M).subtype.toAddMonoidHom
        Subtype.val_injective (eT (1, 0))
    rw [h1, AddEquiv.addOrderOf_eq eT, Prod.addOrderOf_mk, ZMod.addOrderOf_one, addOrderOf_zero,
      Nat.lcm_one_right]

end Supplies

end P2MKcORBH
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_torsionOrbit_places_qExpFunctionFieldC_gammaH.P2MKcORBH"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_torsionOrbit_places_qExpFunctionFieldC_gammaH.P2MKcORBH"

open P2MKcORBH in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0)
    (H : Subgroup (ZMod M)ˣ) (j₀ : K) (E₀ : WeierstrassCurve K) [E₀.IsElliptic] (hE₀ : E₀.j = j₀)
    (x : qExpFunctionFieldC K (CohCarrier.GammaH M H)) (hx : (x : LaurentSeries K) = jqModC K)
    (S : Finset (Place K (qExpFunctionFieldC K (CohCarrier.GammaH M H))))
    (hS : ∀ Q, Q ∈ S ↔
      0 < Q.ord (x - algebraMap K (qExpFunctionFieldC K (CohCarrier.GammaH M H)) j₀)) :
    ∃ f : {s : Set E₀.toAffine.Point // ∃ P : E₀.toAffine.Point, addOrderOf P = M ∧
            s = {T | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧ T = (u : ZMod M).val • P}} →
        Place K (qExpFunctionFieldC K (CohCarrier.GammaH M H)),
      (∀ s, f s ∈ S) ∧ (∀ Q ∈ S, ∃ s, f s = Q) ∧
      (∀ s s', f s = f s' ↔ ∃ γ : VariableChange K, γ • E₀ = E₀ ∧
        ∀ T ∈ s.1, ∃ T' ∈ s'.1, HEq (Point.vcInvFun γ E₀.toAffine T) T') ∧
      ∀ s, (f s).ord (x - algebraMap K (qExpFunctionFieldC K (CohCarrier.GammaH M H)) j₀) =
        (Nat.card {s' : {s : Set E₀.toAffine.Point // ∃ P : E₀.toAffine.Point, addOrderOf P = M ∧
            s = {T | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧ T = (u : ZMod M).val • P}} //
          f s' = f s} : ℤ) := by
  classical
  let F := qExpFunctionFieldC K (CohCarrier.GammaH M H)
  obtain ⟨p, hp⟩ := CharP.exists K
  have hpM : ¬ p ∣ M := fun h => hM ((CharP.cast_eq_zero_iff K p M).mpr h)

  obtain ⟨𝕄, _iF, _iD, _iA, t, ht, hfin, hgal, W₀, hW₀, θ, ρ, hfull, hθinj, hρE, -, hequivC,
    hsurjC, -⟩ := ModularCurve.exists_equivariant_torsion_reduction_ofJ K p M hM j₀ E₀ hE₀
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

  obtain ⟨Φ, hnatA⟩ :=
    ModularCurve.exists_equiv_algHom_qExpFunctionFieldC_gammaH_of_transcendental_j
      K M hM H x hx K⟮t⟯ 𝕄 E hEtr hfull

  let X : Type _ := {ψ : F →ₐ[K] 𝕄 // ψ x = t}
  let embX : {ψ : F →ₐ[K] 𝕄 // ψ x = algebraMap K⟮t⟯ 𝕄 E.j} ≃ X :=
    Equiv.subtypeEquivRight (fun ψ => by rw [hjt])
  let ΦX : XH (E.baseChange 𝕄).toAffine.Point M H ≃ X := Φ.trans embX
  have ΦX_val : ∀ s, (ΦX s).1 = (Φ s).1 := fun s => rfl

  have hint : ∀ ψ : F →ₐ[K] 𝕄, ψ x = t → ψ.toRingHom.IsIntegral :=
    fun ψ hψ => isIntegral_of_apply_eq x t ψ hψ

  obtain ⟨hcard₀, g₀, hg₀⟩ := tors_facts E₀ hM
  have hθ : Set.InjOn θ (tors (E.baseChange 𝕄).toAffine.Point M) := by
    intro P hP Q hQ h
    have hPQ : M • (P - Q) = 0 := by
      rw [nsmul_sub, show M • P = 0 from hP, show M • Q = 0 from hQ, sub_zero]
    have := hθinj M (P - Q) hpM hPQ (by rw [map_sub, h, sub_self])
    exact sub_eq_zero.mp this
  have hθs : ∀ y ∈ tors E₀.toAffine.Point M, ∃ x ∈ tors (E.baseChange 𝕄).toAffine.Point M, θ x = y := by
    let θr : tors (E.baseChange 𝕄).toAffine.Point M → tors E₀.toAffine.Point M :=
      fun P => ⟨θ P.1, show M • θ P.1 = 0 by rw [← map_nsmul, show M • P.1 = 0 from P.2, map_zero]⟩
    have hinj : Function.Injective θr := fun P Q h =>
      Subtype.ext (hθ P.2 Q.2 (congrArg Subtype.val h))
    haveI : Finite (tors E₀.toAffine.Point M) :=
      Nat.finite_of_card_ne_zero (by rw [hcard₀]; exact pow_ne_zero 2 (NeZero.ne M))
    have hbij := hinj.bijective_of_nat_card_le (by
      rw [hcard₀]
      exact le_of_eq hfull.symm)
    intro y hy
    obtain ⟨x, hx⟩ := hbij.2 ⟨y, hy⟩
    exact ⟨x.1, x.2, congrArg Subtype.val hx⟩

  obtain ⟨s₁, -⟩ := mapX_surjective (H := H) hθ hθs ⟨orb H g₀, g₀, hg₀, rfl⟩
  let ι : F →ₐ[K] 𝕄 := (ΦX s₁).1
  have hι : ι x = t := (ΦX s₁).2

  obtain ⟨-, hBi, hBii, hBiii, hBiv⟩ :=
    AlgebraicCurve.Place.ord_restrictAlong_eq_natCard_algHom_of_isGalois K x t j₀ ι hι hfin hgal
      hint W₀ hW₀

  let D : (𝕄 ≃ₐ[K⟮t⟯] 𝕄) → Prop := fun σ => SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀
  let act : (𝕄 ≃ₐ[K⟮t⟯] 𝕄) → ((E.baseChange 𝕄).toAffine.Point →+ (E.baseChange 𝕄).toAffine.Point) :=
    fun σ => WeierstrassCurve.Affine.Point.map (σ : 𝕄 →ₐ[K⟮t⟯] 𝕄)
  have hact : ∀ σ, Function.Injective (act σ) := fun σ =>
    WeierstrassCurve.Affine.Point.map_injective (W' := E) (σ : 𝕄 →ₐ[K⟮t⟯] 𝕄)
  have hσt : ∀ σ : 𝕄 ≃ₐ[K⟮t⟯] 𝕄, σ t = t := fun σ => σ.commutes tk
  let actX : (𝕄 ≃ₐ[K⟮t⟯] 𝕄) → X → X := fun σ ψ =>
    ⟨((σ : 𝕄 →ₐ[K⟮t⟯] 𝕄).restrictScalars K).comp ψ.1, by
      show σ (ψ.1 x) = t
      rw [ψ.2, hσt]⟩
  have hnat : ∀ σ (s : XH (E.baseChange 𝕄).toAffine.Point M H),
      ΦX (mapX (act σ) (hact σ).injOn s) = actX σ (ΦX s) := by
    intro σ s
    apply Subtype.ext
    rw [ΦX_val]
    exact hnatA σ s (mapX (act σ) (hact σ).injOn s) rfl

  have hequiv : ∀ σ (hσ : D σ) (P : (E.baseChange 𝕄).toAffine.Point),
      θ (act σ P) = autPt (ρ σ) (hρE σ hσ) (θ P) :=
    fun σ hσ P => ((autPt_eq_iff_heq _ _ _ _).mpr (hequivC σ hσ P)).symm
  have hsurj : ∀ (γ : VariableChange K) (hγ : γ • E₀ = E₀), ∃ σ, D σ ∧
      ((∀ P, θ (act σ P) = autPt γ hγ (θ P)) ∨ (∀ P, θ (act σ P) = -autPt γ hγ (θ P))) := by
    intro γ hγ
    obtain ⟨σ, hσ, h⟩ := hsurjC γ hγ
    refine ⟨σ, hσ, ?_⟩
    rcases h with h | h
    · exact Or.inl fun P => ((autPt_eq_iff_heq _ _ _ _).mpr (h P)).symm
    · refine Or.inr fun P => ?_
      have := (autPt_eq_iff_heq γ hγ (θ P) _).mpr (h P)
      rw [this, neg_neg]

  let π : X → Place K F := fun ψ => W₀.restrictAlong ψ.1 (hint ψ.1 ψ.2)
  have hπS : ∀ ψ, π ψ ∈ S := fun ψ => (hS _).mpr (hBi ψ.1 ψ.2)
  have hπsurj : ∀ P ∈ S, ∃ ψ, π ψ = P := by
    intro P hP
    obtain ⟨ψ, hψ, h⟩ := hBii P ((hS P).mp hP)
    exact ⟨⟨ψ, hψ⟩, h⟩
  have hπfib : ∀ ψ ψ' : X, π ψ = π ψ' ↔ ∃ σ, D σ ∧ ψ' = actX σ ψ := by
    intro ψ ψ'
    rw [show (π ψ = π ψ') = (W₀.restrictAlong ψ.1 (hint ψ.1 ψ.2) =
      W₀.restrictAlong ψ'.1 (hint ψ'.1 ψ'.2)) from rfl, hBiii ψ.1 ψ'.1 ψ.2 ψ'.2]
    refine exists_congr fun σ => and_congr_right fun _ => ?_
    rw [Subtype.ext_iff]
  let e : Place K F → ℤ := fun P => P.ord (x - algebraMap K F j₀)
  have hπe : ∀ ψ : X, e (π ψ) = Nat.card {ψ' // π ψ' = π ψ} := fun ψ => hBiv ψ.1 ψ.2

  obtain ⟨f, hfS, hfsurj, hfib, hord⟩ := assemble θ hθ hθs D act hact ρ hρE hequiv hsurj ΦX actX
    hnat π S hπS hπsurj hπfib e hπe
  exact ⟨f, hfS, hfsurj, fun s s' => (hfib s s').trans Iff.rfl, hord⟩

end S_ModularCurve_exists_orbitMap_torsionOrbit_places_qExpFunctionFieldC_gammaH
end P2MW
export P2MW.S_ModularCurve_exists_orbitMap_torsionOrbit_places_qExpFunctionFieldC_gammaH (solution)
