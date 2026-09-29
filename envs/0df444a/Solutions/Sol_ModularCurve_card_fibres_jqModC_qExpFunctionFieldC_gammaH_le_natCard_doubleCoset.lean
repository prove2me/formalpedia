-- Prove2me | solution 1 for ModularCurve.card_fibres_jqModC_qExpFunctionFieldC_gammaH_le_natCard_doubleCoset
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/f925c003-b8c4-5cdd-b913-317a89b275ca

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_XHDiamondModL
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_zmod
import Theorems.Thm_ModularCurve_existsUnique_algEquiv_qExpFunctionFieldC_coe_apply_eq_coeffMap
import Theorems.Thm_ModularCurve_coe_mem_modularFunctionFieldFullC_of_forall_diamondPullbackModL_apply_eq
import Theorems.Thm_ModularCurve_exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_pos
import Theorems.Thm_ModularCurve_exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_neg
import Theorems.Thm_AlgebraicCurve_Place_exists_algEquiv_smul_eq_of_restrict_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_card_fibres_jqModC_qExpFunctionFieldC_gammaH_le_natCard_doubleCoset
p2m_attr_erase "instance" "CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd"
p2m_attr_erase "instance" "KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single"
p2m_attr_erase "simp" "ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec"
p2m_attr_erase "simp" "TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

p2m_open "ModularCurve~coeffMap_injective IntermediateField HahnSeries CongruenceSubgroup CohCarrier AlgebraicCurve"
open scoped MatrixGroups ModularForm

namespace XHFibreCount

section BaseChange

variable {K₀ K : Type*} [Field K₀] [Field K] (φ : K₀ →+* K) (Γ : Subgroup SL(2, ℤ))

theorem coeffMap_intSeriesC (p : PowerSeries ℤ) : coeffMap φ (intSeriesC K₀ p) = intSeriesC K p := by
  rw [intSeriesC, intSeriesC, coeffMap_ofPowerSeries, ← RingHom.comp_apply (PowerSeries.map φ),
    ← PowerSeries.map_comp, RingHom.ext_int (φ.comp (Int.castRingHom K₀)) (Int.castRingHom K)]

theorem coeffMap_injective : Function.Injective (coeffMap φ) := by
  intro x y h
  ext n
  have := congrArg (fun z : LaurentSeries K => z.coeff n) h
  simp only [coeffMap_coeff] at this
  exact φ.injective this

include φ in
theorem intSeriesC_ne_zero_iff (p : PowerSeries ℤ) : intSeriesC K p ≠ 0 ↔ intSeriesC K₀ p ≠ 0 := by
  rw [← coeffMap_intSeriesC φ]
  refine ⟨fun h h0 => h (by rw [h0, map_zero]), fun h h0 => h ?_⟩
  exact coeffMap_injective φ (h0.trans (map_zero _).symm)

theorem coeffMap_mem {x : LaurentSeries K₀} (hx : x ∈ qExpFunctionFieldC K₀ Γ) :
    coeffMap φ x ∈ qExpFunctionFieldC K Γ := by
  let T : Subfield (LaurentSeries K₀) := (qExpFunctionFieldC K Γ).toSubfield.comap (coeffMap φ)
  have hgen : intFormRatiosC K₀ Γ ⊆ (T : Set (LaurentSeries K₀)) := by
    rintro y ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
    change coeffMap φ (intSeriesC K₀ pf / intSeriesC K₀ pg) ∈ qExpFunctionFieldC K Γ
    rw [map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]
    exact div_mem_qExpFunctionFieldC f g hf hg ((intSeriesC_ne_zero_iff φ pg).mpr hg0)
  have hconst : Set.range (algebraMap K₀ (LaurentSeries K₀)) ⊆ (T : Set (LaurentSeries K₀)) := by
    rintro y ⟨c, rfl⟩
    change coeffMap φ (algebraMap K₀ (LaurentSeries K₀) c) ∈ qExpFunctionFieldC K Γ
    rw [algebraMap_laurentSeries_eq_single, coeffMap_single, ← algebraMap_laurentSeries_eq_single]
    exact (qExpFunctionFieldC K Γ).algebraMap_mem _
  have hle : (qExpFunctionFieldC K₀ Γ).toSubfield ≤ T := by
    rw [qExpFunctionFieldC, IntermediateField.adjoin_toSubfield]
    exact Subfield.closure_le.mpr (Set.union_subset hconst hgen)
  exact hle hx

theorem intFormRatiosC_eq_image :
    intFormRatiosC K Γ = coeffMap φ '' intFormRatiosC K₀ Γ := by
  ext y
  constructor
  · rintro ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
    refine ⟨intSeriesC K₀ pf / intSeriesC K₀ pg,
      ⟨k, f, g, pf, pg, hf, hg, (intSeriesC_ne_zero_iff φ pg).mp hg0, rfl⟩, ?_⟩
    rw [map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]
  · rintro ⟨x, ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩, rfl⟩
    refine ⟨k, f, g, pf, pg, hf, hg, (intSeriesC_ne_zero_iff φ pg).mpr hg0, ?_⟩
    rw [map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]

def iota : qExpFunctionFieldC K₀ Γ →+* qExpFunctionFieldC K Γ where
  toFun y := ⟨coeffMap φ y, coeffMap_mem φ Γ y.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ _ _)

@[scoped simp] theorem coe_iota (y : qExpFunctionFieldC K₀ Γ) :
    ((iota φ Γ y : qExpFunctionFieldC K Γ) : LaurentSeries K) = coeffMap φ y := rfl

def liftAut (σ₀ : qExpFunctionFieldC K₀ Γ ≃ₐ[K₀] qExpFunctionFieldC K₀ Γ) :
    qExpFunctionFieldC K Γ ≃ₐ[K] qExpFunctionFieldC K Γ :=
  (ModularCurve.existsUnique_algEquiv_qExpFunctionFieldC_coe_apply_eq_coeffMap φ Γ σ₀).choose

theorem liftAut_iota (σ₀ : qExpFunctionFieldC K₀ Γ ≃ₐ[K₀] qExpFunctionFieldC K₀ Γ)
    (x₀ : qExpFunctionFieldC K₀ Γ) :
    liftAut φ Γ σ₀ (iota φ Γ x₀) = iota φ Γ (σ₀ x₀) :=
  Subtype.ext ((ModularCurve.existsUnique_algEquiv_qExpFunctionFieldC_coe_apply_eq_coeffMap
    φ Γ σ₀).choose_spec.1 x₀ (iota φ Γ x₀) rfl)

theorem liftAut_unique (σ₀ : qExpFunctionFieldC K₀ Γ ≃ₐ[K₀] qExpFunctionFieldC K₀ Γ)
    (τ : qExpFunctionFieldC K Γ ≃ₐ[K] qExpFunctionFieldC K Γ)
    (hτ : ∀ x₀ : qExpFunctionFieldC K₀ Γ, τ (iota φ Γ x₀) = iota φ Γ (σ₀ x₀)) :
    τ = liftAut φ Γ σ₀ := by
  refine (ModularCurve.existsUnique_algEquiv_qExpFunctionFieldC_coe_apply_eq_coeffMap
    φ Γ σ₀).choose_spec.2 τ ?_
  intro x₀ x hx
  have : x = iota φ Γ x₀ := Subtype.ext hx
  rw [this, hτ]
  rfl

theorem liftAut_one : liftAut φ Γ (1 : qExpFunctionFieldC K₀ Γ ≃ₐ[K₀] qExpFunctionFieldC K₀ Γ) = 1 :=
  (liftAut_unique φ Γ 1 1 fun x₀ => rfl).symm

theorem liftAut_mul (σ₀ τ₀ : qExpFunctionFieldC K₀ Γ ≃ₐ[K₀] qExpFunctionFieldC K₀ Γ) :
    liftAut φ Γ (σ₀ * τ₀) = liftAut φ Γ σ₀ * liftAut φ Γ τ₀ := by
  refine (liftAut_unique φ Γ (σ₀ * τ₀) _ fun x₀ => ?_).symm
  rw [AlgEquiv.mul_apply, liftAut_iota, liftAut_iota, AlgEquiv.mul_apply]

def liftHom : (qExpFunctionFieldC K₀ Γ ≃ₐ[K₀] qExpFunctionFieldC K₀ Γ) →*
    (qExpFunctionFieldC K Γ ≃ₐ[K] qExpFunctionFieldC K Γ) where
  toFun := liftAut φ Γ
  map_one' := liftAut_one φ Γ
  map_mul' := liftAut_mul φ Γ

@[scoped simp] theorem liftHom_apply (σ₀ : qExpFunctionFieldC K₀ Γ ≃ₐ[K₀] qExpFunctionFieldC K₀ Γ) :
    liftHom φ Γ σ₀ = liftAut φ Γ σ₀ := rfl

theorem exists_iota_eq_of_coe_eq_div (x : qExpFunctionFieldC K Γ) (a b : PowerSeries ℤ)
    (hx : (x : LaurentSeries K) = intSeriesC K a / intSeriesC K b)
    (hmem : intSeriesC K₀ a / intSeriesC K₀ b ∈ qExpFunctionFieldC K₀ Γ) :
    ∃ x₀ : qExpFunctionFieldC K₀ Γ, (x₀ : LaurentSeries K₀) = intSeriesC K₀ a / intSeriesC K₀ b ∧
      iota φ Γ x₀ = x := by
  refine ⟨⟨_, hmem⟩, rfl, Subtype.ext ?_⟩
  rw [coe_iota, hx]
  change coeffMap φ (intSeriesC K₀ a / intSeriesC K₀ b) = _
  rw [map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]

end BaseChange

section DiamondK

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [Fact ℓ.Prime]
  (K : Type*) [Field K] [CharP K ℓ]

abbrev FbK : Type _ := ↥(qExpFunctionFieldC K (GammaH M H))

def phiK : ZMod ℓ →+* K := ZMod.castHom (dvd_refl ℓ) K

variable {M H ℓ K}

def rhoF (hℓM : ¬ ℓ ∣ M) : Gamma0 M →* (FbK M H (ZMod ℓ) ≃ₐ[ZMod ℓ] FbK M H (ZMod ℓ)) :=
  (ModularCurve.exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_zmod ℓ M hℓM H).choose

variable (K) in

def rhoK (hℓM : ¬ ℓ ∣ M) : Gamma0 M →* (FbK M H K ≃ₐ[K] FbK M H K) :=
  (liftHom (phiK ℓ K) (GammaH M H)).comp (rhoF (H := H) hℓM)

theorem rhoK_apply (hℓM : ¬ ℓ ∣ M) (γ : Gamma0 M) :
    rhoK (H := H) K hℓM γ = liftAut (phiK ℓ K) (GammaH M H) (rhoF (H := H) hℓM γ) := rfl

theorem rhoK_iota (hℓM : ¬ ℓ ∣ M) (γ : Gamma0 M) (x₀ : FbK M H (ZMod ℓ)) :
    rhoK (H := H) K hℓM γ (iota (phiK ℓ K) (GammaH M H) x₀) =
      iota (phiK ℓ K) (GammaH M H) (rhoF (H := H) hℓM γ x₀) := by
  rw [rhoK_apply, liftAut_iota]

theorem rhoK_pullback (hℓM : ¬ ℓ ∣ M) : IsDiamondPullbackModL K M H (rhoK (H := H) K hℓM) := by
  intro γ k f g f₁ g₁ pf pg pf₁ pg₁ hf hg hf₁ hg₁ hfs hgs hpg x hx
  obtain ⟨_, h2, -, -, -⟩ :=
    (ModularCurve.exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_zmod ℓ M hℓM H).choose_spec
  have hpg0 : intSeriesC (ZMod ℓ) pg ≠ 0 := (intSeriesC_ne_zero_iff (phiK ℓ K) pg).mp hpg

  have hmem : intSeriesC (ZMod ℓ) pf₁ / intSeriesC (ZMod ℓ) pg₁ ∈
      qExpFunctionFieldC (ZMod ℓ) (GammaH M H) := by
    by_cases h0 : intSeriesC (ZMod ℓ) pg₁ = 0
    · rw [h0, div_zero]; exact zero_mem _
    · exact div_mem_qExpFunctionFieldC f₁ g₁ hf₁ hg₁ h0
  obtain ⟨x₀, hx₀, rfl⟩ := exists_iota_eq_of_coe_eq_div (phiK ℓ K) (GammaH M H) x pf₁ pg₁ hx hmem
  rw [rhoK_iota, coe_iota,
    show ((rhoF (H := H) hℓM γ x₀ : FbK M H (ZMod ℓ)) : LaurentSeries (ZMod ℓ)) = _ from
      h2 γ k f g f₁ g₁ pf pg pf₁ pg₁ hf hg hf₁ hg₁ hfs hgs hpg0 x₀ hx₀,
    map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]

theorem rhoK_eq_one_of_mem_sup (hℓM : ¬ ℓ ∣ M) (γ : Gamma0 M)
    (hγ : (γ : SL(2, ℤ)) ∈ GammaH M (H ⊔ Subgroup.zpowers (-1))) : rhoK (H := H) K hℓM γ = 1 := by
  obtain ⟨-, -, h3, -, -⟩ :=
    (ModularCurve.exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_zmod ℓ M hℓM H).choose_spec
  rw [rhoK_apply, show rhoF (H := H) hℓM γ = 1 from h3 γ hγ, liftAut_one]

theorem rhoK_eq_one_of_mem (hℓM : ¬ ℓ ∣ M) (γ : Gamma0 M)
    (hγ : (γ : SL(2, ℤ)) ∈ GammaH M H) : rhoK (H := H) K hℓM γ = 1 :=
  rhoK_eq_one_of_mem_sup hℓM γ (GammaH_mono le_sup_left hγ)

theorem full_le (hℓM : ¬ ℓ ∣ M) :
    modularFunctionFieldFullC K M ≤ qExpFunctionFieldC K (GammaH M H) := by
  obtain ⟨-, -, -, h4, -⟩ :=
    (ModularCurve.exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_zmod ℓ M hℓM H).choose_spec
  rw [modularFunctionFieldFullC, adjoin_le_iff]
  rintro y ⟨d, hne, hd, rfl⟩
  haveI := hne
  have h0 : qExpand (ZMod ℓ) d (jqModC (ZMod ℓ)) ∈ qExpFunctionFieldC (ZMod ℓ) (GammaH M H) :=
    h4 (jqModCd_mem_full (ZMod ℓ) M hd)
  have := coeffMap_mem (phiK ℓ K) (GammaH M H) h0
  rwa [coeffMap_qExpand, coeffMap_jqModC] at this

theorem rhoK_apply_eq_self_of_mem_full (hℓM : ¬ ℓ ∣ M) (γ : Gamma0 M) (x : FbK M H K)
    (hx : (x : LaurentSeries K) ∈ modularFunctionFieldFullC K M) : rhoK (H := H) K hℓM γ x = x := by
  obtain ⟨-, -, -, h4, h5⟩ :=
    (ModularCurve.exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_zmod ℓ M hℓM H).choose_spec

  let E : IntermediateField K (FbK M H K) :=
    { carrier := {y | rhoK (H := H) K hℓM γ y = y}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_mul] at *; rw [ha, hb]
      one_mem' := map_one _
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add] at *; rw [ha, hb]
      zero_mem' := map_zero _
      algebraMap_mem' := fun c => (rhoK (H := H) K hℓM γ).commutes c
      inv_mem' := fun x hx => by
        simp only [Set.mem_setOf_eq, map_inv₀] at *; rw [hx] }
  have hE : ∀ z : FbK M H K, z ∈ E ↔ rhoK (H := H) K hℓM γ z = z := fun z => Iff.rfl
  suffices hle : modularFunctionFieldFullC K M ≤ IntermediateField.lift E by
    have := hle hx
    exact (hE x).mp ((mem_lift x).mp this)
  rw [modularFunctionFieldFullC, adjoin_le_iff]
  rintro y ⟨d, hne, hd, rfl⟩
  haveI := hne
  have h0 : qExpand (ZMod ℓ) d (jqModC (ZMod ℓ)) ∈ qExpFunctionFieldC (ZMod ℓ) (GammaH M H) :=
    h4 (jqModCd_mem_full (ZMod ℓ) M hd)
  have hfix0 : rhoF (H := H) hℓM γ ⟨_, h0⟩ = ⟨_, h0⟩ := h5 γ ⟨_, h0⟩ (jqModCd_mem_full (ZMod ℓ) M hd)
  have hmemK : qExpand K d (jqModC K) ∈ qExpFunctionFieldC K (GammaH M H) := by
    have := coeffMap_mem (phiK ℓ K) (GammaH M H) h0
    rwa [coeffMap_qExpand, coeffMap_jqModC] at this
  have heq : (⟨_, hmemK⟩ : FbK M H K) = iota (phiK ℓ K) (GammaH M H) ⟨_, h0⟩ := by
    refine Subtype.ext ?_
    rw [coe_iota]
    change qExpand K d (jqModC K) = coeffMap (phiK ℓ K) (qExpand (ZMod ℓ) d (jqModC (ZMod ℓ)))
    rw [coeffMap_qExpand, coeffMap_jqModC]
  have hfixK : rhoK (H := H) K hℓM γ ⟨_, hmemK⟩ = ⟨_, hmemK⟩ := by
    rw [heq, rhoK_iota, hfix0]
  exact (mem_lift (⟨_, hmemK⟩ : FbK M H K)).mpr ((hE _).mpr hfixK)

theorem finite_range (hℓM : ¬ ℓ ∣ M) : Finite (rhoK (H := H) K hℓM).range := by

  have hker : (GammaH M H).subgroupOf (Gamma0 M) ≤ (rhoK (H := H) K hℓM).ker := by
    intro γ hγ
    rw [MonoidHom.mem_ker]
    exact rhoK_eq_one_of_mem hℓM γ (Subgroup.mem_subgroupOf.mp hγ)
  haveI : (GammaH M H).FiniteIndex := by
    refine @Subgroup.finiteIndex_of_le _ _ (Gamma1 M) _ ?_ (Gamma1_le_GammaH M H)
    infer_instance
  haveI : ((GammaH M H).subgroupOf (Gamma0 M)).FiniteIndex := by
    refine ⟨fun h0 => ?_⟩
    have := Subgroup.relIndex_mul_index (GammaH_le_Gamma0 (M := M) H)
    rw [Subgroup.relIndex, h0, zero_mul] at this
    exact Subgroup.FiniteIndex.index_ne_zero this.symm
  haveI : (rhoK (H := H) K hℓM).ker.FiniteIndex := Subgroup.finiteIndex_of_le hker
  have e := QuotientGroup.quotientKerEquivRange (rhoK (H := H) K hℓM)
  haveI : Finite (Gamma0 M ⧸ (rhoK (H := H) K hℓM).ker) := Subgroup.finite_quotient_of_finiteIndex
  exact Finite.of_equiv _ e.toEquiv

end DiamondK

section DoubleCosets

theorem finite_doubleCoset {G : Type*} [Group G] (N C : Subgroup G) [N.FiniteIndex] :
    Finite (DoubleCoset.Quotient (N : Set G) (C : Set G)) := by
  haveI : Finite (G ⧸ N) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Finite (Quotient (QuotientGroup.rightRel N)) :=
    Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel N).symm
  let f : Quotient (QuotientGroup.rightRel N) → DoubleCoset.Quotient (N : Set G) (C : Set G) :=
    Quotient.map' id (fun a b hab => by
      rw [QuotientGroup.rightRel_apply] at hab
      rw [DoubleCoset.rel_iff]
      exact ⟨b * a⁻¹, hab, 1, one_mem C, by simp⟩)
  refine Finite.of_surjective f ?_
  intro q
  induction q using Quotient.inductionOn' with
  | h g => exact ⟨Quotient.mk'' g, rfl⟩

variable {M : ℕ} (H : Subgroup (ZMod M)ˣ) (C : Subgroup SL(2, ℤ))

abbrev DCH : Type := DoubleCoset.Quotient (GammaH M H : Set SL(2, ℤ)) (C : Set SL(2, ℤ))

abbrev DC0 (M : ℕ) : Type := DoubleCoset.Quotient (Gamma0 M : Set SL(2, ℤ)) (C : Set SL(2, ℤ))

def dcSMul (γ : Gamma0 M) (q : DCH H C) : DCH H C :=
  Quotient.map' (fun g : SL(2, ℤ) => (γ : SL(2, ℤ)) * g) (fun a b hab => by
    rw [DoubleCoset.rel_iff] at hab ⊢
    obtain ⟨n, hn, c, hc, rfl⟩ := hab
    refine ⟨(γ : SL(2, ℤ)) * n * (γ : SL(2, ℤ))⁻¹, conj_mem_GammaH M H γ ⟨n, hn⟩, c, hc, by group⟩) q

scoped instance : MulAction (Gamma0 M) (DCH H C) where
  smul := dcSMul H C
  one_smul q := by
    induction q using Quotient.inductionOn' with
    | h g =>
      change Quotient.mk'' _ = Quotient.mk'' _
      simp
  mul_smul γ δ q := by
    induction q using Quotient.inductionOn' with
    | h g =>
      change Quotient.mk'' _ = Quotient.mk'' _
      simp [mul_assoc]

theorem smul_mk (γ : Gamma0 M) (g : SL(2, ℤ)) :
    γ • (DoubleCoset.mk (GammaH M H) C g : DCH H C) = DoubleCoset.mk (GammaH M H) C ((γ : SL(2, ℤ)) * g) :=
  rfl

def proj (q : DCH H C) : DC0 C M :=
  Quotient.map' id (fun a b hab => by
    rw [DoubleCoset.rel_iff] at hab ⊢
    obtain ⟨n, hn, c, hc, rfl⟩ := hab
    exact ⟨n, GammaH_le_Gamma0 H hn, c, hc, rfl⟩) q

theorem proj_mk (g : SL(2, ℤ)) :
    proj H C (DoubleCoset.mk (GammaH M H) C g) = DoubleCoset.mk (Gamma0 M) C g := rfl

theorem proj_smul (γ : Gamma0 M) (q : DCH H C) : proj H C (γ • q) = proj H C q := by
  induction q using Quotient.inductionOn' with
  | h g =>
    change DoubleCoset.mk (Gamma0 M) C ((γ : SL(2, ℤ)) * g) = DoubleCoset.mk (Gamma0 M) C g
    rw [DoubleCoset.eq]
    exact ⟨(γ : SL(2, ℤ))⁻¹, inv_mem γ.2, 1, one_mem C, by group⟩

theorem proj_eq_iff (q q' : DCH H C) : proj H C q' = proj H C q ↔ ∃ γ : Gamma0 M, γ • q = q' := by
  constructor
  · induction q using Quotient.inductionOn' with
    | h g =>
      induction q' using Quotient.inductionOn' with
      | h g' =>
        intro h
        change DoubleCoset.mk (Gamma0 M) C g' = DoubleCoset.mk (Gamma0 M) C g at h
        rw [DoubleCoset.eq] at h
        obtain ⟨γ, hγ, c, hc, rfl⟩ := h
        refine ⟨⟨γ⁻¹, inv_mem hγ⟩, ?_⟩
        change DoubleCoset.mk (GammaH M H) C (γ⁻¹ * (γ * g' * c)) = DoubleCoset.mk (GammaH M H) C g'
        rw [DoubleCoset.eq]
        exact ⟨1, one_mem _, c⁻¹, inv_mem hc, by group⟩
  · rintro ⟨γ, rfl⟩
    exact proj_smul H C γ q

theorem exists_of_mem_stabilizer (g : SL(2, ℤ)) (γ : Gamma0 M)
    (hγ : γ ∈ MulAction.stabilizer (Gamma0 M) (DoubleCoset.mk (GammaH M H) C g : DCH H C)) :
    ∃ h : Gamma0 M, (h : SL(2, ℤ)) ∈ GammaH M H ∧
      g⁻¹ * ((h * γ : Gamma0 M) : SL(2, ℤ)) * g ∈ C := by
  rw [MulAction.mem_stabilizer_iff, smul_mk, DoubleCoset.eq] at hγ
  obtain ⟨n, hn, c, hc, h⟩ := hγ

  refine ⟨⟨n, GammaH_le_Gamma0 H hn⟩, hn, ?_⟩
  have : g⁻¹ * (n * (γ : SL(2, ℤ))) * g = c⁻¹ := by
    have h' : n * ((γ : SL(2, ℤ)) * g) * c = g := h.symm
    calc g⁻¹ * (n * (γ : SL(2, ℤ))) * g
        = g⁻¹ * (n * ((γ : SL(2, ℤ)) * g) * c) * c⁻¹ := by group
      _ = c⁻¹ := by rw [h']; group
  change g⁻¹ * (n * (γ : SL(2, ℤ))) * g ∈ C
  rw [this]
  exact inv_mem hc

theorem subgroupOf_le_stabilizer (q : DCH H C) :
    (GammaH M H).subgroupOf (Gamma0 M) ≤ MulAction.stabilizer (Gamma0 M) q := by
  intro γ hγ
  rw [Subgroup.mem_subgroupOf] at hγ
  rw [MulAction.mem_stabilizer_iff]
  induction q using Quotient.inductionOn' with
  | h g =>
    change DoubleCoset.mk (GammaH M H) C ((γ : SL(2, ℤ)) * g) = DoubleCoset.mk (GammaH M H) C g
    rw [DoubleCoset.eq]
    exact ⟨(γ : SL(2, ℤ))⁻¹, inv_mem hγ, 1, one_mem C, by group⟩

variable [NeZero M]

scoped instance : (GammaH M H).FiniteIndex := by
  refine @Subgroup.finiteIndex_of_le _ _ (Gamma1 M) _ ?_ (Gamma1_le_GammaH M H)
  infer_instance

scoped instance : ((GammaH M H).subgroupOf (Gamma0 M)).FiniteIndex := by
  refine ⟨fun h0 => ?_⟩
  have := Subgroup.relIndex_mul_index (GammaH_le_Gamma0 (M := M) H)
  rw [Subgroup.relIndex, h0, zero_mul] at this
  exact Subgroup.FiniteIndex.index_ne_zero this.symm

scoped instance : Finite (DCH H C) := finite_doubleCoset _ _
scoped instance : Finite (DC0 C M) := finite_doubleCoset _ _

noncomputable scoped instance : Fintype (DCH H C) := Fintype.ofFinite _
noncomputable scoped instance : Fintype (DC0 C M) := Fintype.ofFinite _

open Classical in

def fib (y : DC0 C M) : Finset (DCH H C) := Finset.univ.filter fun q => proj H C q = y

open Classical in
theorem coe_fib_proj (q : DCH H C) :
    ((fib H C (proj H C q) : Finset (DCH H C)) : Set (DCH H C)) = MulAction.orbit (Gamma0 M) q := by
  ext q'
  rw [fib, Finset.coe_filter, Set.mem_setOf_eq, MulAction.mem_orbit_iff]
  simp only [Finset.mem_univ, true_and]
  exact proj_eq_iff H C q q'

open Classical in

theorem card_fib_mk (g : SL(2, ℤ)) :
    (fib H C (DoubleCoset.mk (Gamma0 M) C g)).card =
      (MulAction.stabilizer (Gamma0 M) (DoubleCoset.mk (GammaH M H) C g : DCH H C)).index := by
  rw [MulAction.index_stabilizer, ← coe_fib_proj, Set.ncard_coe_finset, proj_mk]

open Classical in

theorem sum_card_fib :
    ∑ y : DC0 C M, (fib H C y).card = Nat.card (DCH H C) := by
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  symm
  exact Finset.card_eq_sum_card_fiberwise (f := proj H C) (s := Finset.univ) (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))

theorem index_stabilizer_ne_zero (q : DCH H C) :
    (MulAction.stabilizer (Gamma0 M) q).index ≠ 0 :=
  (Subgroup.finiteIndex_of_le (subgroupOf_le_stabilizer H C q)).index_ne_zero

end DoubleCosets

section Engine

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {ℓ : ℕ} [Fact ℓ.Prime]
  {K : Type*} [Field K] [CharP K ℓ] [IsAlgClosed K]

variable (M K) in

abbrev FullK : Type _ := ↥(modularFunctionFieldFullC K M)

variable (M K) in

def jFull : FullK M K := ⟨jqModC K, jqModC_mem_full K M⟩

def incl (hℓM : ¬ ℓ ∣ M) : FullK M K →ₐ[K] FbK M H K := IntermediateField.inclusion (full_le (H := H) hℓM)

@[scoped simp] theorem coe_incl (hℓM : ¬ ℓ ∣ M) (u : FullK M K) :
    ((incl (H := H) hℓM u : FbK M H K) : LaurentSeries K) = u :=
  IntermediateField.coe_inclusion (full_le (H := H) hℓM) u

theorem rho_incl (hℓM : ¬ ℓ ∣ M) (γ : Gamma0 M) (u : FullK M K) :
    rhoK (H := H) K hℓM γ (incl hℓM u) = incl hℓM u :=
  rhoK_apply_eq_self_of_mem_full hℓM γ _ (by rw [coe_incl]; exact u.2)

def Gr (hℓM : ¬ ℓ ∣ M) : Subgroup (FbK M H K ≃ₐ[K] FbK M H K) := (rhoK (H := H) K hℓM).range

theorem finite_Gr (hℓM : ¬ ℓ ∣ M) : Finite (Gr (H := H) (K := K) hℓM) := finite_range hℓM

def Fix (hℓM : ¬ ℓ ∣ M) : Subfield (FbK M H K) := FixedPoints.subfield (Gr (H := H) (K := K) hℓM) (FbK M H K)

theorem mem_Fix_iff (hℓM : ¬ ℓ ∣ M) (u : FbK M H K) :
    u ∈ Fix (H := H) hℓM ↔ ∀ γ : Gamma0 M, rhoK (H := H) K hℓM γ u = u := by
  change (∀ g : Gr (H := H) (K := K) hℓM, g • u = u) ↔ _
  constructor
  · intro h γ
    exact h ⟨rhoK (H := H) K hℓM γ, γ, rfl⟩
  · rintro h ⟨g, γ, rfl⟩
    exact h γ

theorem coe_mem_full_of_mem_Fix (hℓM : ¬ ℓ ∣ M) (u : FbK M H K) (hu : u ∈ Fix (H := H) hℓM) :
    (u : LaurentSeries K) ∈ modularFunctionFieldFullC K M :=
  ModularCurve.coe_mem_modularFunctionFieldFullC_of_forall_diamondPullbackModL_apply_eq M H hℓM K
    (rhoK (H := H) K hℓM) (rhoK_pullback hℓM) (fun γ x hx => rhoK_apply_eq_self_of_mem_full hℓM γ x hx)
    u ((mem_Fix_iff hℓM u).mp hu)

def valFix (hℓM : ¬ ℓ ∣ M) : Fix (H := H) (K := K) hℓM →+* LaurentSeries K :=
  ((qExpFunctionFieldC K (GammaH M H)).toSubfield.subtype).comp (Fix (H := H) hℓM).subtype

theorem valFix_apply (hℓM : ¬ ℓ ∣ M) (u : Fix (H := H) (K := K) hℓM) :
    valFix hℓM u = ((u : FbK M H K) : LaurentSeries K) := rfl

def psi (hℓM : ¬ ℓ ∣ M) : Fix (H := H) (K := K) hℓM →+* FullK M K :=
  (valFix hℓM).codRestrict (modularFunctionFieldFullC K M) fun u =>
    coe_mem_full_of_mem_Fix hℓM (u : FbK M H K) u.2

theorem coe_psi (hℓM : ¬ ℓ ∣ M) (u : Fix (H := H) (K := K) hℓM) :
    ((psi hℓM u : FullK M K) : LaurentSeries K) = ((u : FbK M H K) : LaurentSeries K) :=
  RingHom.codRestrict_apply _ _ _ u

theorem incl_psi (hℓM : ¬ ℓ ∣ M) (u : Fix (H := H) (K := K) hℓM) :
    incl (H := H) hℓM (psi hℓM u) = (u : FbK M H K) :=
  Subtype.ext (by rw [coe_incl, coe_psi])

theorem incl_isIntegral (hℓM : ¬ ℓ ∣ M) : (incl (H := H) (K := K) hℓM).toRingHom.IsIntegral := by
  intro u
  haveI := finite_Gr (H := H) (K := K) hℓM
  have hint : IsIntegral (Fix (H := H) hℓM) u :=
    FixedPoints.isIntegral (Gr (H := H) (K := K) hℓM) (FbK M H K) u
  obtain ⟨p, hp, hpu⟩ := hint
  refine ⟨p.map (psi hℓM), hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have : (incl (H := H) (K := K) hℓM).toRingHom.comp (psi hℓM) =
      algebraMap (Fix (H := H) hℓM) (FbK M H K) := by
    ext u : 1
    exact incl_psi hℓM u
  rw [this]
  exact hpu

def restr (hℓM : ¬ ℓ ∣ M) (Q : Place K (FbK M H K)) : Place K (FullK M K) :=
  Q.restrictAlong (incl (H := H) hℓM) (incl_isIntegral hℓM)

theorem restr_toValuationSubring (hℓM : ¬ ℓ ∣ M) (Q : Place K (FbK M H K)) :
    (restr (H := H) hℓM Q).toValuationSubring =
      Q.toValuationSubring.comap (IntermediateField.inclusion (full_le (H := H) hℓM)).toRingHom := by
  letI := algebraAlong (incl (H := H) (K := K) hℓM)
  rfl

theorem mem_restr_iff (hℓM : ¬ ℓ ∣ M) (Q : Place K (FbK M H K)) (u : FullK M K) :
    u ∈ (restr (H := H) hℓM Q).toValuationSubring ↔ incl (H := H) hℓM u ∈ Q.toValuationSubring := by
  rw [restr_toValuationSubring, ValuationSubring.mem_comap]
  rfl

theorem ord_incl (hℓM : ¬ ℓ ∣ M) (Q : Place K (FbK M H K)) (u : FullK M K) :
    Q.ord (incl (H := H) hℓM u) =
      Place.ramificationIndexAlong (incl (H := H) hℓM) Q * (restr (H := H) hℓM Q).ord u :=
  Place.ord_restrictAlong _ _ Q u

theorem ramificationIndexAlong_pos (hℓM : ¬ ℓ ∣ M) (Q : Place K (FbK M H K)) :
    0 < Place.ramificationIndexAlong (incl (H := H) hℓM) Q := by
  letI := algebraAlong (incl (H := H) (K := K) hℓM)
  haveI := isScalarTower_along (incl (H := H) (K := K) hℓM)
  haveI := isIntegral_along (incl (H := H) (K := K) hℓM) (incl_isIntegral hℓM)
  exact Q.ramificationIndex_pos (F := FullK M K)

theorem restr_smul (hℓM : ¬ ℓ ∣ M) (γ : Gamma0 M) (Q : Place K (FbK M H K)) :
    restr (H := H) hℓM (rhoK (H := H) K hℓM γ • Q) = restr hℓM Q := by
  apply Place.ext
  ext u
  rw [mem_restr_iff, mem_restr_iff, Place.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← map_inv, rho_incl]

theorem ord_smul_of_apply_eq (σ : FbK M H K ≃ₐ[K] FbK M H K) (Q : Place K (FbK M H K)) (x : FbK M H K)
    (hx : σ x = x) : (σ • Q).ord x = Q.ord x := by
  conv_lhs => rw [← hx]
  exact Place.ord_smul σ Q x

theorem ofAlgAut_smul_place (τ : FbK M H K ≃ₐ[K] FbK M H K) (Q : Place K (FbK M H K)) :
    SemilinearAut.ofAlgAut τ • Q = τ • Q := by
  apply Place.ext
  ext u
  rw [SemilinearAut.smul_toValuationSubring, Place.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, SemilinearAut.ofAlgAut_smul,
    AlgEquiv.smul_def]

set_option maxHeartbeats 3200000 in

theorem exists_smul_eq_of_restr_eq (hℓM : ¬ ℓ ∣ M) (Q Q' : Place K (FbK M H K))
    (h : restr (H := H) hℓM Q = restr hℓM Q') :
    ∃ γ : Gamma0 M, rhoK (H := H) K hℓM γ • Q = Q' := by
  haveI := finite_Gr (H := H) (K := K) hℓM

  letI : Algebra K (Fix (H := H) (K := K) hℓM) :=
    ((algebraMap K (FbK M H K)).codRestrict (Fix (H := H) hℓM) fun c => by
      rw [mem_Fix_iff]
      intro γ
      exact (rhoK (H := H) K hℓM γ).commutes c).toAlgebra
  haveI : IsScalarTower K (Fix (H := H) (K := K) hℓM) (FbK M H K) :=
    IsScalarTower.of_algebraMap_eq fun c => rfl
  haveI : IsGalois (Fix (H := H) (K := K) hℓM) (FbK M H K) :=
    IsGalois.of_fixed_field (FbK M H K) (Gr (H := H) (K := K) hℓM)

  have key : ∀ (R : Place K (FbK M H K)) (u : Fix (H := H) (K := K) hℓM),
      u ∈ (R.restrict (Fix (H := H) (K := K) hℓM)).toValuationSubring ↔
        psi hℓM u ∈ (restr (H := H) hℓM R).toValuationSubring := by
    intro R u
    rw [Place.mem_restrict_iff, mem_restr_iff, incl_psi]
    rfl
  haveI : FiniteDimensional (Fix (H := H) (K := K) hℓM) (FbK M H K) :=
    show FiniteDimensional (FixedPoints.subfield (Gr (H := H) (K := K) hℓM) (FbK M H K)) (FbK M H K) from
      inferInstance
  have hF : Q'.restrict (Fix (H := H) (K := K) hℓM) = Q.restrict (Fix (H := H) (K := K) hℓM) := by
    apply Place.ext
    ext u
    rw [key, key, h]
  obtain ⟨σ, hσ⟩ := AlgebraicCurve.Place.exists_algEquiv_smul_eq_of_restrict_eq (K := K)
    (F' := Fix (H := H) (K := K) hℓM) (M := FbK M H K) Q Q' hF

  obtain ⟨g, hg⟩ := FixedPoints.toAlgAut_surjective (Gr (H := H) (K := K) hℓM) (FbK M H K) σ
  obtain ⟨γ, hγ⟩ := g.2
  refine ⟨γ, ?_⟩
  have hres : σ.restrictScalars K = rhoK (H := H) K hℓM γ := by
    refine AlgEquiv.ext fun x => ?_
    rw [AlgEquiv.restrictScalars_apply, ← hg, MulSemiringAction.toAlgAut_apply, hγ]
    rfl
  rw [← hres, ← ofAlgAut_smul_place]
  exact hσ

open Classical in

theorem card_le_natCard (hℓM : ¬ ℓ ∣ M) (C : Subgroup SL(2, ℤ)) (p : Place K (FullK M K) → Prop)
    (S : Finset (Place K (FbK M H K)))
    (hstab : ∀ (γ : Gamma0 M) (Q : Place K (FbK M H K)), Q ∈ S → rhoK (H := H) K hℓM γ • Q ∈ S)
    (hSP : ∀ Q ∈ S, p (restr (H := H) hℓM Q))
    (ι : {P : Place K (FullK M K) // p P} → DC0 C M) (hι : Function.Injective ι)
    (hdec : ∀ (P : {P : Place K (FullK M K) // p P}) (g : SL(2, ℤ)),
      ι P = DoubleCoset.mk (Gamma0 M) C g →
      ∀ γ : Gamma0 M, g⁻¹ * (γ : SL(2, ℤ)) * g ∈ C →
      ∀ Q : Place K (FbK M H K), restr (H := H) hℓM Q = P.1 → rhoK (H := H) K hℓM γ • Q = Q) :
    S.card ≤ Nat.card (DCH H C) := by

  letI : MulAction (Gamma0 M) (Place K (FbK M H K)) := MulAction.compHom _ (rhoK (H := H) K hℓM)
  have hsmul : ∀ (γ : Gamma0 M) (Q : Place K (FbK M H K)), γ • Q = rhoK (H := H) K hℓM γ • Q :=
    fun _ _ => rfl

  set T₀ : Finset (Place K (FullK M K)) := S.image (restr (H := H) hℓM) with hT₀

  let ι' : Place K (FullK M K) → DC0 C M := fun P =>
    if h : p P then ι ⟨P, h⟩ else DoubleCoset.mk (Gamma0 M) C 1
  have hι' : ∀ P (h : p P), ι' P = ι ⟨P, h⟩ := fun P h => dif_pos h
  have hpT : ∀ P ∈ T₀, p P := by
    intro P hP
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
    exact hSP Q hQ

  have h1 : S.card = ∑ P ∈ T₀, (S.filter fun Q => restr (H := H) hℓM Q = P).card :=
    Finset.card_eq_sum_card_image _ _

  have h2 : ∀ P ∈ T₀, (S.filter fun Q => restr (H := H) hℓM Q = P).card ≤ (fib H C (ι' P)).card := by
    intro P hP
    obtain ⟨Q₀, hQ₀, rfl⟩ := Finset.mem_image.mp hP
    have hp0 : p (restr (H := H) hℓM Q₀) := hSP Q₀ hQ₀

    have horb : ((S.filter fun Q => restr (H := H) hℓM Q = restr hℓM Q₀ : Finset _) :
          Set (Place K (FbK M H K))) = MulAction.orbit (Gamma0 M) Q₀ := by
      ext Q
      rw [Finset.coe_filter, Set.mem_setOf_eq, MulAction.mem_orbit_iff]
      constructor
      · rintro ⟨-, hQ⟩
        obtain ⟨γ, hγ⟩ := exists_smul_eq_of_restr_eq hℓM Q₀ Q hQ.symm
        exact ⟨γ, hγ⟩
      · rintro ⟨γ, rfl⟩
        exact ⟨hstab γ Q₀ hQ₀, restr_smul hℓM γ Q₀⟩
    have hcard : (S.filter fun Q => restr (H := H) hℓM Q = restr hℓM Q₀).card =
        (MulAction.stabilizer (Gamma0 M) Q₀).index := by
      rw [MulAction.index_stabilizer, ← horb, Set.ncard_coe_finset]

    obtain ⟨g, hg⟩ : ∃ g : SL(2, ℤ), ι ⟨_, hp0⟩ = DoubleCoset.mk (Gamma0 M) C g := by
      induction h : ι ⟨_, hp0⟩ using Quotient.inductionOn' with
      | h g => exact ⟨g, rfl⟩
    rw [hcard, hι' _ hp0, hg, card_fib_mk]

    have hle : MulAction.stabilizer (Gamma0 M) (DoubleCoset.mk (GammaH M H) C g : DCH H C) ≤
        MulAction.stabilizer (Gamma0 M) Q₀ := by
      intro γ hγ
      obtain ⟨h, hh, hs⟩ := exists_of_mem_stabilizer H C g γ hγ
      rw [MulAction.mem_stabilizer_iff, hsmul]
      have hγeq : γ = h⁻¹ * (h * γ) := by group
      have hfix : rhoK (H := H) K hℓM (h * γ) • Q₀ = Q₀ := hdec ⟨_, hp0⟩ g hg (h * γ) hs Q₀ rfl
      have hh1 : rhoK (H := H) K hℓM h⁻¹ = 1 := by
        rw [map_inv, rhoK_eq_one_of_mem hℓM h hh, inv_one]
      rw [hγeq, map_mul, hh1, one_mul, hfix]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero (index_stabilizer_ne_zero H C _)) (Subgroup.index_dvd_of_le hle)

  calc S.card = ∑ P ∈ T₀, (S.filter fun Q => restr (H := H) hℓM Q = P).card := h1
    _ ≤ ∑ P ∈ T₀, (fib H C (ι' P)).card := Finset.sum_le_sum h2
    _ = ∑ y ∈ T₀.image ι', (fib H C y).card := by
        symm
        refine Finset.sum_image (s := T₀) (g := ι') (f := fun y => (fib H C y).card) ?_
        intro P hP P' hP' hPP'
        rw [hι' P (hpT P hP), hι' P' (hpT P' hP')] at hPP'
        exact congrArg Subtype.val (hι hPP')
    _ ≤ ∑ y : DC0 C M, (fib H C y).card :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
    _ = Nat.card (DCH H C) := sum_card_fib H C

end Engine

section Main

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime]
  (K : Type*) [Field K] [IsAlgClosed K] [CharP K ℓ]

set_option maxHeartbeats 3200000 in
theorem main (hℓM : ¬ ℓ ∣ M)
    (x : qExpFunctionFieldC K (GammaH M H)) (hx : (x : LaurentSeries K) = jqModC K)
    (S₀ S₁ Sinf : Finset (Place K (qExpFunctionFieldC K (GammaH M H))))
    (hS₀ : ∀ Q, Q ∈ S₀ ↔ 0 < Q.ord x) (hS₁ : ∀ Q, Q ∈ S₁ ↔ 0 < Q.ord (x - 1728))
    (hSinf : ∀ Q, Q ∈ Sinf ↔ Q.ord x < 0) :
    S₀.card ≤ Nat.card (DoubleCoset.Quotient (GammaH M H : Set SL(2, ℤ))
        (Subgroup.zpowers (ModularGroup.S * ModularGroup.T) : Set SL(2, ℤ))) ∧
      S₁.card ≤ Nat.card (DoubleCoset.Quotient (GammaH M H : Set SL(2, ℤ))
        (Subgroup.zpowers ModularGroup.S : Set SL(2, ℤ))) ∧
      Sinf.card ≤ Nat.card (DoubleCoset.Quotient (GammaH M H : Set SL(2, ℤ))
        ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) :
          Set SL(2, ℤ))) := by

  have hxj : x = incl (H := H) hℓM (jFull M K) := Subtype.ext hx
  have hxfix : ∀ γ : Gamma0 M, rhoK (H := H) K hℓM γ x = x := fun γ => by
    rw [hxj]; exact rho_incl hℓM γ _
  have h1728 : (1728 : FbK M H K) = incl (H := H) hℓM (algebraMap K (FullK M K) 1728) := by
    rw [AlgHom.commutes]
    exact (map_ofNat (algebraMap K (FbK M H K)) 1728).symm
  have hxc : x - 1728 = incl (H := H) hℓM (jFull M K - algebraMap K (FullK M K) 1728) := by
    rw [map_sub, ← hxj, ← h1728]
  have hcfix : ∀ γ : Gamma0 M, rhoK (H := H) K hℓM γ (x - 1728) = x - 1728 := fun γ => by
    rw [hxc]; exact rho_incl hℓM γ _

  have hordx : ∀ Q : Place K (FbK M H K),
      Q.ord x = (Place.ramificationIndexAlong (incl (H := H) hℓM) Q : ℤ) *
        (restr (H := H) hℓM Q).ord (jFull M K) := by
    intro Q
    rw [hxj, ord_incl]
  have hordc : ∀ Q : Place K (FbK M H K),
      Q.ord (x - 1728) = (Place.ramificationIndexAlong (incl (H := H) hℓM) Q : ℤ) *
        (restr (H := H) hℓM Q).ord (jFull M K - algebraMap K (FullK M K) 1728) := by
    intro Q
    rw [hxc, ord_incl]
  have hepos : ∀ Q : Place K (FbK M H K),
      (0 : ℤ) < Place.ramificationIndexAlong (incl (H := H) hℓM) Q := fun Q => by
    exact_mod_cast ramificationIndexAlong_pos (H := H) (K := K) hℓM Q

  obtain ⟨⟨ι₀, hι₀, hdec₀⟩, ⟨ι₁, hι₁, hdec₁⟩⟩ :=
    ModularCurve.exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_pos M H hℓM K
      (rhoK (H := H) K hℓM) (rhoK_pullback hℓM) (full_le (H := H) hℓM)
      (fun γ x hx => rhoK_apply_eq_self_of_mem_full hℓM γ x hx)
  obtain ⟨ιi, hιi, hdeci⟩ :=
    ModularCurve.exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_neg M H hℓM K
      (rhoK (H := H) K hℓM) (rhoK_pullback hℓM) (full_le (H := H) hℓM)
      (fun γ x hx => rhoK_apply_eq_self_of_mem_full hℓM γ x hx)
  refine ⟨?_, ?_, ?_⟩
  · refine card_le_natCard hℓM (Subgroup.zpowers (ModularGroup.S * ModularGroup.T))
      (fun P => 0 < P.ord (jFull M K)) S₀ ?_ ?_ ι₀ hι₀ ?_
    · intro γ Q hQ
      rw [hS₀] at hQ ⊢
      rwa [ord_smul_of_apply_eq _ Q x (hxfix γ)]
    · intro Q hQ
      rw [hS₀, hordx] at hQ
      exact pos_of_mul_pos_right hQ (hepos Q).le
    · intro P g hg γ hγ Q hQ
      exact hdec₀ P g hg γ hγ Q (by rw [← restr_toValuationSubring hℓM, hQ])
  · refine card_le_natCard hℓM (Subgroup.zpowers ModularGroup.S)
      (fun P => 0 < P.ord (jFull M K - algebraMap K (FullK M K) 1728)) S₁ ?_ ?_ ι₁ hι₁ ?_
    · intro γ Q hQ
      rw [hS₁] at hQ ⊢
      rwa [ord_smul_of_apply_eq _ Q (x - 1728) (hcfix γ)]
    · intro Q hQ
      rw [hS₁, hordc] at hQ
      exact pos_of_mul_pos_right hQ (hepos Q).le
    · intro P g hg γ hγ Q hQ
      exact hdec₁ P g hg γ hγ Q (by rw [← restr_toValuationSubring hℓM, hQ])
  · refine card_le_natCard hℓM (Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1))
      (fun P => P.ord (jFull M K) < 0) Sinf ?_ ?_ ιi hιi ?_
    · intro γ Q hQ
      rw [hSinf] at hQ ⊢
      rwa [ord_smul_of_apply_eq _ Q x (hxfix γ)]
    · intro Q hQ
      rw [hSinf, hordx] at hQ
      exact neg_of_mul_neg_right hQ (hepos Q).le
    · intro P g hg γ hγ Q hQ
      exact hdeci P g hg γ hγ Q (by rw [← restr_toValuationSubring hℓM, hQ])

end Main

end XHFibreCount
p2m_reactivate "P2MW.S_ModularCurve_card_fibres_jqModC_qExpFunctionFieldC_gammaH_le_natCard_doubleCoset.XHFibreCount"

open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K ℓ]
    (x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H))
    (hx : (x : LaurentSeries K) = ModularCurve.jqModC K)
    (S₀ S₁ Sinf : Finset (AlgebraicCurve.Place K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H))))
    (hS₀ : ∀ Q, Q ∈ S₀ ↔ 0 < Q.ord x) (hS₁ : ∀ Q, Q ∈ S₁ ↔ 0 < Q.ord (x - 1728))
    (hSinf : ∀ Q, Q ∈ Sinf ↔ Q.ord x < 0) :
    S₀.card ≤ Nat.card (DoubleCoset.Quotient
        (CohCarrier.GammaH M H : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
        (Subgroup.zpowers (ModularGroup.S * ModularGroup.T) :
          Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))) ∧
      S₁.card ≤ Nat.card (DoubleCoset.Quotient
        (CohCarrier.GammaH M H : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
        (Subgroup.zpowers ModularGroup.S : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))) ∧
      Sinf.card ≤ Nat.card (DoubleCoset.Quotient
        (CohCarrier.GammaH M H : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
        ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) :
            Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
          Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))) :=
  XHFibreCount.main M H K hℓM x hx S₀ S₁ Sinf hS₀ hS₁ hSinf

end
end S_ModularCurve_card_fibres_jqModC_qExpFunctionFieldC_gammaH_le_natCard_doubleCoset
end P2MW
export P2MW.S_ModularCurve_card_fibres_jqModC_qExpFunctionFieldC_gammaH_le_natCard_doubleCoset (solution)
