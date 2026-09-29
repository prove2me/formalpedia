-- Prove2me | solution 1 for ModPForms.mem_modPMod_sub_of_qP_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/6f25d2cb-0749-53dc-bc7d-891acdf693f2

import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_SwdAlgebra
import Definitions.Def_ModularCurve_ModPFormFn
import Theorems.Thm_ModPForms_exists_isModPFormFn_qexpOfWeight_eq_of_mem_modPMod
import Theorems.Thm_ModPForms_exists_mem_modPMod_ofPowerSeries_eq_qexpOfWeight_of_isModPFormFn
import Theorems.Thm_ModularCurve_stackOrd_nonneg_and_le_ord_of_isModPFormFn
import Theorems.Thm_ModularCurve_isModPFormFn_of_forall_stackOrd_nonneg_of_forall_le_ord
import Theorems.Thm_ModularCurve_exists_coe_eq_thetaL_jqModC_zpow_and_stackOrd_eq
import Theorems.Thm_ModularCurve_exists_coe_eq_qP_mul_thetaL_jqModC_zpow_and_stackOrd_eq_zero
import Theorems.Thm_ModularCurve_eq_zero_of_forall_stackOrd_nonneg_of_forall_le_ord_of_neg
import Theorems.Thm_ModPForms_modPMod_eq_bot_of_odd
import Theorems.Thm_ModPForms_modPMod_eq_bot_of_neg
import Theorems.Thm_ModPForms_modPMod_eq_span_map_modPMod_zmod
import Theorems.Thm_ModPForms_mem_modPMod_of_mul_mem_of_forall_zmod
import Theorems.Thm_ModularCurve_thetaL_jqNModC_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModPForms_mem_modPMod_sub_of_qP_mul_mem
p2m_attr_erase "instance" "ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instIsElliptic_tateBase"
p2m_attr_erase "simp" "ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.qExpandAlgHomC_apply ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero"
p2m_attr_erase "simp" "ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.cuspCount_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero"
p2m_attr_erase "simp" "TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply"

set_option autoImplicit false
set_option maxHeartbeats 3200000

open AlgebraicCurve ModularCurve

namespace FltWs24
namespace Dbfcd913

section Coordinates
variable (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [CharP F p]

noncomputable abbrev ι : PowerSeries (ZMod p) →+* PowerSeries F :=
  PowerSeries.map (ZMod.castHom (dvd_refl p) F)

noncomputable def coordPS (lam : F →+ ZMod p) : PowerSeries F →+ PowerSeries (ZMod p) where
  toFun φ := PowerSeries.mk fun n => lam (PowerSeries.coeff n φ)
  map_zero' := by ext n; simp
  map_add' φ ψ := by ext n; simp

theorem coeff_coordPS (lam : F →+ ZMod p) (φ : PowerSeries F) (n : ℕ) :
    PowerSeries.coeff n (coordPS p F lam φ) = lam (PowerSeries.coeff n φ) := by
  simp [coordPS, PowerSeries.coeff_mk]

theorem coordPS_smul_ι (lam : F →+ ZMod p)
    (hlam : ∀ (t : ZMod p) (c : F), lam ((ZMod.castHom (dvd_refl p) F t) * c) = t * lam c)
    (c : F) (s : PowerSeries (ZMod p)) :
    coordPS p F lam (c • ι p F s) = lam c • s := by
  ext n
  rw [coeff_coordPS, PowerSeries.coeff_smul, PowerSeries.coeff_smul, PowerSeries.coeff_map, smul_eq_mul,
    smul_eq_mul, mul_comm c, hlam, mul_comm]

theorem coordPS_mem_of_mem_span_image (lam : F →+ ZMod p)
    (hlam : ∀ (t : ZMod p) (c : F), lam ((ZMod.castHom (dvd_refl p) F t) * c) = t * lam c)
    (S : Submodule (ZMod p) (PowerSeries (ZMod p))) (φ : PowerSeries F)
    (hφ : φ ∈ Submodule.span F (ι p F '' (S : Set (PowerSeries (ZMod p))))) :
    coordPS p F lam φ ∈ S := by
  suffices h : ∀ c : F, coordPS p F lam (c • φ) ∈ S by simpa using h 1
  induction hφ using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨s, hs, rfl⟩ := hy
    intro c
    rw [coordPS_smul_ι p F lam hlam]
    exact S.smul_mem _ hs
  | zero => intro c; rw [smul_zero, map_zero]; exact S.zero_mem
  | add y z _ _ hy hz => intro c; rw [smul_add, map_add]; exact S.add_mem (hy c) (hz c)
  | smul c' y _ hy => intro c; rw [smul_smul]; exact hy (c * c')

theorem exists_coord_family :
    ∃ (B : Type) (lam : B → (F →+ ZMod p)),
      (∀ b (t : ZMod p) (c : F), lam b ((ZMod.castHom (dvd_refl p) F t) * c) = t * lam b c) ∧
      (∀ c : F, (∀ b, lam b c = 0) → c = 0) := by
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  let bs := Module.Free.chooseBasis (ZMod p) F
  refine ⟨Module.Free.ChooseBasisIndex (ZMod p) F, fun b => (bs.coord b).toAddMonoidHom, ?_, ?_⟩
  · intro b t c
    show bs.coord b (algebraMap (ZMod p) F t * c) = t * bs.coord b c
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  · intro c hc
    exact bs.forall_coord_eq_zero_iff.mp hc

end Coordinates

theorem map_qP_zmod (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [CharP F p] :
    PowerSeries.map (ZMod.castHom (dvd_refl p) F) (SwdAlgebra.qP (ZMod p)) = SwdAlgebra.qP F := by

  ext n
  simp only [SwdAlgebra.qP, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  rw [eq_intCast, eq_intCast, map_intCast]

theorem mem_of_map_mem_span_image (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p]
    (T : Submodule (ZMod p) (PowerSeries (ZMod p))) (ψ : PowerSeries (ZMod p))
    (h : PowerSeries.map (ZMod.castHom (dvd_refl p) K) ψ ∈
      Submodule.span K (PowerSeries.map (ZMod.castHom (dvd_refl p) K) '' (T : Set (PowerSeries (ZMod p))))) :
    ψ ∈ T := by
  obtain ⟨B, lam, hlam, hdet⟩ := exists_coord_family p K

  have h1 : ∃ b, lam b 1 ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact one_ne_zero (hdet 1 hall)
  obtain ⟨b, hb⟩ := h1
  have hmem := coordPS_mem_of_mem_span_image p K (lam b) (hlam b) T _ h
  have hid : coordPS p K (lam b) (PowerSeries.map (ZMod.castHom (dvd_refl p) K) ψ) = lam b 1 • ψ := by
    have : PowerSeries.map (ZMod.castHom (dvd_refl p) K) ψ = (1 : K) • ι p K ψ := (one_smul _ _).symm
    rw [this, coordPS_smul_ι p K (lam b) (hlam b)]
  rw [hid] at hmem
  have := T.smul_mem (lam b 1)⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ hb, one_smul] at this

theorem map_mem_modPMod (p : ℕ) [Fact p.Prime] (N : ℕ) (k : ℤ) (K : Type) [Field K] [CharP K p]
    (ψ : PowerSeries (ZMod p)) (hψ : ψ ∈ ModPForms.modPMod N k (ZMod p)) :
    PowerSeries.map (ZMod.castHom (dvd_refl p) K) ψ ∈ ModPForms.modPMod N k K := by
  rw [ModPForms.modPMod_eq_span_map_modPMod_zmod p N k K]
  exact Submodule.subset_span ⟨ψ, hψ, rfl⟩

theorem mem_modPMod_zmod_of_map_mem (p : ℕ) [Fact p.Prime] (N : ℕ) (k : ℤ) (K : Type) [Field K] [CharP K p]
    (ψ : PowerSeries (ZMod p)) (h : PowerSeries.map (ZMod.castHom (dvd_refl p) K) ψ ∈ ModPForms.modPMod N k K) :
    ψ ∈ ModPForms.modPMod N k (ZMod p) := by
  rw [ModPForms.modPMod_eq_span_map_modPMod_zmod p N k K] at h
  exact mem_of_map_mem_span_image p K _ ψ h

section StackOrd
variable {K : Type} [Field K] [DecidableEq K] (N : ℕ) [NeZero N]

theorem stackOrd_mul (a b : ℤ) (X Y : ↥(modularFunctionFieldC K N)) (hX : X ≠ 0) (hY : Y ≠ 0)
    (x : Place K (modularFunctionFieldC K N)) :
    stackOrd N (a + b) (X * Y) x = stackOrd N a X x + stackOrd N b Y x := by
  unfold stackOrd
  rw [x.ord_mul hX hY]
  ring

theorem stackOrd_inv (a : ℤ) (X : ↥(modularFunctionFieldC K N)) (x : Place K (modularFunctionFieldC K N)) :
    stackOrd N (-a) X⁻¹ x = - stackOrd N a X x := by
  unfold stackOrd
  rw [x.ord_inv]
  ring

end StackOrd

theorem core (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (m : ℕ) (ψ : PowerSeries K) (hψ : ψ ∈ ModPForms.modPMod N (2 * (m : ℤ)) K)
    (hP : SwdAlgebra.qP K * ψ ∈ ModPForms.modPMod N (2 * (m : ℤ) + 2) K) :
    ψ ∈ ModPForms.modPMod N (2 * (m : ℤ) - ((p : ℤ) - 1)) K := by
  classical

  obtain ⟨t, ht⟩ : ∃ t : ℕ, p = 2 * t + 1 := by
    have hodd := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left (by omega)
    obtain ⟨t, ht⟩ := hodd
    exact ⟨t, by omega⟩
  have hpm1 : ((p : ℤ) - 1) / 2 = t := by omega
  have hpp1 : ((p : ℤ) + 1) / 2 = t + 1 := by omega

  by_cases hψ0 : ψ = 0
  · subst hψ0; exact Submodule.zero_mem _

  obtain ⟨G, hGint, hGq⟩ :=
    ModPForms.exists_isModPFormFn_qexpOfWeight_eq_of_mem_modPMod p N hpN K m ψ hψ
  have hP' : SwdAlgebra.qP K * ψ ∈ ModPForms.modPMod N (2 * ((m + 1 : ℕ) : ℤ)) K := by
    have : (2 * ((m + 1 : ℕ) : ℤ)) = 2 * (m : ℤ) + 2 := by push_cast; ring
    rw [this]; exact hP
  obtain ⟨G₂, hG₂int, hG₂q⟩ :=
    ModPForms.exists_isModPFormFn_qexpOfWeight_eq_of_mem_modPMod p N hpN K (m + 1) _ hP'
  obtain ⟨h, hhq, hhaff, hhcusp⟩ :=
    ModularCurve.exists_coe_eq_thetaL_jqModC_zpow_and_stackOrd_eq p hp5 N hpN K
  obtain ⟨b, hbq, hbss⟩ :=
    ModularCurve.exists_coe_eq_qP_mul_thetaL_jqModC_zpow_and_stackOrd_eq_zero p hp5 N hpN K

  set T : LaurentSeries K := thetaL K (jqModC K) with hT
  have hT0 : T ≠ 0 := by
    have h := ModularCurve.thetaL_jqNModC_ne_zero K 1 (by simp)
    rwa [jqNModC_one] at h

  have hGq' : (G : LaurentSeries K) * T ^ (m : ℤ) = HahnSeries.ofPowerSeries ℤ K ψ := by
    simpa [qexpOfWeight, thetaJ, hT] using hGq
  have hG₂q' : (G₂ : LaurentSeries K) * T ^ ((m : ℤ) + 1) =
      HahnSeries.ofPowerSeries ℤ K (SwdAlgebra.qP K) * HahnSeries.ofPowerSeries ℤ K ψ := by
    have e : (((m + 1 : ℕ) : ℤ)) = (m : ℤ) + 1 := by push_cast; ring
    have h := hG₂q
    simp only [qexpOfWeight, thetaJ, map_mul, e] at h
    exact h

  have hpsi0 : HahnSeries.ofPowerSeries ℤ K ψ ≠ 0 := by
    intro h0
    exact hψ0 (HahnSeries.ofPowerSeries_injective (by rw [h0, map_zero]))
  have hG0 : G ≠ 0 := by
    intro h0; apply hpsi0; rw [← hGq', h0]; simp
  have hqP0 : HahnSeries.ofPowerSeries ℤ K (SwdAlgebra.qP K) ≠ 0 := by
    intro h0
    have h1 : SwdAlgebra.qP K = 0 := HahnSeries.ofPowerSeries_injective (by rw [h0, map_zero])
    have h2 := congrArg (PowerSeries.coeff 0) h1
    simp [SwdAlgebra.qP, PowerSeries.coeff_map, PowerSeries.coeff_mk] at h2
  have hG₂0 : G₂ ≠ 0 := by
    intro h0; apply mul_ne_zero hqP0 hpsi0; rw [← hG₂q', h0]; simp
  have hh0 : h ≠ 0 := by
    intro h0; have e := congrArg Subtype.val h0; rw [hhq] at e
    exact zpow_ne_zero _ hT0 (by simpa using e)
  have hb0 : b ≠ 0 := by
    intro h0; have e := congrArg Subtype.val h0; rw [hbq] at e
    exact mul_ne_zero hqP0 (zpow_ne_zero _ hT0) (by simpa using e)

  have hbG : b * G = G₂ * h := by
    apply Subtype.ext
    have e1 : ((b * G : ↥(modularFunctionFieldC K N)) : LaurentSeries K) * T ^ ((m : ℤ) + (t + 1)) =
        HahnSeries.ofPowerSeries ℤ K (SwdAlgebra.qP K) * HahnSeries.ofPowerSeries ℤ K ψ := by
      rw [IntermediateField.coe_mul, hbq, hpp1, ← hGq']
      rw [show ((m : ℤ) + (t + 1)) = (m : ℤ) + ((t : ℤ) + 1) by ring, zpow_add₀ hT0]
      have hu : T ^ (-((t : ℤ) + 1)) * T ^ ((t : ℤ) + 1) = 1 := by
        rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ hT0)]
      calc HahnSeries.ofPowerSeries ℤ K (SwdAlgebra.qP K) * T ^ (-((t : ℤ) + 1)) * (G : LaurentSeries K)
            * (T ^ (m : ℤ) * T ^ ((t : ℤ) + 1))
          = HahnSeries.ofPowerSeries ℤ K (SwdAlgebra.qP K) * ((G : LaurentSeries K) * T ^ (m : ℤ))
            * (T ^ (-((t : ℤ) + 1)) * T ^ ((t : ℤ) + 1)) := by ring
        _ = _ := by rw [hu, mul_one]
    have e2 : ((G₂ * h : ↥(modularFunctionFieldC K N)) : LaurentSeries K) * T ^ ((m : ℤ) + (t + 1)) =
        HahnSeries.ofPowerSeries ℤ K (SwdAlgebra.qP K) * HahnSeries.ofPowerSeries ℤ K ψ := by
      rw [IntermediateField.coe_mul, hhq, hpm1, ← hG₂q']
      rw [show ((m : ℤ) + (t + 1)) = ((m : ℤ) + 1) + (t : ℤ) by ring, zpow_add₀ hT0]
      have hu : T ^ (-(t : ℤ)) * T ^ (t : ℤ) = 1 := by
        rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ hT0)]
      calc (G₂ : LaurentSeries K) * T ^ (-(t : ℤ)) * (T ^ ((m : ℤ) + 1) * T ^ (t : ℤ))
          = (G₂ : LaurentSeries K) * T ^ ((m : ℤ) + 1) * (T ^ (-(t : ℤ)) * T ^ (t : ℤ)) := by ring
        _ = _ := by rw [hu, mul_one]
    have hTu : T ^ ((m : ℤ) + (t + 1)) ≠ 0 := zpow_ne_zero _ hT0
    exact mul_right_cancel₀ hTu (e1.trans e2.symm)

  obtain ⟨hGaff, hGcusp⟩ :=
    ModularCurve.stackOrd_nonneg_and_le_ord_of_isModPFormFn p hp5 N hpN K m G hG0 hGint
  obtain ⟨hG₂aff, -⟩ :=
    ModularCurve.stackOrd_nonneg_and_le_ord_of_isModPFormFn p hp5 N hpN K (m + 1) G₂ hG₂0 hG₂int

  set Q : ↥(modularFunctionFieldC K N) := G * h⁻¹ with hQ
  have hQ0 : Q ≠ 0 := mul_ne_zero hG0 (inv_ne_zero hh0)
  have hQaff : ∀ x : Place K (modularFunctionFieldC K N), IsAffineGeomPlace K N x →
      0 ≤ stackOrd N ((m : ℤ) - t) Q x := by
    intro x hx
    have eQ : stackOrd N ((m : ℤ) - t) Q x = stackOrd N (m : ℤ) G x - stackOrd N (t : ℤ) h x := by
      rw [hQ, show ((m : ℤ) - t) = (m : ℤ) + (-(t : ℤ)) by ring,
        stackOrd_mul N (m : ℤ) (-(t : ℤ)) G h⁻¹ hG0 (inv_ne_zero hh0), stackOrd_inv]
      ring
    by_cases hss : x ∈ ssPlaces p N K
    ·
      have e := congrArg (fun X : ↥(modularFunctionFieldC K N) => stackOrd N (((m : ℤ) + 1) + (t : ℤ)) X x) hbG
      have l1 : stackOrd N (((m : ℤ) + 1) + (t : ℤ)) (b * G) x =
          stackOrd N ((t : ℤ) + 1) b x + stackOrd N (m : ℤ) G x := by
        rw [show (((m : ℤ) + 1) + (t : ℤ)) = ((t : ℤ) + 1) + (m : ℤ) by ring]
        exact stackOrd_mul N _ _ b G hb0 hG0 x
      have l2 : stackOrd N (((m : ℤ) + 1) + (t : ℤ)) (G₂ * h) x =
          stackOrd N ((m : ℤ) + 1) G₂ x + stackOrd N (t : ℤ) h x :=
        stackOrd_mul N _ _ G₂ h hG₂0 hh0 x
      have hb : stackOrd N ((t : ℤ) + 1) b x = 0 := by simpa [hpp1] using hbss x hx hss
      have hh1 : stackOrd N (t : ℤ) h x = 1 := by simpa [hpm1] using (hhaff x hx).1 hss
      have hG₂x : 0 ≤ stackOrd N ((m : ℤ) + 1) G₂ x := by simpa using hG₂aff x hx
      simp only [l1, l2, hb, hh1] at e
      rw [eQ, hh1]; linarith
    · have hh0' : stackOrd N (t : ℤ) h x = 0 := by simpa [hpm1] using (hhaff x hx).2 hss
      rw [eQ, hh0']; linarith [hGaff x hx]
  have hQcusp : ∀ x : Place K (modularFunctionFieldC K N), x.ord (jGeomGen K N) < 0 →
      ((m : ℤ) - t) * (-(x.ord (jGeomGen K N))) ≤ x.ord Q := by
    intro x hx
    rw [hQ, x.ord_mul hG0 (inv_ne_zero hh0), x.ord_inv, hhcusp x hx, hpm1]
    have hc := hGcusp x hx
    nlinarith

  rcases lt_or_ge m t with hmt | htm
  ·
    exfalso
    have hneg : (m : ℤ) - t < 0 := by omega
    exact hQ0 (ModularCurve.eq_zero_of_forall_stackOrd_nonneg_of_forall_le_ord_of_neg p hp5 N hpN K
      ((m : ℤ) - t) hneg Q hQaff hQcusp)
  ·
    obtain ⟨m', rfl⟩ : ∃ m' : ℕ, m = t + m' := ⟨m - t, by omega⟩
    have hw : ((t + m' : ℕ) : ℤ) - t = (m' : ℤ) := by push_cast; ring
    rw [hw] at hQaff hQcusp
    have hQint : IsModPFormFn K m' (Q : LaurentSeries K) :=
      ModularCurve.isModPFormFn_of_forall_stackOrd_nonneg_of_forall_le_ord p hp5 N hpN K m' Q hQ0 hQaff hQcusp
    obtain ⟨φ', hφ'mem, hφ'q⟩ :=
      ModPForms.exists_mem_modPMod_ofPowerSeries_eq_qexpOfWeight_of_isModPFormFn p hp5 N hpN K m' Q hQint

    have hq : qexpOfWeight K (m' : ℤ) (Q : LaurentSeries K) = HahnSeries.ofPowerSeries ℤ K ψ := by
      simp only [qexpOfWeight, thetaJ]
      rw [← hT, hQ, IntermediateField.coe_mul, IntermediateField.coe_inv, hhq, hpm1, ← hGq', ← zpow_neg, neg_neg]
      rw [show ((t + m' : ℕ) : ℤ) = (t : ℤ) + (m' : ℤ) by push_cast; ring, zpow_add₀ hT0]
      ring
    have : φ' = ψ := HahnSeries.ofPowerSeries_injective (hφ'q.trans hq)
    subst this
    have hk : (2 * ((t + m' : ℕ) : ℤ) - ((p : ℤ) - 1)) = 2 * (m' : ℤ) := by push_cast; omega
    rw [hk]; exact hφ'mem

theorem main (p : ℕ) (hp5 : 5 ≤ p) (N' : ℕ) [NeZero N'] (hpN' : ¬ p ∣ N')
    (F : Type) [Field F] [CharP F p] (k : ℤ) (hpk : ¬ (p : ℤ) ∣ k) (φ : PowerSeries F)
    (hφ : φ ∈ ModPForms.modPMod N' k F) (hP : SwdAlgebra.qP F * φ ∈ ModPForms.modPMod N' (k + 2) F) :
    φ ∈ ModPForms.modPMod N' (k - ((p : ℤ) - 1)) F := by
  classical

  haveI : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero F p).resolve_right (by omega)⟩

  refine ModPForms.mem_modPMod_of_mul_mem_of_forall_zmod p N' k (k + 2) (k - ((p : ℤ) - 1)) F
    (SwdAlgebra.qP (ZMod p)) ?_ φ hφ (by rwa [map_qP_zmod])
  intro ψ hψ hPψ

  rcases Int.even_or_odd k with ⟨m₀, hm₀⟩ | hodd
  swap
  · rw [ModPForms.modPMod_eq_bot_of_odd N' k hodd (ZMod p)] at hψ
    rw [(Submodule.mem_bot _).mp hψ]; exact Submodule.zero_mem _

  rcases lt_or_ge k 0 with hneg | hnn
  · rw [ModPForms.modPMod_eq_bot_of_neg N' k hneg (ZMod p)] at hψ
    rw [(Submodule.mem_bot _).mp hψ]; exact Submodule.zero_mem _
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = 2 * (m : ℤ) := ⟨m₀.toNat, by omega⟩

  let K := AlgebraicClosure (ZMod p)
  haveI : CharP K p := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  have hψK := map_mem_modPMod p N' (2 * (m : ℤ)) K ψ hψ
  have hPK : SwdAlgebra.qP K * PowerSeries.map (ZMod.castHom (dvd_refl p) K) ψ ∈
      ModPForms.modPMod N' (2 * (m : ℤ) + 2) K := by
    have e := map_mem_modPMod p N' (2 * (m : ℤ) + 2) K _ hPψ
    rwa [map_mul, map_qP_zmod] at e
  have hcore := core p hp5 N' hpN' K m _ hψK hPK
  exact mem_modPMod_zmod_of_map_mem p N' _ K ψ hcore

end FltWs24.Dbfcd913

theorem solution (p : ℕ) (hp5 : 5 ≤ p) (N' : ℕ) [NeZero N'] (hpN' : ¬ p ∣ N')
    (F : Type) [Field F] [CharP F p] (k : ℤ) (hpk : ¬ (p : ℤ) ∣ k) (φ : PowerSeries F)
    (hφ : φ ∈ ModPForms.modPMod N' k F) (hP : SwdAlgebra.qP F * φ ∈ ModPForms.modPMod N' (k + 2) F) :
    φ ∈ ModPForms.modPMod N' (k - ((p : ℤ) - 1)) F :=
  FltWs24.Dbfcd913.main p hp5 N' hpN' F k hpk φ hφ hP

end S_ModPForms_mem_modPMod_sub_of_qP_mul_mem
end P2MW
export P2MW.S_ModPForms_mem_modPMod_sub_of_qP_mul_mem (solution)
