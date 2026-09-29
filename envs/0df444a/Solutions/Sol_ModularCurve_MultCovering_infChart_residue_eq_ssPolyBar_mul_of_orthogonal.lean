-- Prove2me | solution 1 for ModularCurve.MultCovering.infChart_residue_eq_ssPolyBar_mul_of_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/3de956cc-fdbd-5ec9-a5e6-dfaaf20c49a1

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residuePair_mem_riemannRochSpace_of_isGoodDivisor_or_eq_cuspInftyBar
import Theorems.Thm_ValuationSubring_ratCast_mem_iff_padicValRat_nonneg
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFst_residue_of_forall_coeff_mem
import Theorems.Thm_ModularCurve_LevelOneFibre_card_eq_genusFF_one_mul_add_one_of_ssJSet
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_cuspInftyBar
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_regularityLaw
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_divisorLawFst
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_cuspLawInfty
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_divisorLawSnd_of_divisorLawFst
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_cuspLawZero_of_cuspLawInfty
import Theorems.Thm_ModularCurve_exists_eq_algebraMap_add_prod_mul_aeval_of_forall_ord_nonneg_of_hasValue
import Theorems.Thm_ModularCurve_linearIndependent_coeffMap_algebraMap
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_infChart_residue_eq_ssPolyBar_mul_of_orthogonal
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat"
p2m_attr_erase "instance" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two"
p2m_attr_erase "simp" "compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.cuspCount_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ HahnSeries.coeff_hahnTwist ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.tateUnivCurve_a₂"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.NodeLocalized.coe_modularEvalAt"
p2m_attr_erase "simp" "ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂"

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxHeartbeats 1600000

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~jBar P2MW.S_ModularCurve_MultCovering_infChart_residue_eq_ssPolyBar_mul_of_orthogonal.ModularCurve ModularCurve.MultCovering P2MW.S_ModularCurve_MultCovering_infChart_residue_eq_ssPolyBar_mul_of_orthogonal.ModularCurve.MultCovering"

namespace ModularCurve
p2m_export "ModularCurve" "embDegree embDivisor frickeInvolutionFull cuspInftyBar modularFunctionFieldFull modularFunctionFieldBar coeffMap coeffMap_coeff coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange ssJSet PlaceSpecialization.LevelOneProlongationPair modularFunctionFieldC PlaceSpecialization frobNodePair frobNodePair_fst charLGeomPlaceEquiv charLGeomPlaceOfPoint frickeInvolutionBar frickeInvolutionBar_def coe_geomAut_coeffEmb PlaceSpecialization.LevelOneProlongationPair.chartFst PlaceSpecialization.LevelOneProlongationPair.chartFst_residue_of_forall_coeff_mem LevelOneFibre.card_eq_genusFF_one_mul_add_one_of_ssJSet PlaceSpecialization.redFst_cuspInftyBar PlaceSpecialization.LevelOneProlongationPair.regularityLaw PlaceSpecialization.LevelOneProlongationPair.divisorLawFst PlaceSpecialization.LevelOneProlongationPair.cuspLawInfty PlaceSpecialization.LevelOneProlongationPair.divisorLawSnd_of_divisorLawFst PlaceSpecialization.LevelOneProlongationPair.cuspLawZero_of_cuspLawInfty exists_eq_algebraMap_add_prod_mul_aeval_of_forall_ord_nonneg_of_hasValue linearIndependent_coeffMap_algebraMap"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "ssPolyBar jBar mAnnuli ChartCtx infChart chart ssValue"
namespace INF
p2m_open "ModularCurve.MultCovering ModularCurve~jBar"

theorem neg_le_ord_of_mem_riemannRochSpace {K F : Type*} [Field K] [Field F] [Algebra K F]
    {D : Divisor K F} {f : F} (hf : f ∈ riemannRochSpace D) (hf0 : f ≠ 0) (v : Place K F) :
    -D v ≤ v.ord f := by
  have h := hf v
  have hne := v.adicValuation_ne_zero hf0
  rw [← WithZero.exp_log hne, WithZero.exp_le_exp] at h
  show -D v ≤ -(WithZero.log (v.adicValuation f))
  omega

theorem coeff_coe_smul (K : Type*) [Field K] (S : IntermediateField K (LaurentSeries K)) (c : K) (x : S) (n : ℤ) :
    ((c • x : S) : LaurentSeries K).coeff n = c * (x : LaurentSeries K).coeff n := by
  rw [Algebra.smul_def, IntermediateField.coe_mul]
  erw [SubalgebraClass.coe_algebraMap S c]
  rw [HahnSeries.algebraMap_apply']
  simp

theorem coeff_coe_ratSmul (S : IntermediateField ℚ (LaurentSeries ℚ)) (c : ℚ) (x : S) (n : ℤ) :
    ((c • x : S) : LaurentSeries ℚ).coeff n = c * (x : LaurentSeries ℚ).coeff n := by
  have h1 : ((c • x : S) : LaurentSeries ℚ) = c • (x : LaurentSeries ℚ) := rfl
  have h2 : (c : LaurentSeries ℚ) = HahnSeries.C c := by
    rw [← map_ratCast (HahnSeries.C : ℚ →+* LaurentSeries ℚ) c, Rat.cast_id]
  rw [h1, Rat.smul_def, h2, HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]

section PIntegral

variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}

theorem valuation_natCast_lt_one (hA : A.LiesOverPrime p) : A.valuation ((p : ℕ) : AlgebraicClosure ℚ) < 1 :=
  (A.mem_nonunits_iff).mp hA

theorem ratCast_mem (hA : A.LiesOverPrime p) {x : ℚ} (hx : 0 ≤ padicValRat p x) :
    ((x : ℚ) : AlgebraicClosure ℚ) ∈ A := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  exact (A.ratCast_mem_iff_padicValRat_nonneg (Fact.out : p.Prime) (valuation_natCast_lt_one hA) hx0).mpr hx

theorem padicValRat_nonneg_of_mem (hA : A.LiesOverPrime p) {x : ℚ}
    (hx : ((x : ℚ) : AlgebraicClosure ℚ) ∈ A) : 0 ≤ padicValRat p x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  exact (A.ratCast_mem_iff_padicValRat_nonneg (Fact.out : p.Prime) (valuation_natCast_lt_one hA) hx0).mp hx

theorem padicValRat_inv_mul_nonneg_of_residue_eq_zero (hA : A.LiesOverPrime p) {x : ℚ} (hx : 0 ≤ padicValRat p x)
    (h0 : IsLocalRing.residue ↥A ⟨(x : AlgebraicClosure ℚ), ratCast_mem hA hx⟩ = 0) :
    0 ≤ padicValRat p ((p : ℚ)⁻¹ * x) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp

  have hnu : ¬ IsUnit (⟨(x : AlgebraicClosure ℚ), ratCast_mem hA hx⟩ : ↥A) := by
    rw [IsLocalRing.residue_eq_zero_iff] at h0
    exact (IsLocalRing.mem_maximalIdeal _).mp h0
  have hinv : ((x⁻¹ : ℚ) : AlgebraicClosure ℚ) ∉ A := by
    intro hmem
    apply hnu
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
    show ((x : ℚ) : AlgebraicClosure ℚ) * ((x⁻¹ : ℚ) : AlgebraicClosure ℚ) = 1
    rw [Rat.cast_inv, mul_inv_cancel₀ (by exact_mod_cast hx0)]
  have hneg : padicValRat p x⁻¹ < 0 := by
    by_contra hge
    exact hinv (ratCast_mem hA (not_lt.mp hge))
  rw [padicValRat.inv] at hneg
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [padicValRat.mul (inv_ne_zero hp0) hx0, padicValRat.inv, padicValRat.self (Fact.out : p.Prime).one_lt]
  omega

theorem not_dvd_den (hx0 : ∀ {x : ℚ}, True) {x : ℚ} (hx : 0 ≤ padicValRat p x) : ¬ (p ∣ x.den) := by
  intro hd
  rcases eq_or_ne x 0 with rfl | hx0'
  · simp at hd; exact (Fact.out : p.Prime).one_lt.ne' hd
  have hnd : ¬ (p : ℤ) ∣ x.num := by
    intro hn
    have : p ∣ Nat.gcd x.num.natAbs x.den := Nat.dvd_gcd (Int.natAbs_dvd_natAbs.mpr hn) hd
    rw [x.reduced] at this
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp this)
  have h1 : 1 ≤ padicValNat p x.den := one_le_padicValNat_of_dvd x.den_ne_zero hd
  rw [padicValRat_def, padicValInt.eq_zero_of_not_dvd hnd, Nat.cast_zero, zero_sub] at hx
  have h1' : (1 : ℤ) ≤ (padicValNat p x.den : ℤ) := by exact_mod_cast h1
  omega

def redZMod (p : ℕ) (x : ℚ) : ZMod p := (x.num : ZMod p) * ((x.den : ZMod p))⁻¹

@[scoped simp] theorem redZMod_zero : redZMod p (0 : ℚ) = 0 := by simp [redZMod]

theorem algebraMap_redZMod [CharP (IsLocalRing.ResidueField ↥A) p] [Algebra (ZMod p) (IsLocalRing.ResidueField ↥A)] (hA : A.LiesOverPrime p) {x : ℚ} (hx : 0 ≤ padicValRat p x) :
    algebraMap (ZMod p) (IsLocalRing.ResidueField ↥A) (redZMod p x)
      = IsLocalRing.residue ↥A ⟨(x : AlgebraicClosure ℚ), ratCast_mem hA hx⟩ := by
  have hden : ((x.den : ℕ) : (IsLocalRing.ResidueField ↥A)) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (IsLocalRing.ResidueField ↥A) p]
    exact not_dvd_den (fun {_} => trivial) hx

  have hmul : (⟨(x : AlgebraicClosure ℚ), ratCast_mem hA hx⟩ : ↥A) * (x.den : ↥A) = (x.num : ↥A) := by
    apply Subtype.ext
    push_cast
    exact_mod_cast x.mul_den_eq_num
  have hk := congrArg (IsLocalRing.residue ↥A) hmul
  rw [map_mul, map_natCast, map_intCast] at hk
  show algebraMap (ZMod p) _ ((x.num : ZMod p) * ((x.den : ZMod p))⁻¹) = _
  rw [map_mul, map_inv₀, map_intCast, map_natCast, eq_comm, ← hk, mul_inv_cancel_right₀ hden]

end PIntegral

theorem valuation_natCast_lt_one_ord {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    (hA : A.LiesOverPrime p) : A.valuation ((p : ℕ) : AlgebraicClosure ℚ) < 1 :=
  (A.mem_nonunits_iff).mp hA

theorem ratCast_mem_ord {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    (hA : A.LiesOverPrime p) {x : ℚ} (hx : 0 ≤ padicValRat p x) :
    ((x : ℚ) : AlgebraicClosure ℚ) ∈ A := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  · exact (A.ratCast_mem_iff_padicValRat_nonneg (Fact.out : p.Prime) (valuation_natCast_lt_one_ord hA) hx0).mpr hx

set_option maxHeartbeats 6400000 in
theorem fricke_residue₂_eq_zero
    {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    (y : ↥(modularFunctionFieldFull (1 * p)))
    (hy : ∀ m : ℤ, 0 ≤ padicValRat p
      ((p : ℚ)⁻¹ * ((frickeInvolutionFull (1 * p) y : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m)) :
    ∃ h₂ : (⟨coeffEmb (AlgebraicClosure ℚ) ↑y, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) y.2⟩ : ↥(modularFunctionFieldBar (1 * p)))
        ∈ Γ.R.R₂.integers,
      Γ.R.R₂.residue ⟨⟨coeffEmb (AlgebraicClosure ℚ) ↑y, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) y.2⟩, h₂⟩ = 0 := by
  classical
  have hp : p.Prime := Fact.out
  set Y : ↥(modularFunctionFieldBar (1 * p)) :=
    ⟨coeffEmb (AlgebraicClosure ℚ) ↑y, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) y.2⟩ with hYdef
  set f : ↥(modularFunctionFieldBar (1 * p)) := frickeInvolutionBar (1 * p) Y with hfdef

  set c : ℤ → ℚ := fun m =>
    ((frickeInvolutionFull (1 * p) y : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m with hcdef
  have hcoef : ∀ n : ℤ, (f : LaurentSeries (AlgebraicClosure ℚ)).coeff n = ((c n : ℚ) : AlgebraicClosure ℚ) := by
    intro n
    rw [hfdef, hYdef, frickeInvolutionBar_def, coe_geomAut_coeffEmb, coeffEmb_coeff, eq_ratCast]

  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hcm : ∀ m, ((c m : ℚ) : AlgebraicClosure ℚ) =
      (p : AlgebraicClosure ℚ) * (((p : ℚ)⁻¹ * c m : ℚ) : AlgebraicClosure ℚ) := by
    intro m
    push_cast
    rw [← mul_assoc, mul_inv_cancel₀ hp0, one_mul]
  have hmemA : ∀ m, (((p : ℚ)⁻¹ * c m : ℚ) : AlgebraicClosure ℚ) ∈ A := fun m => ratCast_mem_ord hA (hy m)
  have hpA : ((p : ℕ) : AlgebraicClosure ℚ) ∈ A := natCast_mem A p
  have hf : ∀ n : ℤ, (f : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ A := by
    intro n
    rw [hcoef n, hcm n]
    exact mul_mem hpA (hmemA n)
  obtain ⟨h₁, hres⟩ :=
    PlaceSpecialization.LevelOneProlongationPair.chartFst_residue_of_forall_coeff_mem Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply f hf
  have hpnu : ¬ IsUnit (⟨((p : ℕ) : AlgebraicClosure ℚ), hpA⟩ : ↥A) := by
    have h1 : ((⟨((p : ℕ) : AlgebraicClosure ℚ), hpA⟩ : ↥A) : AlgebraicClosure ℚ) ∈ A.nonunits := hA
    rw [ValuationSubring.coe_mem_nonunits_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h1
    exact h1
  have hres0 : ∀ n : ℤ,
      (((PlaceSpecialization.LevelOneProlongationPair.chartFst Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply).residue ⟨f, h₁⟩ :
          ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) :
            LaurentSeries (IsLocalRing.ResidueField ↥A)).coeff n = 0 := by
    intro n
    rw [hres n, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    have hx : (⟨(f : LaurentSeries (AlgebraicClosure ℚ)).coeff n, hf n⟩ : ↥A) =
        ⟨((p : ℕ) : AlgebraicClosure ℚ), hpA⟩ * ⟨_, hmemA n⟩ := by
      apply Subtype.ext
      show (f : LaurentSeries (AlgebraicClosure ℚ)).coeff n = (p : AlgebraicClosure ℚ) * _
      rw [hcoef n, hcm n]
    rw [hx]
    intro hu
    exact hpnu (IsUnit.mul_iff.mp hu).1

  have hres1 : (PlaceSpecialization.LevelOneProlongationPair.chartFst Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply).residue ⟨f, h₁⟩ = 0 := by
    apply Subtype.ext
    ext n
    rw [hres0 n]
    simp
  have hraw : Γ.R.R₁.residue ⟨f, h₁⟩ = 0 := by
    have hι : Γ.R.ι (Γ.R.R₁.residue ⟨f, h₁⟩) = 0 := hres1
    exact (map_eq_zero_iff Γ.R.ι Γ.R.ι.injective).mp hι

  have h₂ : Y ∈ Γ.R.R₂.integers := (Γ.R.mem_integers₂_iff Y).mpr h₁
  refine ⟨h₂, ?_⟩
  rw [Γ.R.residue₂_eq Y h₂]
  exact hraw

theorem neg_le_ord_of_mem_riemannRochSpace_ord {K F : Type*} [Field K] [Field F] [Algebra K F]
    {D : Divisor K F} {f : F} (hf : f ∈ riemannRochSpace D) (hf0 : f ≠ 0) (v : Place K F) :
    -D v ≤ v.ord f := by
  rcases (mem_riemannRochSpace_iff.mp hf) v with h | h
  · exact absurd h hf0
  · exact h

set_option maxHeartbeats 6400000 in
theorem ord_residue_bounds_of_residue₂_eq_zero
    {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)] (Γ : ChartCtx p A)
    (G : ↥(modularFunctionFieldBar (1 * p))) (hG : G ∈ riemannRochSpace (embDivisor (1 * p)))
    (h₁ : G ∈ (infChart Γ).integers) (h₂ : G ∈ Γ.R.R₂.integers) (hres₂ : Γ.R.R₂.residue ⟨G, h₂⟩ = 0) :
    (∀ v : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1), v ≠ Γ.P.redFst (cuspInftyBar (1 * p)) →
        0 ≤ v.ord ((infChart Γ).residue ⟨G, h₁⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))) ∧
    (-(embDegree (1 * p) : ℤ) ≤ (Γ.P.redFst (cuspInftyBar (1 * p))).ord ((infChart Γ).residue ⟨G, h₁⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))) ∧
    (∀ a ∈ ssJSet p (IsLocalRing.ResidueField ↥A),
        (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) a).HasValue ((infChart Γ).residue ⟨G, h₁⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) 0) := by
  classical

  set R := Γ.R with hRdef
  have hR : R.IsModel :=
    ⟨PlaceSpecialization.LevelOneProlongationPair.divisorLawFst R,
      PlaceSpecialization.LevelOneProlongationPair.divisorLawSnd_of_divisorLawFst R
        (PlaceSpecialization.LevelOneProlongationPair.divisorLawFst R),
      PlaceSpecialization.LevelOneProlongationPair.cuspLawInfty R,
      PlaceSpecialization.LevelOneProlongationPair.cuspLawZero_of_cuspLawInfty R
        (PlaceSpecialization.LevelOneProlongationPair.cuspLawInfty R)⟩
  set S₀ : Finset (IsLocalRing.ResidueField ↥A) := Γ.hfin.toFinset with hS₀def
  have hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet p (IsLocalRing.ResidueField ↥A) := fun a => Set.Finite.mem_toFinset _
  have hNR : R.RegularityLaw S₀ := PlaceSpecialization.LevelOneProlongationPair.regularityLaw R (fun a ha => (hS₀ a).mp ha)

  set D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) := embDivisor (1 * p) with hDdef
  have hDapp : ∀ W, D W = if W = cuspInftyBar (1 * p) then (embDegree (1 * p) : ℤ) else 0 := by
    intro W
    show ((embDegree (1 * p) : ℤ) • Finsupp.single (cuspInftyBar (1 * p)) (1 : ℤ)) W = _
    rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
    by_cases h : W = cuspInftyBar (1 * p)
    · rw [if_pos h.symm, if_pos h, mul_one]
    · rw [if_neg (Ne.symm h), if_neg h, mul_zero]
  have hD : ∀ W, 0 ≤ D W := fun W => by
    rw [hDapp]; split_ifs <;> simp
  have hgood : ∀ W ∈ D.support, Γ.P.IsStrictTypeOne W ∨ Γ.P.IsStrictTypeTwo W ∨ W = cuspInftyBar (1 * p) := by
    intro W hW
    right; right
    by_contra hne
    apply Finsupp.mem_support_iff.mp hW
    rw [hDapp, if_neg hne]
  have h₁' : G ∈ R.R₁.integers := h₁
  obtain ⟨hL₁, -, hnode⟩ :=
    R.residuePair_mem_riemannRochSpace_of_isGoodDivisor_or_eq_cuspInftyBar hR S₀ hS₀ hNR D hD hgood G hG h₁' h₂

  have hres : ((infChart Γ).residue ⟨G, h₁⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) =
      R.ι (R.R₁.residue ⟨G, h₁'⟩) := rfl

  have hfst : Γ.P.fstPart D = 0 := by
    ext W
    show (D.filter Γ.P.IsStrictTypeOne) W = 0
    rw [Finsupp.filter_apply]
    split_ifs with hs
    · rw [hDapp, if_neg]
      rintro rfl
      exact hs.2 Γ.supply.cusp_fixed
    · rfl
  have hE' : Finsupp.mapDomain Γ.P.redFst (Γ.P.fstPart D + Finsupp.single (cuspInftyBar (1 * p)) (D (cuspInftyBar (1 * p)))) =
      Finsupp.single (Γ.P.redFst (cuspInftyBar (1 * p))) (embDegree (1 * p) : ℤ) := by
    rw [hfst, zero_add, Finsupp.mapDomain_single, hDapp, if_pos rfl]
  rw [hE'] at hL₁
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    rw [hres]
    by_cases h0 : (R.ι (R.R₁.residue ⟨G, h₁'⟩) : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) = 0
    · rw [h0, Place.ord_zero]
    · have := neg_le_ord_of_mem_riemannRochSpace_ord hL₁ h0 v
      rw [Finsupp.single_apply, if_neg (Ne.symm hv), neg_zero] at this
      exact this
  · rw [hres]
    by_cases h0 : (R.ι (R.R₁.residue ⟨G, h₁'⟩) : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) = 0
    · rw [h0, Place.ord_zero]
      have : (0 : ℤ) ≤ (embDegree (1 * p) : ℤ) := Int.natCast_nonneg _
      omega
    · have := neg_le_ord_of_mem_riemannRochSpace_ord hL₁ h0 (Γ.P.redFst (cuspInftyBar (1 * p)))
      rw [Finsupp.single_apply, if_pos rfl] at this
      exact this
  · intro a ha
    obtain ⟨c, hc₁, hc₂⟩ := hnode a ((hS₀ a).mpr ha)
    have hι0 : (R.ι (R.R₂.residue ⟨G, h₂⟩) : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) = 0 := by
      rw [hres₂, map_zero]
    rw [hι0] at hc₂
    have hc0 : c = 0 := by
      have h0 : ((frobNodePair p a).2).HasValue (0 : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) 0 := by
        have := Place.hasValue_algebraMap (frobNodePair p a).2 (0 : IsLocalRing.ResidueField ↥A)
        rwa [map_zero] at this
      exact hc₂.unique h0
    rw [hres, ← frobNodePair_fst p a]
    rw [hc0] at hc₁
    exact hc₁

theorem prod_toFinset_sub_eq_ssPolyBar
    {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) :
    (∏ a ∈ Γ.hfin.toFinset, (jBar (IsLocalRing.ResidueField ↥A) - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) a)) = ssPolyBar Γ := by
  rw [← Finset.prod_coe_sort]
  show _ = ∏ e : Fin (mAnnuli p), (jBar (IsLocalRing.ResidueField ↥A)
    - algebraMap (IsLocalRing.ResidueField ↥A) _ (ssValue Γ e))
  refine Fintype.prod_equiv (Γ.hfin.toFinset.equivFinOfCardEq Γ.hcard) _ _ (fun i => ?_)
  simp only [ssValue, Equiv.symm_apply_apply]

theorem embDegree_add_one_eq
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)] (Γ : ChartCtx p A) :
    Γ.hfin.toFinset.card = mAnnuli p ∧ embDegree (1 * p) + 1 = 2 * mAnnuli p := by
  have hc := ModularCurve.LevelOneFibre.card_eq_genusFF_one_mul_add_one_of_ssJSet hp5 Γ.hfin.toFinset
    (fun a => Set.Finite.mem_toFinset _)
  refine ⟨Γ.hcard, ?_⟩
  have hcard := Γ.hcard
  unfold embDegree
  omega

end ModularCurve.MultCovering.INF
p2m_reactivate "P2MW.S_ModularCurve_MultCovering_infChart_residue_eq_ssPolyBar_mul_of_orthogonal.ModularCurve P2MW.S_ModularCurve_MultCovering_infChart_residue_eq_ssPolyBar_mul_of_orthogonal.ModularCurve.MultCovering P2MW.S_ModularCurve_MultCovering_infChart_residue_eq_ssPolyBar_mul_of_orthogonal.ModularCurve.MultCovering.INF"
p2m_reactivate "P2MW.S_ModularCurve_MultCovering_infChart_residue_eq_ssPolyBar_mul_of_orthogonal.ModularCurve P2MW.S_ModularCurve_MultCovering_infChart_residue_eq_ssPolyBar_mul_of_orthogonal.ModularCurve.MultCovering"
p2m_reactivate "P2MW.S_ModularCurve_MultCovering_infChart_residue_eq_ssPolyBar_mul_of_orthogonal.ModularCurve"

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
open ModularCurve.MultCovering.INF in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    {r : ℕ} (hr : r = mAnnuli p + 1) (g : Fin r → ↥(modularFunctionFieldFull (1 * p)))
    (hg0 : ∀ l : Fin r, (l : ℕ) = 0 → g l = 1)
    (hW : ∀ l : Fin r, (⟨coeffEmb (AlgebraicClosure ℚ) ↑(g l), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (g l).2⟩ : ↥(modularFunctionFieldBar (1 * p))) ∈ riemannRochSpace (embDivisor (1 * p)))
    (horth : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • g i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, 0 ≤ padicValRat p (c i))
    (h0 : ∀ l : Fin r, 1 ≤ (l : ℕ) → ∀ m : ℤ, 0 ≤ padicValRat p
      ((p : ℚ)⁻¹ * ((frickeInvolutionFull (1 * p) (g l) : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) :
    ∃ hint : ∀ l, (⟨coeffEmb (AlgebraicClosure ℚ) ↑(g l), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (g l).2⟩ : ↥(modularFunctionFieldBar (1 * p))) ∈ (infChart Γ).integers,
      (∀ l : Fin r, (l : ℕ) = 0 → (infChart Γ).residue ⟨(⟨coeffEmb (AlgebraicClosure ℚ) ↑(g l), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (g l).2⟩ : ↥(modularFunctionFieldBar (1 * p))), hint l⟩ = 1) ∧
      ∃ P : Fin r → Polynomial (IsLocalRing.ResidueField ↥A),
        (∀ l : Fin r, 1 ≤ (l : ℕ) →
          (P l).natDegree + 1 ≤ mAnnuli p ∧
          (infChart Γ).residue ⟨(⟨coeffEmb (AlgebraicClosure ℚ) ↑(g l), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (g l).2⟩ : ↥(modularFunctionFieldBar (1 * p))), hint l⟩
            = ssPolyBar Γ * Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l)) ∧
        LinearIndependent (IsLocalRing.ResidueField ↥A) (fun l : {l : Fin r // 1 ≤ (l : ℕ)} => P l) ∧
        Submodule.span (IsLocalRing.ResidueField ↥A) (Set.range fun l : {l : Fin r // 1 ≤ (l : ℕ)} => P l)
          = Polynomial.degreeLT (IsLocalRing.ResidueField ↥A) (mAnnuli p) := by
  classical
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A

  set T : Fin r → ↥(modularFunctionFieldBar (1 * p)) := fun l => (⟨coeffEmb (AlgebraicClosure ℚ) ↑(g l), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (g l).2⟩ : ↥(modularFunctionFieldBar (1 * p))) with hTdef
  have hp : p.Prime := Fact.out
  have hp0Q : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero

  have hcoefQ : ∀ (l : Fin r) (m : ℤ), 0 ≤ padicValRat p (((g l : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m) := by
    intro l
    have h := (horth (Pi.single l 1)).mpr (fun i => by
      rcases eq_or_ne i l with rfl | hil
      · simp
      · simp [Pi.single_eq_of_ne hil])
    simpa [Finset.sum_pi_single', Pi.single_apply] using h

  have hTcoe : ∀ l, ((T l : ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) ↑(g l) :=
    fun l => rfl
  have hcoefA : ∀ (l : Fin r) (m : ℤ), ((T l : ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)).coeff m ∈ A := by
    intro l m
    rw [hTcoe, coeffEmb_coeff, eq_ratCast]
    exact ratCast_mem hA (hcoefQ l m)

  have key : ∀ l, ∃ h : T l ∈ (infChart Γ).integers, ∀ n : ℤ,
      ((((infChart Γ).residue ⟨T l, h⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) : LaurentSeries (IsLocalRing.ResidueField ↥A)).coeff n
        = IsLocalRing.residue ↥A ⟨((T l : ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)).coeff n, hcoefA l n⟩) :=
    fun l => ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_residue_of_forall_coeff_mem
      Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply (T l) (hcoefA l)
  choose hint hres using key

  set ρ : Fin r → ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) := fun l => (infChart Γ).residue ⟨T l, hint l⟩ with hρdef
  have hρcoeff : ∀ l n, ((ρ l : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) : LaurentSeries (IsLocalRing.ResidueField ↥A)).coeff n
      = IsLocalRing.residue ↥A ⟨_, ratCast_mem hA (hcoefQ l n)⟩ := by
    intro l n
    rw [hρdef, hres l n]
    congr 1

  have hzero : ∀ l : Fin r, (l : ℕ) = 0 → ρ l = 1 := by
    intro l hl
    have hT1 : T l = 1 := by
      apply Subtype.ext
      rw [hTcoe, hg0 l hl]
      simp
    have : (⟨T l, hint l⟩ : (infChart Γ).integers) = 1 := Subtype.ext hT1
    show (infChart Γ).residue ⟨T l, hint l⟩ = 1
    rw [this, map_one]

  have hLI : LinearIndependent (IsLocalRing.ResidueField ↥A) ρ := by
    letI : Algebra (ZMod p) (IsLocalRing.ResidueField ↥A) := ZMod.algebra _ p

    let v : Fin r → LaurentSeries (ZMod p) := fun l =>
      { coeff := fun n => redZMod p (((g l : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff n)
        isPWO_support' := (((g l : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).isPWO_support).mono (by
          intro n hn
          rw [Function.mem_support] at hn
          rw [HahnSeries.mem_support]
          intro h0
          apply hn
          simp only [h0, redZMod_zero]) }
    have hvcoeff : ∀ l n, (v l).coeff n = redZMod p (((g l : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff n) := fun _ _ => rfl
    have hv : ∀ l, coeffMap (algebraMap (ZMod p) (IsLocalRing.ResidueField ↥A)) (v l) = ((ρ l : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) : LaurentSeries (IsLocalRing.ResidueField ↥A)) := by
      intro l; ext n
      rw [coeffMap_coeff, hvcoeff, hρcoeff l n]
      exact algebraMap_redZMod hA (hcoefQ l n)

    have hcomb : ∀ (c : Fin r → ℚ) (n : ℤ), ((∑ i, c i • g i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff n
        = ∑ i, c i * ((g i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff n := by
      intro c n
      rw [IntermediateField.coe_sum, HahnSeries.coeff_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact coeff_coe_ratSmul (modularFunctionFieldFull (1 * p)) (c i) (g i) n

    have hvLI : LinearIndependent (ZMod p) v := by
      rw [Fintype.linearIndependent_iff]
      intro eb hrel l₀
      let e : Fin r → ℕ := fun l => (eb l).val
      have he : ∀ l, ((e l : ℕ) : ZMod p) = eb l := fun l => ZMod.natCast_zmod_val (eb l)
      have hGint : ∀ n, 0 ≤ padicValRat p (((∑ i, (e i : ℚ) • g i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff n) := by
        intro n
        apply padicValRat_nonneg_of_mem hA
        rw [hcomb, Rat.cast_sum]
        refine sum_mem fun l _ => ?_
        rw [Rat.cast_mul, Rat.cast_natCast]
        exact mul_mem (natCast_mem A _) (ratCast_mem hA (hcoefQ l n))
      have hGres : ∀ n, IsLocalRing.residue ↥A ⟨_, ratCast_mem hA (hGint n)⟩ = 0 := by
        intro n
        have hsum : (⟨((((∑ i, (e i : ℚ) • g i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff n : ℚ) : AlgebraicClosure ℚ),
              ratCast_mem hA (hGint n)⟩ : ↥A)
            = ∑ l, (e l : ↥A) * ⟨_, ratCast_mem hA (hcoefQ l n)⟩ := by
          apply Subtype.ext
          conv_rhs => rw [AddSubmonoidClass.coe_finsetSum]
          show ((((∑ i, (e i : ℚ) • g i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff n : ℚ) : AlgebraicClosure ℚ) = _
          rw [hcomb, Rat.cast_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          push_cast
          rfl
        rw [hsum, map_sum]
        have h2 : (coeffMap (algebraMap (ZMod p) (IsLocalRing.ResidueField ↥A)) (∑ l, eb l • v l)).coeff n = 0 := by
          rw [hrel, map_zero]; rfl
        rw [map_sum, HahnSeries.coeff_sum] at h2
        rw [← h2]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [map_mul, map_natCast, coeffMap_coeff, HahnSeries.coeff_smul, smul_eq_mul, map_mul, ← he l, map_natCast,
          hvcoeff, algebraMap_redZMod hA (hcoefQ l n)]
      have hdiv : ∀ n, 0 ≤ padicValRat p ((p : ℚ)⁻¹ * (((∑ i, (e i : ℚ) • g i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff n)) :=
        fun n => padicValRat_inv_mul_nonneg_of_residue_eq_zero hA (hGint n) (hGres n)
      have hc := (horth fun l => (p : ℚ)⁻¹ * (e l : ℚ)).mp (by
        intro n
        have : ((∑ i, ((p : ℚ)⁻¹ * (e i : ℚ)) • g i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff n
            = (p : ℚ)⁻¹ * (((∑ i, (e i : ℚ) • g i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff n) := by
          rw [hcomb, hcomb, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
        rw [this]; exact hdiv n) l₀

      rw [← he l₀, CharP.cast_eq_zero_iff (ZMod p) p]
      by_contra hnd
      have he0 : (e l₀ : ℚ) ≠ 0 := by
        intro h
        apply hnd
        have : e l₀ = 0 := by exact_mod_cast h
        rw [this]
        exact dvd_zero p
      rw [padicValRat.mul (inv_ne_zero hp0Q) he0, padicValRat.inv, padicValRat.self hp.one_lt,
        padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnd] at hc
      norm_num at hc

    have h1 : LinearIndependent (IsLocalRing.ResidueField ↥A) (fun l => ((ρ l : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) : LaurentSeries (IsLocalRing.ResidueField ↥A))) := by
      have h := ModularCurve.linearIndependent_coeffMap_algebraMap (K := ZMod p) (L := (IsLocalRing.ResidueField ↥A)) v hvLI
      have hfun : (fun l => coeffMap (algebraMap (ZMod p) (IsLocalRing.ResidueField ↥A)) (v l)) = fun l => ((ρ l : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) : LaurentSeries (IsLocalRing.ResidueField ↥A)) :=
        funext hv
      rw [hfun] at h
      exact h

    let coeffL : LaurentSeries (IsLocalRing.ResidueField ↥A) →ₗ[(IsLocalRing.ResidueField ↥A)] (ℤ → (IsLocalRing.ResidueField ↥A)) :=
      { toFun := fun y => y.coeff
        map_add' := fun _ _ => rfl
        map_smul' := fun c y => HahnSeries.coeff_smul' c y }
    have h2 : LinearIndependent (IsLocalRing.ResidueField ↥A) (fun l => (((ρ l : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) : LaurentSeries (IsLocalRing.ResidueField ↥A))).coeff) :=
      h1.map' coeffL (LinearMap.ker_eq_bot.mpr HahnSeries.coeff_injective)
    let coeffC : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) →ₗ[(IsLocalRing.ResidueField ↥A)] (ℤ → (IsLocalRing.ResidueField ↥A)) :=
      { toFun := fun x => ((x : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) : LaurentSeries (IsLocalRing.ResidueField ↥A)).coeff
        map_add' := fun x y => by
          funext n
          show ((x + y : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) : LaurentSeries (IsLocalRing.ResidueField ↥A)).coeff n = _
          rw [IntermediateField.coe_add, HahnSeries.coeff_add]
          rfl
        map_smul' := fun c x => by
          funext n
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
          exact coeff_coe_smul _ (modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) c x n }
    exact LinearIndependent.of_comp coeffC h2
  have hρ0 : ∀ l, ρ l ≠ 0 := fun l => hLI.ne_zero l

  have main : ∀ l : Fin r, 1 ≤ (l : ℕ) → ∃ Q : Polynomial (IsLocalRing.ResidueField ↥A),
      Q.natDegree + 1 ≤ mAnnuli p ∧ ρ l = ssPolyBar Γ * Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) Q := by
    intro l hl
    obtain ⟨h₂, hres₂⟩ := fricke_residue₂_eq_zero hA Γ (g l) (h0 l hl)
    obtain ⟨hreg, hinf, hval⟩ := ord_residue_bounds_of_residue₂_eq_zero hA Γ (T l) (hW l) (hint l) h₂ hres₂
    obtain ⟨hcard, hdeg⟩ := embDegree_add_one_eq hp5 Γ
    have hcusp : Γ.P.redFst (cuspInftyBar (1 * p))
        = charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)) :=
      ModularCurve.PlaceSpecialization.redFst_cuspInftyBar Γ.P
    obtain ⟨Q, hQdeg, hQ⟩ := exists_eq_algebraMap_add_prod_mul_aeval_of_forall_ord_nonneg_of_hasValue
        Γ.hfin.toFinset (0 : (IsLocalRing.ResidueField ↥A)) (embDegree (1 * p)) (ρ l)
        (fun v hv => hreg v (by rwa [hcusp])) (by rw [← hcusp]; exact hinf)
        (fun a ha => hval a (Γ.hfin.mem_toFinset.mp ha))
    refine ⟨Q, ?_, ?_⟩
    · have hQ0 : Q ≠ 0 := by
        rintro rfl
        apply hρ0 l
        rw [hQ, map_zero, map_zero, mul_zero, add_zero]
      have := hQdeg hQ0
      rw [hcard] at this
      omega
    · rw [hQ, map_zero, zero_add, prod_toFinset_sub_eq_ssPolyBar Γ]

  choose Q hQ using main
  let P : Fin r → Polynomial (IsLocalRing.ResidueField ↥A) := fun l => if h : 1 ≤ (l : ℕ) then Q l h else 0
  have hP : ∀ l : Fin r, (h : 1 ≤ (l : ℕ)) → P l = Q l h := fun l h => dif_pos h
  refine ⟨hint, hzero, P, fun l hl => ?_, ?_, ?_⟩
  · rw [hP l hl]; exact hQ l hl
  ·
    have hρ' : LinearIndependent (IsLocalRing.ResidueField ↥A) (fun l : {l : Fin r // 1 ≤ (l : ℕ)} => ρ l) :=
      hLI.comp (fun l : {l : Fin r // 1 ≤ (l : ℕ)} => (l : Fin r)) Subtype.val_injective
    let L : Polynomial (IsLocalRing.ResidueField ↥A) →ₗ[(IsLocalRing.ResidueField ↥A)] ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) :=
      (LinearMap.mulLeft (IsLocalRing.ResidueField ↥A) (ssPolyBar Γ)).comp (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A))).toLinearMap
    have heq : (fun l : {l : Fin r // 1 ≤ (l : ℕ)} => ρ l) = L ∘ (fun l : {l : Fin r // 1 ≤ (l : ℕ)} => P l) := by
      funext l
      show ρ l = ssPolyBar Γ * Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l)
      rw [hP l l.2]; exact (hQ l l.2).2
    rw [heq] at hρ'
    exact LinearIndependent.of_comp L hρ'
  ·
    have hmem : ∀ l : {l : Fin r // 1 ≤ (l : ℕ)}, P l ∈ Polynomial.degreeLT (IsLocalRing.ResidueField ↥A) (mAnnuli p) := by
      intro l
      rw [Polynomial.mem_degreeLT, hP l l.2]
      exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast (hQ l l.2).1)
    apply le_antisymm
    · exact Submodule.span_le.mpr (by rintro _ ⟨l, rfl⟩; exact hmem l)
    ·
      set W := Polynomial.degreeLT (IsLocalRing.ResidueField ↥A) (mAnnuli p) with hW
      let P' : {l : Fin r // 1 ≤ (l : ℕ)} → W := fun l => ⟨P l, hmem l⟩
      have hli' : LinearIndependent (IsLocalRing.ResidueField ↥A) P' := by
        have hρ' : LinearIndependent (IsLocalRing.ResidueField ↥A) (fun l : {l : Fin r // 1 ≤ (l : ℕ)} => ρ l) :=
          hLI.comp (fun l : {l : Fin r // 1 ≤ (l : ℕ)} => (l : Fin r)) Subtype.val_injective
        let L : Polynomial (IsLocalRing.ResidueField ↥A) →ₗ[(IsLocalRing.ResidueField ↥A)] ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) :=
          (LinearMap.mulLeft (IsLocalRing.ResidueField ↥A) (ssPolyBar Γ)).comp (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A))).toLinearMap
        have heq : (fun l : {l : Fin r // 1 ≤ (l : ℕ)} => ρ l) = (L.comp W.subtype) ∘ P' := by
          funext l
          show ρ l = ssPolyBar Γ * Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l)
          rw [hP l l.2]; exact (hQ l l.2).2
        rw [heq] at hρ'
        exact LinearIndependent.of_comp _ hρ'
      have hcardsub : Fintype.card {l : Fin r // 1 ≤ (l : ℕ)} = mAnnuli p := by
        subst hr
        rw [Fintype.card_subtype]
        have : (Finset.univ.filter fun l : Fin (mAnnuli p + 1) => 1 ≤ (l : ℕ))
            = Finset.univ.image Fin.succ := by
          ext l
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
          constructor
          · intro h
            exact ⟨l.pred (fun h0 => by simp [h0] at h), by simp⟩
          · rintro ⟨i, rfl⟩
            simp [Fin.val_succ]
        rw [this, Finset.card_image_of_injective _ (Fin.succ_injective _), Finset.card_univ, Fintype.card_fin]
      have hfin : Module.finrank (IsLocalRing.ResidueField ↥A) W = mAnnuli p := by
        rw [hW, (Polynomial.degreeLTEquiv (IsLocalRing.ResidueField ↥A) (mAnnuli p)).finrank_eq, Module.finrank_fin_fun]
      haveI : FiniteDimensional (IsLocalRing.ResidueField ↥A) W :=
        LinearEquiv.finiteDimensional (Polynomial.degreeLTEquiv (IsLocalRing.ResidueField ↥A) (mAnnuli p)).symm
      have htop : Submodule.span (IsLocalRing.ResidueField ↥A) (Set.range P') = ⊤ :=
        hli'.span_eq_top_of_card_eq_finrank' (hcardsub.trans hfin.symm)

      have hWmap : W = Submodule.map W.subtype ⊤ := by rw [Submodule.map_top, Submodule.range_subtype]
      rw [hWmap, ← htop, Submodule.map_span, ← Set.range_comp]
      exact le_rfl

end S_ModularCurve_MultCovering_infChart_residue_eq_ssPolyBar_mul_of_orthogonal
end P2MW
export P2MW.S_ModularCurve_MultCovering_infChart_residue_eq_ssPolyBar_mul_of_orthogonal (solution)
