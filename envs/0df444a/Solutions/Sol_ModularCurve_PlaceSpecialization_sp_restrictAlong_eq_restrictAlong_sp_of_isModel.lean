-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.sp_restrictAlong_eq_restrictAlong_sp_of_isModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/9a27dc10-238e-53e3-890c-e95f88216877

import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_DegeneracyTower
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Theorems.Thm_ModularCurve_PlaceSpecialization_restrictAlong_heckeAlphaC_sp_and_restrictAlong_heckeBetaC_sp_eq_sp_restrictAlong_of_isModel
import Theorems.Thm_ModularCurve_ModularPolynomialData_eq_all
import Theorems.Thm_AlgebraicCurve_Place_restrictAlong_restrictAlong
import Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_heckeAlphaCIntegral_unconditional
import Theorems.Thm_ModularCurve_heckeBetaCIntegral_unconditional
import Theorems.Thm_ModularCurve_towerInclBar_isIntegral
import Theorems.Thm_ModularCurve_towerSubstBar_isIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_sp_restrictAlong_eq_restrictAlong_sp_of_isModel
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk"
p2m_attr_erase "simp" "ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.cuspCount_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero"
p2m_attr_erase "simp" "PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃"
p2m_attr_erase "simp" "ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"
p2m_attr_erase "simp" "AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec"
set_option synthInstance.maxHeartbeats 1600000
set_option Elab.async false
set_option autoImplicit false
open AlgebraicCurve IsLocalRing ModularCurve

namespace SpCompatDock

theorem eq_heckeAlphaBar {M s : ℕ} [NeZero M] [NeZero s]
    (δ : ↥(modularFunctionFieldBar M) →ₐ[AlgebraicClosure ℚ] ↥(modularFunctionFieldBar (M * s)))
    (h : ∀ x, ((δ x : ↥(modularFunctionFieldBar (M * s))) : LaurentSeries (AlgebraicClosure ℚ)) = x) :
    δ = heckeAlphaBar (AlgebraicClosure ℚ) M s :=
  AlgHom.ext fun x => Subtype.ext ((h x).trans (coe_heckeAlphaBar M s x).symm)

theorem eq_heckeBetaBar {M s : ℕ} [NeZero M] [NeZero s]
    (δ : ↥(modularFunctionFieldBar M) →ₐ[AlgebraicClosure ℚ] ↥(modularFunctionFieldBar (M * s)))
    (h : ∀ x, ((δ x : ↥(modularFunctionFieldBar (M * s))) : LaurentSeries (AlgebraicClosure ℚ)) =
      qExpand (AlgebraicClosure ℚ) s x) :
    δ = heckeBetaBar (AlgebraicClosure ℚ) M s :=
  AlgHom.ext fun x => Subtype.ext ((h x).trans (coe_heckeBetaBar M s x).symm)

theorem eq_inclusion_comp_heckeAlphaC {k : Type*} [Field k] {M s : ℕ} [NeZero M] [NeZero s]
    (hroof' : charLDegeneracyRoof k M s ≤ modularFunctionFieldC k (M * s))
    (φ : ↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s)))
    (h : ∀ x, ((φ x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x) :
    φ = (IntermediateField.inclusion hroof').comp (heckeAlphaC k M s) :=
  AlgHom.ext fun x => Subtype.ext <|
    (h x).trans <|
      ((congrArg Subtype.val (AlgHom.comp_apply (IntermediateField.inclusion hroof') (heckeAlphaC k M s) x)).trans <|
        (IntermediateField.coe_inclusion hroof' (heckeAlphaC k M s x)).trans (coe_heckeAlphaC k M s x)).symm

theorem eq_inclusion_comp_heckeBetaC {k : Type*} [Field k] {M s : ℕ} [NeZero M] [NeZero s]
    (hroof' : charLDegeneracyRoof k M s ≤ modularFunctionFieldC k (M * s))
    (φ : ↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s)))
    (h : ∀ x, ((φ x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = qExpand k s x) :
    φ = (IntermediateField.inclusion hroof').comp (heckeBetaC k M s) :=
  AlgHom.ext fun x => Subtype.ext <|
    (h x).trans <|
      ((congrArg Subtype.val (AlgHom.comp_apply (IntermediateField.inclusion hroof') (heckeBetaC k M s) x)).trans <|
        (IntermediateField.coe_inclusion hroof' (heckeBetaC k M s x)).trans (coe_heckeBetaC k M s x)).symm

end SpCompatDock

open SpCompatDock in
theorem solution
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) (hq' : q'.Prime)
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q') :
    haveI : NeZero q' := ⟨hq'.ne_zero⟩
    haveI : Fact q'.Prime := ⟨hq'⟩
    haveI : CharP (ResidueField A) q' := ValuationSubring.charP_residueField_of_liesOverPrime_def hq' hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (M * s)
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A M
    ∀ (data₁ : ModularPolynomialData q') (hKr₁ : KroneckerCongruence q' data₁)
      (hα₁ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (M * s) q')
      (hβ₁ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (M * s) q')
      (P₁ : PlaceSpecialization A q' (M * s) data₁ hKr₁ (ResidueField A) (IsLocalRing.residue A) hα₁ hβ₁)
      (R₁ : PlaceSpecialization.ProlongationTuple P₁) (hmodel₁ : R₁.IsModel) (hO₁ : R₁.OrderLawFixed)
      (data₂ : ModularPolynomialData q') (hKr₂ : KroneckerCongruence q' data₂)
      (hα₂ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) M q')
      (hβ₂ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) M q')
      (P₂ : PlaceSpecialization A q' M data₂ hKr₂ (ResidueField A) (IsLocalRing.residue A) hα₂ hβ₂)
      (R₂ : PlaceSpecialization.ProlongationTuple P₂) (hmodel₂ : R₂.IsModel) (hO₂ : R₂.OrderLawFixed)
      (δ : Fin 2 → (↥(modularFunctionFieldBar M) →ₐ[AlgebraicClosure ℚ] ↥(modularFunctionFieldBar (M * s))))
      (hδ : ∀ i, (δ i).toRingHom.IsIntegral)
      (hδα : ∀ x, ((δ 0 x : ↥(modularFunctionFieldBar (M * s))) : LaurentSeries (AlgebraicClosure ℚ)) = x)
      (hδβ : ∀ x, ((δ 1 x : ↥(modularFunctionFieldBar (M * s))) : LaurentSeries (AlgebraicClosure ℚ)) =
        qExpand (AlgebraicClosure ℚ) s x)
      (φ : Fin 2 → (↥(modularFunctionFieldC (ResidueField A) M) →ₐ[ResidueField A] ↥(modularFunctionFieldC (ResidueField A) (M * s))))
      (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
      (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC (ResidueField A) (M * s))) : LaurentSeries (ResidueField A)) = x)
      (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC (ResidueField A) (M * s))) : LaurentSeries (ResidueField A)) = qExpand (ResidueField A) s x),
    ∀ (i : Fin 2) (v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (M * s))),
      frobOnPlacesGeomLevel (ResidueField A) M data₂ hKr₂
          (frobOnPlacesGeomLevel (ResidueField A) M data₂ hKr₂ ((P₁.sp v).restrictAlong (φ i) (hφ i))) ≠
        (P₁.sp v).restrictAlong (φ i) (hφ i) →
      P₂.sp (v.restrictAlong (δ i) (hδ i)) = (P₁.sp v).restrictAlong (φ i) (hφ i) := by
  haveI : NeZero q' := ⟨hq'.ne_zero⟩
  haveI hqF : Fact q'.Prime := ⟨hq'⟩
  haveI : CharP (ResidueField A) q' := ValuationSubring.charP_residueField_of_liesOverPrime_def hq' hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (M * s)
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A M
  intro data₁ hKr₁ hα₁ hβ₁ P₁ R₁ hmodel₁ hO₁ data₂ hKr₂ hα₂ hβ₂ P₂ R₂ hmodel₂ hO₂ δ hδ hδα hδβ φ hφ hφα hφβ

  obtain rfl : data₂ = data₁ := ModularPolynomialData.eq_all q' data₂ data₁
  obtain rfl : hKr₂ = hKr₁ := rfl

  haveI hsF : Fact s.Prime := ⟨hs⟩
  have hq's : ¬ q' ∣ s := fun h => by
    rcases (Nat.dvd_prime hs).mp h with h1 | h1
    · exact hq'.one_lt.ne' h1
    · exact hsq' h1.symm
  have hq'Ms : ¬ q' ∣ M * s := fun h => by
    rcases hq'.dvd_mul.mp h with h1 | h1
    · exact hq'M h1
    · exact hq's h1

  have hroofeq : charLDegeneracyRoof (ResidueField A) M s = modularFunctionFieldC (ResidueField A) (M * s) :=
    (ModularCurve.charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul (ResidueField A) q' M s hq'Ms).trans
      (ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC (ResidueField A) q' (M * s) hq'Ms).symm
  have hroof' : charLDegeneracyRoof (ResidueField A) M s ≤ modularFunctionFieldC (ResidueField A) (M * s) := hroofeq.le
  have hroof : modularFunctionFieldC (ResidueField A) (M * s) ≤ charLDegeneracyRoof (ResidueField A) M s := hroofeq.ge
  have hι' : (IntermediateField.inclusion hroof').toRingHom.IsIntegral := by
    apply RingHom.isIntegral_of_surjective
    intro z
    exact ⟨IntermediateField.inclusion hroof z, Subtype.ext
      ((IntermediateField.coe_inclusion hroof' (IntermediateField.inclusion hroof z)).trans
        (IntermediateField.coe_inclusion hroof z))⟩

  have hαℓ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) M s :=
    ModularCurve.towerInclBar_isIntegral (AlgebraicClosure ℚ) (dvd_mul_right M s)
  have hβℓ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) M s := by
    unfold HeckeBetaBarIntegral
    rw [heckeBetaBar_eq_towerSubstBar]
    exact ModularCurve.towerSubstBar_isIntegral (AlgebraicClosure ℚ) s dvd_rfl
  have hαC : (heckeAlphaC (ResidueField A) M s).toRingHom.IsIntegral :=
    ModularCurve.heckeAlphaCIntegral_unconditional (ResidueField A) M s
  have hβC : (heckeBetaC (ResidueField A) M s).toRingHom.IsIntegral :=
    ModularCurve.heckeBetaCIntegral_unconditional (ResidueField A) M s

  have hδ0 : δ 0 = heckeAlphaBar (AlgebraicClosure ℚ) M s := eq_heckeAlphaBar (δ 0) hδα
  have hδ1 : δ 1 = heckeBetaBar (AlgebraicClosure ℚ) M s := eq_heckeBetaBar (δ 1) hδβ
  have hφ0 : φ 0 = (IntermediateField.inclusion hroof').comp (heckeAlphaC (ResidueField A) M s) :=
    eq_inclusion_comp_heckeAlphaC hroof' (φ 0) hφα
  have hφ1 : φ 1 = (IntermediateField.inclusion hroof').comp (heckeBetaC (ResidueField A) M s) :=
    eq_inclusion_comp_heckeBetaC hroof' (φ 1) hφβ
  have hφ0i : ((IntermediateField.inclusion hroof').comp (heckeAlphaC (ResidueField A) M s)).toRingHom.IsIntegral := by
    rw [← hφ0]; exact hφ 0
  have hφ1i : ((IntermediateField.inclusion hroof').comp (heckeBetaC (ResidueField A) M s)).toRingHom.IsIntegral := by
    rw [← hφ1]; exact hφ 1

  have hSS := fun (W₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (M * s))) =>
    ModularCurve.PlaceSpecialization.restrictAlong_heckeAlphaC_sp_and_restrictAlong_heckeBetaC_sp_eq_sp_restrictAlong_of_isModel
      M q' hq' hq'M A hA _ _ hα₂ hβ₂ P₂ R₂ hmodel₂ hO₂ ⟨s, hs⟩ hsq' hα₁ hβ₁ P₁ R₁ hmodel₁ hO₁
      hαℓ hβℓ hαC hβC hroof' hι' W₀
  refine Fin.forall_fin_two.mpr ⟨fun v _ => ?_, fun v _ => ?_⟩
  ·
    have e1 : v.restrictAlong (δ 0) (hδ 0) = v.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) M s) hαℓ :=
      Place.restrictAlong_congr hδ0 (hδ 0) hαℓ v
    have e2 := (hSS v).1
    have e3 := Place.restrictAlong_restrictAlong (heckeAlphaC (ResidueField A) M s) (IntermediateField.inclusion hroof')
      hαC hι' hφ0i (P₁.sp v)
    have e4 : (P₁.sp v).restrictAlong (φ 0) (hφ 0)
        = (P₁.sp v).restrictAlong ((IntermediateField.inclusion hroof').comp (heckeAlphaC (ResidueField A) M s)) hφ0i :=
      Place.restrictAlong_congr hφ0 (hφ 0) hφ0i (P₁.sp v)
    exact (congrArg P₂.sp e1).trans (e2.symm.trans (e3.trans e4.symm))
  ·
    have e1 : v.restrictAlong (δ 1) (hδ 1) = v.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) M s) hβℓ :=
      Place.restrictAlong_congr hδ1 (hδ 1) hβℓ v
    have e2 := (hSS v).2
    have e3 := Place.restrictAlong_restrictAlong (heckeBetaC (ResidueField A) M s) (IntermediateField.inclusion hroof')
      hβC hι' hφ1i (P₁.sp v)
    have e4 : (P₁.sp v).restrictAlong (φ 1) (hφ 1)
        = (P₁.sp v).restrictAlong ((IntermediateField.inclusion hroof').comp (heckeBetaC (ResidueField A) M s)) hφ1i :=
      Place.restrictAlong_congr hφ1 (hφ 1) hφ1i (P₁.sp v)
    exact (congrArg P₂.sp e1).trans (e2.symm.trans (e3.trans e4.symm))

end S_ModularCurve_PlaceSpecialization_sp_restrictAlong_eq_restrictAlong_sp_of_isModel
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_sp_restrictAlong_eq_restrictAlong_sp_of_isModel (solution)
