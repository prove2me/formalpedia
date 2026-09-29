-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.isGoodDiv_pushforwardAlong_and_glueData_eq_of_isModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/20708093-2e05-550e-99f1-c31ded66c8f9

import Definitions.Def_AlgebraicCurve_GluedPic0Pushforward
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_DegeneracyTower
import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_PlaceSpecialization_sp_restrictAlong_eq_restrictAlong_sp_of_isModel
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_restrictAlong_degeneracyPair
import Theorems.Thm_ModularCurve_PlaceSpecialization_isStrictFst_or_isStrictSnd_iff
import Theorems.Thm_AlgebraicCurve_Place_restrictAlong_restrictAlong
import Theorems.Thm_ModularCurve_towerInclBar_isIntegral
import Theorems.Thm_ModularCurve_towerSubstBar_isIntegral
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_isGoodDiv_pushforwardAlong_and_glueData_eq_of_isModel
p2m_attr_erase "instance" "ModularCurve.SpecializationWitnessData.addCommGroup ModularCurve.CommutingHeckeFamily.commRing_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "ModularCurve.coe_heckeBetaC AlgebraicCurve.Divisor.coe_degZeroEnd ModularCurve.coe_heckeAlphaC ModularCurve.CommutingHeckeFamily.mk.injEq ModularCurve.SpecializationWitnessData.mk.sizeOf_spec ModularCurve.SpecializationWitnessData.mk.injEq ModularCurve.CommutingHeckeFamily.mk.sizeOf_spec ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.cuspCount_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero"
p2m_attr_erase "simp" "WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option Elab.async false
open AlgebraicCurve IsLocalRing ModularCurve

noncomputable section

open ModularCurve.PlaceSpecialization

namespace TransportGlue

section Generic

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

private theorem tg_deg_restrictAlong_mul (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') :
    (w.restrictAlong φ hφ).deg * w.inertiaDegAlong φ hφ = w.deg := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact w.deg_restrict_mul_inertiaDeg

private theorem tg_inertiaDegAlong_eq_one (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F')
    (hw : w.deg = 1) : w.inertiaDegAlong φ hφ = 1 := by
  have h := tg_deg_restrictAlong_mul φ hφ w
  rw [hw] at h
  exact Nat.eq_one_of_mul_eq_one_left h

private theorem tg_pushforwardAlong_single (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F')
    (hw : w.deg = 1) (n : ℤ) :
    Divisor.pushforwardAlong φ hφ (Finsupp.single w n) = Finsupp.single (w.restrictAlong φ hφ) n := by
  rw [Divisor.pushforwardAlong_single, tg_inertiaDegAlong_eq_one φ hφ w hw, Nat.cast_one, mul_one]

private theorem tg_comp_isIntegral {F'' : Type*} [Field F''] [Algebra K F''] (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'')
    (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral) : (χ.comp φ).toRingHom.IsIntegral :=
  show (χ.toRingHom.comp φ.toRingHom).IsIntegral from RingHom.IsIntegral.trans φ.toRingHom χ.toRingHom hφ hχ

end Generic

section Glue

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  (P : PlaceSpecialization A q N data hKr k red hα hβ)

private theorem tg_glueData_add
    (S : Finset (Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)))
    (X Y : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.glueData S (X + Y) = P.glueData S X + P.glueData S Y := by
  simp only [PlaceSpecialization.glueData, PlaceSpecialization.fstDiv, PlaceSpecialization.sndDiv,
    Finsupp.filter_add, Finsupp.mapDomain_add, Prod.mk_add_mk, add_zero]

private theorem tg_isGoodDiv_add {X Y : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
    (hX : P.IsGoodDiv X) (hY : P.IsGoodDiv Y) : P.IsGoodDiv (X + Y) := by
  classical
  intro W hW
  rcases Finset.mem_union.mp (Finsupp.support_add hW) with h | h
  · exact hX W h
  · exact hY W h

private theorem tg_not_isStrictFst_and_isStrictSnd (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (h₁ : P.IsStrictFst W) (h₂ : P.IsStrictSnd W) : False := by
  apply h₁.2
  rw [h₁.1]
  exact h₂.1.symm

private theorem tg_glueData_single_fst
    (S : Finset (Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)))
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hW : P.IsStrictFst W) (c : ℤ) :
    P.glueData S (Finsupp.single W c) = (Finsupp.single (P.reduceFst W) c, 0, 0) := by
  classical
  have hW' : ¬ P.IsStrictSnd W := fun h => tg_not_isStrictFst_and_isStrictSnd P W hW h
  simp only [PlaceSpecialization.glueData, PlaceSpecialization.fstDiv, PlaceSpecialization.sndDiv,
    Finsupp.filter_single_of_pos P.IsStrictFst hW, Finsupp.filter_single_of_neg P.IsStrictSnd hW',
    Finsupp.mapDomain_single, Finsupp.mapDomain_zero]

private theorem tg_glueData_single_snd
    (S : Finset (Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)))
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hW : P.IsStrictSnd W) (c : ℤ) :
    P.glueData S (Finsupp.single W c) = (0, Finsupp.single (P.reduceSnd W) c, 0) := by
  classical
  have hW' : ¬ P.IsStrictFst W := fun h => tg_not_isStrictFst_and_isStrictSnd P W h hW
  simp only [PlaceSpecialization.glueData, PlaceSpecialization.fstDiv, PlaceSpecialization.sndDiv,
    Finsupp.filter_single_of_neg P.IsStrictFst hW', Finsupp.filter_single_of_pos P.IsStrictSnd hW,
    Finsupp.mapDomain_single, Finsupp.mapDomain_zero]

private theorem tg_good_step {F' : Type*} [Field F'] [Algebra (AlgebraicClosure ℚ) F']
    (f : Divisor (AlgebraicClosure ℚ) F' →+ Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (X Y : Divisor (AlgebraicClosure ℚ) F') (hX : P.IsGoodDiv (f X)) (hY : P.IsGoodDiv (f Y)) :
    P.IsGoodDiv (f (X + Y)) := by
  rw [map_add]
  exact tg_isGoodDiv_add P hX hY

private theorem tg_glue_step
    (S : Finset (Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)))
    {N' : ℕ} [NeZero N'] {data' : ModularPolynomialData q} {hKr' : KroneckerCongruence q data'}
    {hα' : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N' q} {hβ' : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N' q}
    (Q : PlaceSpecialization A q N' data' hKr' k red hα' hβ')
    (S' : Finset (Place k (modularFunctionFieldC k N') × Place k (modularFunctionFieldC k N')))
    (f : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N' * q)) →+
      Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (g : GluingData k (modularFunctionFieldC k N') S' →+ GluingData k (modularFunctionFieldC k N) S)
    (X Y : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N' * q)))
    (hX : P.glueData S (f X) = g (Q.glueData S' X)) (hY : P.glueData S (f Y) = g (Q.glueData S' Y)) :
    P.glueData S (f (X + Y)) = g (Q.glueData S' (X + Y)) := by
  rw [map_add, tg_glueData_add, tg_glueData_add, map_add, hX, hY]

end Glue

end TransportGlue

namespace TransportGlue

section Level

variable (M s q' : ℕ) [NeZero M] [NeZero s]

private def tower0 :
    Fin 2 → (↥(modularFunctionFieldBar M) →ₐ[AlgebraicClosure ℚ] ↥(modularFunctionFieldBar (M * s))) :=
  fun i => if i = 0 then towerInclBar (AlgebraicClosure ℚ) (dvd_mul_right M s)
    else towerSubstBar (AlgebraicClosure ℚ) M s (dvd_refl (M * s))

private theorem tower0_zero : tower0 M s 0 = towerInclBar (AlgebraicClosure ℚ) (dvd_mul_right M s) := by
  simp [tower0]

private theorem tower0_one : tower0 M s 1 = towerSubstBar (AlgebraicClosure ℚ) M s (dvd_refl (M * s)) := by
  simp [tower0]

private theorem tower0_isIntegral (hs : s.Prime) (i : Fin 2) : (tower0 M s i).toRingHom.IsIntegral := by
  haveI : Fact s.Prime := ⟨hs⟩
  fin_cases i
  · rw [show (⟨0, by norm_num⟩ : Fin 2) = 0 from rfl, tower0_zero]
    exact towerInclBar_isIntegral (AlgebraicClosure ℚ) _
  · rw [show (⟨1, by norm_num⟩ : Fin 2) = 1 from rfl, tower0_one]
    exact towerSubstBar_isIntegral (AlgebraicClosure ℚ) s _

private theorem coe_tower0_zero (x : ↥(modularFunctionFieldBar M)) :
    ((tower0 M s 0 x : ↥(modularFunctionFieldBar (M * s))) : LaurentSeries (AlgebraicClosure ℚ)) = x := by
  rw [tower0_zero, coe_towerInclBar]

private theorem coe_tower0_one (x : ↥(modularFunctionFieldBar M)) :
    ((tower0 M s 1 x : ↥(modularFunctionFieldBar (M * s))) : LaurentSeries (AlgebraicClosure ℚ)) =
      qExpand (AlgebraicClosure ℚ) s x := by
  rw [tower0_one, coe_towerSubstBar]

variable [NeZero q']

private theorem square_alpha
    (δ : Fin 2 → (↥(modularFunctionFieldBar (M * q')) →ₐ[AlgebraicClosure ℚ] ↥(modularFunctionFieldBar (M * s * q'))))
    (hδα : ∀ x, ((δ 0 x : ↥(modularFunctionFieldBar (M * s * q'))) : LaurentSeries (AlgebraicClosure ℚ)) = x)
    (hδβ : ∀ x, ((δ 1 x : ↥(modularFunctionFieldBar (M * s * q'))) : LaurentSeries (AlgebraicClosure ℚ)) =
      qExpand (AlgebraicClosure ℚ) s x) (i : Fin 2) :
    (δ i).comp (heckeAlphaBar (AlgebraicClosure ℚ) M q') =
      (heckeAlphaBar (AlgebraicClosure ℚ) (M * s) q').comp (tower0 M s i) := by
  apply AlgHom.ext
  intro x
  apply Subtype.ext
  fin_cases i
  · simp only [AlgHom.comp_apply]
    rw [show (⟨0, by norm_num⟩ : Fin 2) = 0 from rfl, hδα, coe_heckeAlphaBar, coe_heckeAlphaBar, coe_tower0_zero]
  · simp only [AlgHom.comp_apply]
    rw [show (⟨1, by norm_num⟩ : Fin 2) = 1 from rfl, hδβ, coe_heckeAlphaBar, coe_heckeAlphaBar, coe_tower0_one]

private theorem square_beta
    (δ : Fin 2 → (↥(modularFunctionFieldBar (M * q')) →ₐ[AlgebraicClosure ℚ] ↥(modularFunctionFieldBar (M * s * q'))))
    (hδα : ∀ x, ((δ 0 x : ↥(modularFunctionFieldBar (M * s * q'))) : LaurentSeries (AlgebraicClosure ℚ)) = x)
    (hδβ : ∀ x, ((δ 1 x : ↥(modularFunctionFieldBar (M * s * q'))) : LaurentSeries (AlgebraicClosure ℚ)) =
      qExpand (AlgebraicClosure ℚ) s x) (i : Fin 2) :
    (δ i).comp (heckeBetaBar (AlgebraicClosure ℚ) M q') =
      (heckeBetaBar (AlgebraicClosure ℚ) (M * s) q').comp (tower0 M s i) := by
  apply AlgHom.ext
  intro x
  apply Subtype.ext
  fin_cases i
  · simp only [AlgHom.comp_apply]
    rw [show (⟨0, by norm_num⟩ : Fin 2) = 0 from rfl, hδα, coe_heckeBetaBar, coe_heckeBetaBar, coe_tower0_zero]
  · simp only [AlgHom.comp_apply]
    rw [show (⟨1, by norm_num⟩ : Fin 2) = 1 from rfl, hδβ, coe_heckeBetaBar, coe_heckeBetaBar, coe_tower0_one,
      qExpand_qExpand, qExpand_qExpand]
    simp only [Nat.mul_comm]

end Level

end TransportGlue

end

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
      (S₁ : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) (M * s)) × Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) (M * s))))
      (S₂ : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M) × Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M))) [DecidableEq ↥S₂]
      (ν : ↥S₁ → ↥S₂) (m : ↥S₁ → ℕ)
      (δ : Fin 2 → (↥(modularFunctionFieldBar (M * q')) →ₐ[AlgebraicClosure ℚ] ↥(modularFunctionFieldBar (M * s * q'))))
      (hδ : ∀ i, (δ i).toRingHom.IsIntegral)
      (hδα : ∀ x, ((δ 0 x : ↥(modularFunctionFieldBar (M * s * q'))) : LaurentSeries (AlgebraicClosure ℚ)) = x)
      (hδβ : ∀ x, ((δ 1 x : ↥(modularFunctionFieldBar (M * s * q'))) : LaurentSeries (AlgebraicClosure ℚ)) =
        qExpand (AlgebraicClosure ℚ) s x)
      (φ : Fin 2 → (↥(modularFunctionFieldC (ResidueField A) M) →ₐ[ResidueField A] ↥(modularFunctionFieldC (ResidueField A) (M * s))))
      (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
      (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC (ResidueField A) (M * s))) : LaurentSeries (ResidueField A)) = x)
      (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC (ResidueField A) (M * s))) : LaurentSeries (ResidueField A)) =
        qExpand (ResidueField A) s x)
      (i : Fin 2) (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (M * s * q')))
      (hclean : ∀ W ∈ D.support,
        frobOnPlacesGeomLevel (ResidueField A) M data₂ hKr₂
            (frobOnPlacesGeomLevel (ResidueField A) M data₂ hKr₂ ((P₁.reduceFst W).restrictAlong (φ i) (hφ i))) ≠
          (P₁.reduceFst W).restrictAlong (φ i) (hφ i) ∧
        frobOnPlacesGeomLevel (ResidueField A) M data₂ hKr₂
            (frobOnPlacesGeomLevel (ResidueField A) M data₂ hKr₂ ((P₁.reduceSnd W).restrictAlong (φ i) (hφ i))) ≠
          (P₁.reduceSnd W).restrictAlong (φ i) (hφ i)),
      P₂.IsGoodDiv (Divisor.pushforwardAlong (δ i) (hδ i) D) ∧
        P₂.glueData S₂ (Divisor.pushforwardAlong (δ i) (hδ i) D) =
          GluingData.pushforwardMap S₁ S₂ ν m (φ i) (hφ i) (P₁.glueData S₁ D) := by

  haveI : NeZero q' := ⟨hq'.ne_zero⟩
  haveI : Fact q'.Prime := ⟨hq'⟩
  haveI : CharP (ResidueField A) q' := ValuationSubring.charP_residueField_of_liesOverPrime_def hq' hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (M * s)
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A M
  intro data₁ hKr₁ hα₁ hβ₁ P₁ R₁ hmodel₁ hO₁ data₂ hKr₂ hα₂ hβ₂ P₂ R₂ hmodel₂ hO₂ S₁ S₂ _ ν m δ hδ hδα hδβ φ hφ
    hφα hφβ i D hclean

  have hK := ModularCurve.PlaceSpecialization.sp_restrictAlong_eq_restrictAlong_sp_of_isModel M s q' hs hq' hsq' hq'M
    A hA data₁ hKr₁ hα₁ hβ₁ P₁ R₁ hmodel₁ hO₁ data₂ hKr₂ hα₂ hβ₂ P₂ R₂ hmodel₂ hO₂ (TransportGlue.tower0 M s)
    (TransportGlue.tower0_isIntegral M s hs) (TransportGlue.coe_tower0_zero M s) (TransportGlue.coe_tower0_one M s)
    φ hφ hφα hφβ i
  have hF := ModularCurve.frobOnPlacesGeomLevel_restrictAlong_degeneracyPair M s q' (ResidueField A) data₁ hKr₁
    data₂ hKr₂ φ hφ hφα hφβ i
  have hsqα := TransportGlue.square_alpha M s q' δ hδα hδβ i
  have hsqβ := TransportGlue.square_beta M s q' δ hδα hδβ i
  have htow := TransportGlue.tower0_isIntegral M s hs i

  have hR1 : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (M * s * q')),
      frobOnPlacesGeomLevel (ResidueField A) M data₂ hKr₂
          (frobOnPlacesGeomLevel (ResidueField A) M data₂ hKr₂ ((P₁.reduceFst W).restrictAlong (φ i) (hφ i))) ≠
        (P₁.reduceFst W).restrictAlong (φ i) (hφ i) →
      P₂.reduceFst (W.restrictAlong (δ i) (hδ i)) = (P₁.reduceFst W).restrictAlong (φ i) (hφ i) := by
    intro W hW
    unfold PlaceSpecialization.reduceFst at hW ⊢
    rw [Place.restrictAlong_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) M q') (δ i) hα₂ (hδ i)
        (TransportGlue.tg_comp_isIntegral _ _ hα₂ (hδ i)) W,
      Place.restrictAlong_congr hsqα _ (TransportGlue.tg_comp_isIntegral _ _ htow hα₁),
      ← Place.restrictAlong_restrictAlong (TransportGlue.tower0 M s i) (heckeAlphaBar (AlgebraicClosure ℚ) (M * s) q')
        htow hα₁ (TransportGlue.tg_comp_isIntegral _ _ htow hα₁) W]
    exact hK _ hW

  have hR2 : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (M * s * q')),
      frobOnPlacesGeomLevel (ResidueField A) M data₂ hKr₂
          (frobOnPlacesGeomLevel (ResidueField A) M data₂ hKr₂ ((P₁.reduceSnd W).restrictAlong (φ i) (hφ i))) ≠
        (P₁.reduceSnd W).restrictAlong (φ i) (hφ i) →
      P₂.reduceSnd (W.restrictAlong (δ i) (hδ i)) = (P₁.reduceSnd W).restrictAlong (φ i) (hφ i) := by
    intro W hW
    unfold PlaceSpecialization.reduceSnd at hW ⊢
    rw [Place.restrictAlong_restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) M q') (δ i) hβ₂ (hδ i)
        (TransportGlue.tg_comp_isIntegral _ _ hβ₂ (hδ i)) W,
      Place.restrictAlong_congr hsqβ _ (TransportGlue.tg_comp_isIntegral _ _ htow hβ₁),
      ← Place.restrictAlong_restrictAlong (TransportGlue.tower0 M s i) (heckeBetaBar (AlgebraicClosure ℚ) (M * s) q')
        htow hβ₁ (TransportGlue.tg_comp_isIntegral _ _ htow hβ₁) W]
    exact hK _ hW

  let Clean : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (M * s * q')) → Prop := fun W =>
    frobOnPlacesGeomLevel (ResidueField A) M data₂ hKr₂
        (frobOnPlacesGeomLevel (ResidueField A) M data₂ hKr₂ ((P₁.reduceFst W).restrictAlong (φ i) (hφ i))) ≠
      (P₁.reduceFst W).restrictAlong (φ i) (hφ i) ∧
    frobOnPlacesGeomLevel (ResidueField A) M data₂ hKr₂
        (frobOnPlacesGeomLevel (ResidueField A) M data₂ hKr₂ ((P₁.reduceSnd W).restrictAlong (φ i) (hφ i))) ≠
      (P₁.reduceSnd W).restrictAlong (φ i) (hφ i)

  have hT1 : ∀ W, Clean W → P₁.IsStrictFst W → P₂.IsStrictFst (W.restrictAlong (δ i) (hδ i)) := by
    intro W hC hW
    refine ⟨?_, ?_⟩
    · rw [hR1 W hC.1, hR2 W hC.2, hF, hW.1]
    · rw [hR1 W hC.1]
      exact hC.1

  have hT2 : ∀ W, Clean W → P₁.IsStrictSnd W → P₂.IsStrictSnd (W.restrictAlong (δ i) (hδ i)) := by
    intro W hC hW
    refine ⟨?_, ?_⟩
    · rw [hR1 W hC.1, hR2 W hC.2, hF, hW.1]
    · rw [hR2 W hC.2]
      exact hC.2

  have hG : ∀ W, Clean W → P₁.IsStrictFst W ∨ P₁.IsStrictSnd W := by
    intro W hC
    rw [ModularCurve.PlaceSpecialization.isStrictFst_or_isStrictSnd_iff]
    intro hfix
    apply hC.1
    rw [hF, hF, hfix]

  have hdegk : ∀ w : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) (M * s)), w.deg = 1 :=
    fun w => ModularCurve.place_deg_eq_one_of_isAlgClosed (ResidueField A) (M * s) w

  have hsingle : ∀ (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (M * s * q'))) (c : ℤ), Clean W →
      P₂.IsGoodDiv (Divisor.pushforwardAlong (δ i) (hδ i) (Finsupp.single W c)) ∧
        P₂.glueData S₂ (Divisor.pushforwardAlong (δ i) (hδ i) (Finsupp.single W c)) =
          GluingData.pushforwardMap S₁ S₂ ν m (φ i) (hφ i) (P₁.glueData S₁ (Finsupp.single W c)) := by
    intro W c hC
    rw [TransportGlue.tg_pushforwardAlong_single (δ i) (hδ i) W (deg_eq_one_modularFunctionFieldBar _ W) c]
    have hmem : ∀ V ∈ (Finsupp.single (W.restrictAlong (δ i) (hδ i)) c).support, V = W.restrictAlong (δ i) (hδ i) :=
      fun V hV => Finset.mem_singleton.mp (Finsupp.support_single_subset hV)
    rcases hG W hC with hfst | hsnd
    · refine ⟨fun V hV => ?_, ?_⟩
      · rw [hmem V hV]
        exact Or.inl (hT1 W hC hfst)
      · rw [TransportGlue.tg_glueData_single_fst P₂ S₂ _ (hT1 W hC hfst) c,
          TransportGlue.tg_glueData_single_fst P₁ S₁ W hfst c, GluingData.pushforwardMap_apply, map_zero, map_zero,
          TransportGlue.tg_pushforwardAlong_single (φ i) (hφ i) _ (hdegk _) c, hR1 W hC.1]
    · refine ⟨fun V hV => ?_, ?_⟩
      · rw [hmem V hV]
        exact Or.inr (hT2 W hC hsnd)
      · rw [TransportGlue.tg_glueData_single_snd P₂ S₂ _ (hT2 W hC hsnd) c,
          TransportGlue.tg_glueData_single_snd P₁ S₁ W hsnd c, GluingData.pushforwardMap_apply, map_zero, map_zero,
          TransportGlue.tg_pushforwardAlong_single (φ i) (hφ i) _ (hdegk _) c, hR2 W hC.2]

  have hclean' : ∀ W ∈ D.support, Clean W := hclean
  clear hclean
  revert hclean'
  induction D using Finsupp.induction with
  | zero =>
    intro _
    refine ⟨?_, ?_⟩
    · rw [map_zero]
      exact P₂.isGoodDiv_zero
    · rw [map_zero, P₂.glueData_zero, P₁.glueData_zero, map_zero]
  | single_add W c D hWD hc ih =>
    intro hcl
    have hCW : Clean W := by
      apply hcl
      rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.notMem_support_iff.mp hWD,
        add_zero]
      exact hc
    have hclD : ∀ V ∈ D.support, Clean V := by
      classical
      intro V hV
      apply hcl
      have hne : ¬ W = V := fun h => hWD (h ▸ hV)
      rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply, if_neg hne, zero_add]
      exact Finsupp.mem_support_iff.mp hV
    obtain ⟨hgood₁, hglue₁⟩ := hsingle W c hCW
    obtain ⟨hgood₂, hglue₂⟩ := ih hclD
    exact ⟨TransportGlue.tg_good_step P₂ (Divisor.pushforwardAlong (δ i) (hδ i)) _ _ hgood₁ hgood₂,
      TransportGlue.tg_glue_step P₂ S₂ P₁ S₁ (Divisor.pushforwardAlong (δ i) (hδ i))
        (GluingData.pushforwardMap S₁ S₂ ν m (φ i) (hφ i)) _ _ hglue₁ hglue₂⟩

end S_ModularCurve_PlaceSpecialization_isGoodDiv_pushforwardAlong_and_glueData_eq_of_isModel
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_isGoodDiv_pushforwardAlong_and_glueData_eq_of_isModel (solution)
