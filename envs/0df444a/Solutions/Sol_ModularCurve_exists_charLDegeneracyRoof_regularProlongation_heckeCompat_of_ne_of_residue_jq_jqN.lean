-- Prove2me | solution 1 for ModularCurve.exists_charLDegeneracyRoof_regularProlongation_heckeCompat_of_ne_of_residue_jq_jqN
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/a7b64c07-ccce-5762-9774-4d24b867b27e

import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_WeierstrassCurve_ReductionMap
import Theorems.Thm_ModularCurve_exists_regularProlongation_placeMap_modularFunctionFieldFullC_of_not_dvd
import Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_AlgebraicCurve_RegularProlongation_mem_adjoin_iff_mem_integers_iff_of_transcendental_residue
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_relfinrank_full_eq_dedekindPsi
import Theorems.Thm_ModularCurve_relfinrank_laurentBaseChange_modularFunctionFieldFull
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_AlgebraicCurve_finrankAlong_eq_relfinrank_fieldRange
import Theorems.Thm_ModularCurve_laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_finiteAlong_heckeBetaBar_of_prime
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_AlgebraicCurve_fundamentalIdentityAlong
import Theorems.Thm_ModularCurve_finiteAlong_heckeBetaC
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_relfinrank_modularFunctionFieldFullC_mul_dedekindPsi
import Theorems.Thm_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff
import Theorems.Thm_ModularCurve_separableAlong_heckeAlphaC_heckeBetaC
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaBar_of_prime
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_charLDegeneracyRoof_regularProlongation_heckeCompat_of_ne_of_residue_jq_jqN
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def"

p2m_open "ModularCurve~dedekindPsi_pos~transcendental_jqNModC AlgebraicCurve IsLocalRing"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
set_option Elab.async false

namespace RoofRigidity

section Kit

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F F' : Type*} [Field F] [Field F'] [Algebra L F] [Algebra L F']
variable {Fb Fb' : Type*} [Field Fb] [Field Fb']
variable [Algebra (ResidueField A) Fb] [Algebra (ResidueField A) Fb']

private theorem isUnit_mk_iff (V : ValuationSubring F) {x : F} (hx : x ∈ V) :
    IsUnit (⟨x, hx⟩ : V) ↔ x ≠ 0 ∧ x⁻¹ ∈ V := by
  constructor
  · rintro ⟨u, hu⟩
    have key : (⟨x, hx⟩ : V) * ↑u⁻¹ = 1 := by
      rw [← hu]
      exact u.mul_inv
    have keyF := congrArg Subtype.val key
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at keyF
    refine ⟨left_ne_zero_of_mul_eq_one keyF, ?_⟩
    rw [inv_eq_of_mul_eq_one_right keyF]
    exact SetLike.coe_mem _
  · rintro ⟨hne, hinv⟩
    exact ⟨⟨⟨x, hx⟩, ⟨x⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hne),
      Subtype.ext (inv_mul_cancel₀ hne)⟩, rfl⟩

private theorem residue_congr (R : RegularProlongation A F Fb) {x y : R.integers}
    (h : (x : F) = (y : F)) : R.residue x = R.residue y := by
  rw [Subtype.ext h]

private def comapIntegers (φ : F →ₐ[L] F') (R' : RegularProlongation A F' Fb') :
    ValuationSubring F :=
  R'.integers.comap (φ : F →+* F')

private theorem mem_comapIntegers {φ : F →ₐ[L] F'} {R' : RegularProlongation A F' Fb'} {x : F} :
    x ∈ comapIntegers φ R' ↔ φ x ∈ R'.integers :=
  ValuationSubring.mem_comap

private theorem isUnit_comap_iff (φ : F →ₐ[L] F') (R' : RegularProlongation A F' Fb') {x : F}
    (hx : x ∈ comapIntegers φ R') :
    IsUnit (⟨x, hx⟩ : comapIntegers φ R') ↔
      IsUnit (⟨φ x, mem_comapIntegers.mp hx⟩ : R'.integers) := by
  rw [isUnit_mk_iff, isUnit_mk_iff]
  have hinj : Function.Injective φ := fun a b h => (φ : F →+* F').injective h
  constructor
  · rintro ⟨hne, hinv⟩
    exact ⟨fun h => hne (hinj (by rw [h, map_zero])),
      by rw [← map_inv₀]; exact mem_comapIntegers.mp hinv⟩
  · rintro ⟨hne, hinv⟩
    exact ⟨fun h => hne (by rw [h, map_zero]),
      mem_comapIntegers.mpr (by rw [map_inv₀]; exact hinv)⟩

private def toIntegers (φ : F →ₐ[L] F') (R' : RegularProlongation A F' Fb') :
    comapIntegers φ R' →+* R'.integers where
  toFun x := ⟨φ x, mem_comapIntegers.mp x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

private theorem coe_toIntegers (φ : F →ₐ[L] F') (R' : RegularProlongation A F' Fb')
    (x : comapIntegers φ R') : ((toIntegers φ R' x : R'.integers) : F') = φ x := rfl

private scoped instance isLocalHom_toIntegers (φ : F →ₐ[L] F') (R' : RegularProlongation A F' Fb') :
    IsLocalHom (toIntegers φ R') := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨x, hx0⟩ := x
  exact (isUnit_comap_iff φ R' hx0).mpr hx

private def comapConst (φ : F →ₐ[L] F') (R' : RegularProlongation A F' Fb') :
    A →+* comapIntegers φ R' where
  toFun a := ⟨algebraMap L F a, mem_comapIntegers.mpr (by
    rw [AlgHom.commutes]
    exact (R'.algebraMap_mem_iff a).mpr a.2)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

private theorem coe_comapConst (φ : F →ₐ[L] F') (R' : RegularProlongation A F' Fb') (a : A) :
    ((comapConst φ R' a : comapIntegers φ R') : F) = algebraMap L F a := rfl

private scoped instance isLocalHom_comapConst (φ : F →ₐ[L] F') (R' : RegularProlongation A F' Fb') :
    IsLocalHom (comapConst φ R') := by
  refine ⟨fun a ha => ?_⟩
  have ha' := (isUnit_comap_iff φ R' (comapConst φ R' a).2).mp ha
  rw [isUnit_mk_iff] at ha'
  obtain ⟨hne, hinv⟩ := ha'
  rw [coe_comapConst, AlgHom.commutes] at hne hinv
  rw [← map_inv₀, R'.algebraMap_mem_iff] at hinv
  have hne' : (a : L) ≠ 0 := fun h => hne (by rw [h, map_zero])
  have key : IsUnit (⟨(a : L), a.2⟩ : A) := (isUnit_mk_iff A a.2).mpr ⟨hne', hinv⟩
  exact key

private noncomputable scoped instance comapAlgebra (φ : F →ₐ[L] F')
    (R' : RegularProlongation A F' Fb') :
    Algebra (ResidueField A) (ResidueField (comapIntegers φ R')) :=
  (ResidueField.map (comapConst φ R')).toAlgebra

private theorem comapAlgebra_algebraMap (φ : F →ₐ[L] F') (R' : RegularProlongation A F' Fb')
    (a : A) :
    algebraMap (ResidueField A) (ResidueField (comapIntegers φ R')) (residue A a)
      = residue (comapIntegers φ R') (comapConst φ R' a) := by
  show ResidueField.map (comapConst φ R') (residue A a) = _
  rw [ResidueField.map_residue]

private noncomputable def _root_.RoofRigidity.comap (φ : F →ₐ[L] F') (R' : RegularProlongation A F' Fb') :
    RegularProlongation A F (ResidueField (comapIntegers φ R')) where
  integers := comapIntegers φ R'
  residue := IsLocalRing.residue (comapIntegers φ R')
  algebraMap_mem_iff x := by
    rw [mem_comapIntegers, AlgHom.commutes, R'.algebraMap_mem_iff]
  residue_surjective := IsLocalRing.residue_surjective
  ker_residue := IsLocalRing.ker_residue
  residue_algebraMap a := by
    rw [comapAlgebra_algebraMap]
    rfl
  exists_smul_mem f hf := by
    have hf' : φ f ≠ 0 := fun h0 => hf ((φ : F →+* F').injective (by rw [map_zero]; exact h0))
    obtain ⟨c, hc, hres⟩ := R'.exists_smul_mem (φ f) hf'
    have hc' : c • f ∈ comapIntegers φ R' := by
      rw [mem_comapIntegers, map_smul φ c f]
      exact hc
    refine ⟨c, hc', ?_⟩
    rw [residue_ne_zero_iff_isUnit, isUnit_comap_iff]
    have hu := R'.isUnit_of_residue_ne_zero hres
    have heq : (⟨c • φ f, hc⟩ : R'.integers) = ⟨φ (c • f), mem_comapIntegers.mp hc'⟩ :=
      Subtype.ext (map_smul φ c f).symm
    rwa [heq] at hu

p2m_export "RoofRigidity" "comap"
private theorem comap_residue (φ : F →ₐ[L] F') (R' : RegularProlongation A F' Fb')
    (x : comapIntegers φ R') : (comap φ R').residue x = residue (comapIntegers φ R') x := rfl

private noncomputable def residueLift (φ : F →ₐ[L] F') (R' : RegularProlongation A F' Fb') :
    ResidueField (comapIntegers φ R') →ₐ[ResidueField A] Fb' :=
  haveI : IsLocalHom (R'.residue.comp (toIntegers φ R')) :=
    ⟨fun x hx => isUnit_of_map_unit (toIntegers φ R') x
      (R'.isUnit_of_residue_ne_zero (f := toIntegers φ R' x) hx.ne_zero)⟩
  { ResidueField.lift (R'.residue.comp (toIntegers φ R')) with
    commutes' := fun c => by
      obtain ⟨a, rfl⟩ := residue_surjective c
      show ResidueField.lift _ (algebraMap _ _ (residue A a)) = _
      rw [comapAlgebra_algebraMap, ResidueField.lift_residue_apply, RingHom.comp_apply,
        ← R'.residue_algebraMap a]
      exact residue_congr R' (by
        show φ (algebraMap L F (a : L)) = algebraMap L F' (a : L)
        exact φ.commutes _) }

private theorem residueLift_residue (φ : F →ₐ[L] F') (R' : RegularProlongation A F' Fb')
    (x : comapIntegers φ R') :
    residueLift φ R' ((comap φ R').residue x) = R'.residue (toIntegers φ R' x) := rfl

private theorem transcendental_comap_residue (φ : F →ₐ[L] F')
    (R' : RegularProlongation A F' Fb') (x : comapIntegers φ R')
    (h : Transcendental (ResidueField A) (R'.residue (toIntegers φ R' x))) :
    Transcendental (ResidueField A) ((comap φ R').residue x) := by
  intro halg
  apply h
  rw [← residueLift_residue]
  exact halg.algHom (residueLift φ R')

private def transfer (R : RegularProlongation A F Fb) (φ : F →ₐ[L] F')
    (R' : RegularProlongation A F' Fb') (hV : comapIntegers φ R' = R.integers) :
    R.integers →+* R'.integers :=
  (toIntegers φ R').comp
    { toFun := fun x => ⟨x, by rw [hV]; exact x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

private theorem coe_transfer (R : RegularProlongation A F Fb) (φ : F →ₐ[L] F')
    (R' : RegularProlongation A F' Fb') (hV : comapIntegers φ R' = R.integers)
    (x : R.integers) : ((transfer R φ R' hV x : R'.integers) : F') = φ x := rfl

private theorem ker_le_ker_transfer (R : RegularProlongation A F Fb) (φ : F →ₐ[L] F')
    (R' : RegularProlongation A F' Fb') (hV : comapIntegers φ R' = R.integers) :
    RingHom.ker R.residue ≤ RingHom.ker (R'.residue.comp (transfer R φ R' hV)) := by
  intro x hx
  rw [R.ker_residue] at hx
  rw [RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker, R'.ker_residue]
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
  intro hu
  apply hx
  have hx' : (x : F) ∈ comapIntegers φ R' := by rw [hV]; exact x.2
  have hu' : IsUnit (⟨(x : F), hx'⟩ : comapIntegers φ R') := (isUnit_comap_iff φ R' hx').mpr hu
  rw [isUnit_mk_iff] at hu'
  obtain ⟨hne, hinv⟩ := hu'
  rw [hV] at hinv
  have key : IsUnit (⟨(x : F), x.2⟩ : R.integers) :=
    (isUnit_mk_iff R.integers x.2).mpr ⟨hne, hinv⟩
  exact key

private noncomputable def residueHom (R : RegularProlongation A F Fb) (φ : F →ₐ[L] F')
    (R' : RegularProlongation A F' Fb') (hV : comapIntegers φ R' = R.integers) :
    Fb →ₐ[ResidueField A] Fb' :=
  { (R.residue.liftOfSurjective R.residue_surjective)
      ⟨R'.residue.comp (transfer R φ R' hV), ker_le_ker_transfer R φ R' hV⟩ with
    commutes' := fun c => by
      obtain ⟨a, rfl⟩ := residue_surjective c
      show (R.residue.liftOfSurjective R.residue_surjective) _ (algebraMap _ _ (residue A a)) = _
      rw [← R.residue_algebraMap a, RingHom.liftOfSurjective_comp_apply,
        ← R'.residue_algebraMap a]
      exact residue_congr R' (by
        show φ (algebraMap L F (a : L)) = algebraMap L F' (a : L)
        exact φ.commutes _) }

private theorem residueHom_residue (R : RegularProlongation A F Fb) (φ : F →ₐ[L] F')
    (R' : RegularProlongation A F' Fb') (hV : comapIntegers φ R' = R.integers) (x : R.integers) :
    residueHom R φ R' hV (R.residue x) = R'.residue (transfer R φ R' hV x) :=
  RingHom.liftOfSurjective_comp_apply R.residue R.residue_surjective _ x

end Kit

section Degree

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

private theorem comap_val_adjoin_simple (M : IntermediateField K E) (z : M) :
    (IntermediateField.adjoin K ({(z : E)} : Set E)).comap M.val
      = IntermediateField.adjoin K ({z} : Set M) := by
  ext y
  change (y : E) ∈ IntermediateField.adjoin K ({(z : E)} : Set E) ↔ _
  rw [← IntermediateField.lift_adjoin_simple K M z]
  exact IntermediateField.mem_lift y

private theorem finrank_adjoin_simple_eq_relfinrank (M : IntermediateField K E) (z : M) :
    Module.finrank (IntermediateField.adjoin K ({z} : Set M)) M
      = IntermediateField.relfinrank (IntermediateField.adjoin K ({(z : E)} : Set E)) M := by
  rw [← comap_val_adjoin_simple M z, IntermediateField.finrank_comap,
    IntermediateField.fieldRange_val]

end Degree

section LevelN

private theorem dedekindPsi_pos (N : ℕ) [NeZero N] : 0 < dedekindPsi N := by
  unfold dedekindPsi
  have h1 : (1 : ℕ) ∈ N.divisors.filter Squarefree :=
    Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr (NeZero.ne N), squarefree_one⟩
  have hle : N / 1 ≤ ∑ d ∈ N.divisors with Squarefree d, N / d :=
    Finset.single_le_sum (f := fun d => N / d) (fun _ _ => Nat.zero_le _) h1
  rw [Nat.div_one] at hle
  exact lt_of_lt_of_le (Nat.pos_of_ne_zero (NeZero.ne N)) hle

private noncomputable def jB (N : ℕ) [NeZero N] : modularFunctionFieldBar N :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩

private noncomputable def jNB (N : ℕ) [NeZero N] : modularFunctionFieldBar N :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (dvd_refl N))⟩

private theorem coe_jB (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ)) :
    ((jB N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
      = coeffMap A.subtype (jqModC A) := by
  show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (jqModC ℚ) = _
  rw [coeffMap_jqModC, coeffMap_jqModC]

private theorem coe_jNB (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ)) :
    ((jNB N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
      = coeffMap A.subtype (jqNModC A N) := by
  show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (jqNModC ℚ N) = _
  rw [coeffMap_jqNModC, coeffMap_jqNModC]

private theorem finrank_adjoin_jB (N : ℕ) [NeZero N] :
    Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({jB N} : Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N)
      = dedekindPsi N := by
  refine (finrank_adjoin_simple_eq_relfinrank (modularFunctionFieldBar N) (jB N)).trans ?_
  change IntermediateField.relfinrank (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({coeffEmb (AlgebraicClosure ℚ) jq} : Set (LaurentSeries (AlgebraicClosure ℚ))))
    (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) = _
  rw [relfinrank_laurentBaseChange_modularFunctionFieldFull, relfinrank_full_eq_dedekindPsi]

private theorem finrank_adjoin_jqModC (k : Type*) [Field k] (N : ℕ) [NeZero N]
    (p : ℕ) [Fact p.Prime] [CharP k p] (hpN : ¬ p ∣ N) :
    Module.finrank (IntermediateField.adjoin k
        ({(⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)} :
          Set (modularFunctionFieldC k N))) (modularFunctionFieldC k N)
      = dedekindPsi N := by
  refine (finrank_adjoin_simple_eq_relfinrank (modularFunctionFieldC k N)
    ⟨jqModC k, jqModC_mem k N⟩).trans ?_
  change IntermediateField.relfinrank (IntermediateField.adjoin k
      ({jqModC k} : Set (LaurentSeries k))) (modularFunctionFieldC k N) = _
  exact relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi k N p hpN

private theorem transcendental_jqModC_mem (k : Type*) [Field k] (N : ℕ) [NeZero N] :
    Transcendental k (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) :=
  fun halg => transcendental_jqModC k (halg.algHom (modularFunctionFieldC k N).val)

private theorem transcendental_jqNModC (k : Type*) [Field k] (n : ℕ) [NeZero n] :
    Transcendental k (jqNModC k n) := fun halg =>
  transcendental_jqModC k ((isAlgebraic_algHom_iff (qExpandAlgHomC k n)
    (fun _ _ h => qExpand_injective n h) (a := jqModC k)).mp halg)

end LevelN

section Rigidity

variable (N : ℕ) [NeZero N]
variable (A : ValuationSubring (AlgebraicClosure ℚ))

private theorem comapIntegers_eq
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField ↥A) p] (hpN : ¬ p ∣ N)
    (R₁ : RegularProlongation A (modularFunctionFieldBar N)
      (modularFunctionFieldC (ResidueField ↥A) N))
    (hj : ∃ h : jB N ∈ R₁.integers,
      R₁.residue ⟨_, h⟩ = ⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) N⟩)
    {Fb' : Type*} [Field Fb'] [Algebra (ResidueField ↥A) Fb'] {M : ℕ} [NeZero M]
    (R' : RegularProlongation A (modularFunctionFieldBar M) Fb')
    (φ : modularFunctionFieldBar N →ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar M)
    (hφj : φ (jB N) ∈ R'.integers)
    (htr : Transcendental (ResidueField ↥A) (R'.residue ⟨φ (jB N), hφj⟩)) :
    comapIntegers φ R' = R₁.integers := by
  obtain ⟨hj1, hj2⟩ := hj
  have hf₂ : jB N ∈ (comap φ R').integers := mem_comapIntegers.mpr hφj
  have htr₁ : Transcendental (ResidueField ↥A) (R₁.residue ⟨jB N, hj1⟩) := by
    rw [hj2]
    exact transcendental_jqModC_mem (ResidueField ↥A) N
  have htr₂ : Transcendental (ResidueField ↥A) ((comap φ R').residue ⟨jB N, hf₂⟩) := by
    apply transcendental_comap_residue φ R' ⟨jB N, hf₂⟩
    have e : R'.residue (toIntegers φ R' ⟨jB N, hf₂⟩) = R'.residue ⟨φ (jB N), hφj⟩ :=
      residue_congr R' rfl
    rw [e]
    exact htr
  have hV : ∀ e : modularFunctionFieldBar N,
      e ∈ IntermediateField.adjoin (AlgebraicClosure ℚ) {((⟨jB N, hj1⟩ : R₁.integers) :
        modularFunctionFieldBar N)} → (e ∈ comapIntegers φ R' ↔ e ∈ R₁.integers) :=
    fun e he =>
      (RegularProlongation.mem_adjoin_iff_mem_integers_iff_of_transcendental_residue A R₁
        (comap φ R') (jB N) hj1 hf₂ htr₁ htr₂ e he).symm
  have hdeg1 : Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({((⟨jB N, hj1⟩ : R₁.integers) : modularFunctionFieldBar N)} :
        Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N) = dedekindPsi N :=
    finrank_adjoin_jB N
  have hdeg2 : Module.finrank (IntermediateField.adjoin (ResidueField ↥A)
      ({R₁.residue ⟨jB N, hj1⟩} : Set (modularFunctionFieldC (ResidueField ↥A) N)))
      (modularFunctionFieldC (ResidueField ↥A) N) = dedekindPsi N := by
    rw [hj2]
    exact finrank_adjoin_jqModC (ResidueField ↥A) N p hpN
  exact RegularProlongation.eq_integers_of_forall_mem_adjoin_iff A R₁ ⟨jB N, hj1⟩ htr₁
    (by rw [hdeg2]; exact dedekindPsi_pos N) (by rw [hdeg1, hdeg2]) (comapIntegers φ R') hV

private theorem residue_map_eq
    (R₁ : RegularProlongation A (modularFunctionFieldBar N)
      (modularFunctionFieldC (ResidueField ↥A) N))
    {Fb' : Type*} [Field Fb'] [Algebra (ResidueField ↥A) Fb'] {M : ℕ} [NeZero M]
    (R' : RegularProlongation A (modularFunctionFieldBar M) Fb')
    (φ : modularFunctionFieldBar N →ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar M)
    (φC : modularFunctionFieldC (ResidueField ↥A) N →ₐ[ResidueField ↥A] Fb')
    (hV : comapIntegers φ R' = R₁.integers)
    (h1 : ∃ (h : jB N ∈ R₁.integers) (h' : φ (jB N) ∈ R'.integers),
      R₁.residue ⟨_, h⟩ = ⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) N⟩ ∧
      R'.residue ⟨_, h'⟩ = φC (R₁.residue ⟨_, h⟩))
    (h2 : ∃ (h : jNB N ∈ R₁.integers) (h' : φ (jNB N) ∈ R'.integers),
      R₁.residue ⟨_, h⟩ = ⟨jqNModC (ResidueField ↥A) N, jqNModC_mem (ResidueField ↥A) N⟩ ∧
      R'.residue ⟨_, h'⟩ = φC (R₁.residue ⟨_, h⟩))
    (f : R₁.integers) :
    ∃ h : φ (f : modularFunctionFieldBar N) ∈ R'.integers,
      R'.residue ⟨_, h⟩ = φC (R₁.residue f) := by
  obtain ⟨hj1, hj1', hjres, hjφ⟩ := h1
  obtain ⟨hn1, hn1', hnres, hnφ⟩ := h2
  have hτ : residueHom R₁ φ R' hV = φC := by
    refine IntermediateField.algHom_ext_of_eq_adjoin (ResidueField ↥A)
      (s := ({jqModC (ResidueField ↥A), jqNModC (ResidueField ↥A) N} :
        Set (LaurentSeries (ResidueField ↥A))))
      rfl (fun x hx => ?_)
    rcases hx with rfl | rfl
    · have e1 : residueHom R₁ φ R' hV (R₁.residue ⟨jB N, hj1⟩) = φC (R₁.residue ⟨jB N, hj1⟩) := by
        rw [residueHom_residue, ← hjφ]
        exact residue_congr R' rfl
      rw [hjres] at e1
      exact e1
    · have e1 : residueHom R₁ φ R' hV (R₁.residue ⟨jNB N, hn1⟩)
          = φC (R₁.residue ⟨jNB N, hn1⟩) := by
        rw [residueHom_residue, ← hnφ]
        exact residue_congr R' rfl
      rw [hnres] at e1
      exact e1
  have hmem : φ (f : modularFunctionFieldBar N) ∈ R'.integers := by
    have : (f : modularFunctionFieldBar N) ∈ comapIntegers φ R' := by rw [hV]; exact f.2
    exact mem_comapIntegers.mp this
  refine ⟨hmem, ?_⟩
  rw [← hτ, residueHom_residue]
  exact residue_congr R' rfl

private theorem residue_heckeAlphaBar_eq (ℓ : ℕ) [Fact ℓ.Prime]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField ↥A) p] (hpN : ¬ p ∣ N)
    (R₁ : RegularProlongation A (modularFunctionFieldBar N)
      (modularFunctionFieldC (ResidueField ↥A) N))
    (hj : ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
        ∈ R₁.integers,
      R₁.residue ⟨_, h⟩
        = ⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) N⟩)
    (hjN : ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full N (dvd_refl N))⟩ : modularFunctionFieldBar N)
        ∈ R₁.integers,
      R₁.residue ⟨_, h⟩
        = ⟨jqNModC (ResidueField ↥A) N, jqNModC_mem (ResidueField ↥A) N⟩)
    (Rℓ : RegularProlongation A (modularFunctionFieldBar (N * ℓ))
        (charLDegeneracyRoof (ResidueField ↥A) N ℓ))
    (hcoef : ∀ (y : LaurentSeries ↥A)
        (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar (N * ℓ)),
      ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar (N * ℓ)) ∈ Rℓ.integers,
        ((Rℓ.residue ⟨_, hint⟩ : charLDegeneracyRoof (ResidueField ↥A) N ℓ)
            : LaurentSeries (ResidueField ↥A))
          = coeffMap (IsLocalRing.residue ↥A) y) :
    ∀ f : R₁.integers,
      ∃ h : heckeAlphaBar (AlgebraicClosure ℚ) N ℓ (f : modularFunctionFieldBar N)
          ∈ Rℓ.integers,
        Rℓ.residue ⟨_, h⟩ = heckeAlphaC (ResidueField ↥A) N ℓ (R₁.residue f) := by

  have hyj : coeffMap A.subtype (jqModC A) ∈ modularFunctionFieldBar (N * ℓ) := by
    rw [← coe_jB N A, ← coe_heckeAlphaBar N ℓ (jB N)]
    exact SetLike.coe_mem _
  have hyn : coeffMap A.subtype (jqNModC A N) ∈ modularFunctionFieldBar (N * ℓ) := by
    rw [← coe_jNB N A, ← coe_heckeAlphaBar N ℓ (jNB N)]
    exact SetLike.coe_mem _
  obtain ⟨hintj, hresj⟩ := hcoef (jqModC A) hyj
  obtain ⟨hintn, hresn⟩ := hcoef (jqNModC A N) hyn
  have ej : (⟨coeffMap A.subtype (jqModC A), hyj⟩ : modularFunctionFieldBar (N * ℓ))
      = heckeAlphaBar (AlgebraicClosure ℚ) N ℓ (jB N) :=
    Subtype.ext (by rw [coe_heckeAlphaBar, coe_jB N A])
  have en : (⟨coeffMap A.subtype (jqNModC A N), hyn⟩ : modularFunctionFieldBar (N * ℓ))
      = heckeAlphaBar (AlgebraicClosure ℚ) N ℓ (jNB N) :=
    Subtype.ext (by rw [coe_heckeAlphaBar, coe_jNB N A])
  have hφj : heckeAlphaBar (AlgebraicClosure ℚ) N ℓ (jB N) ∈ Rℓ.integers := ej ▸ hintj
  have hφn : heckeAlphaBar (AlgebraicClosure ℚ) N ℓ (jNB N) ∈ Rℓ.integers := en ▸ hintn
  have hresj' : Rℓ.residue ⟨_, hφj⟩
      = heckeAlphaC (ResidueField ↥A) N ℓ ⟨jqModC (ResidueField ↥A), jqModC_mem _ N⟩ := by
    apply Subtype.ext
    rw [coe_heckeAlphaC, residue_congr Rℓ (show ((⟨_, hφj⟩ : Rℓ.integers) : modularFunctionFieldBar
      (N * ℓ)) = ((⟨_, hintj⟩ : Rℓ.integers) : modularFunctionFieldBar (N * ℓ)) from ej.symm),
      hresj, coeffMap_jqModC]
  have hresn' : Rℓ.residue ⟨_, hφn⟩
      = heckeAlphaC (ResidueField ↥A) N ℓ ⟨jqNModC (ResidueField ↥A) N, jqNModC_mem _ N⟩ := by
    apply Subtype.ext
    rw [coe_heckeAlphaC, residue_congr Rℓ (show ((⟨_, hφn⟩ : Rℓ.integers) : modularFunctionFieldBar
      (N * ℓ)) = ((⟨_, hintn⟩ : Rℓ.integers) : modularFunctionFieldBar (N * ℓ)) from en.symm),
      hresn, coeffMap_jqNModC]
  have hj' : ∃ h : jB N ∈ R₁.integers,
      R₁.residue ⟨_, h⟩ = ⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) N⟩ := hj
  have hjN' : ∃ h : jNB N ∈ R₁.integers,
      R₁.residue ⟨_, h⟩ = ⟨jqNModC (ResidueField ↥A) N, jqNModC_mem (ResidueField ↥A) N⟩ := hjN
  obtain ⟨hj1, hj2⟩ := hj'
  obtain ⟨hn1, hn2⟩ := hjN'

  have hV : comapIntegers (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) Rℓ = R₁.integers :=
    comapIntegers_eq N A p hpN R₁ ⟨hj1, hj2⟩ Rℓ (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hφj (by
      rw [hresj']
      exact fun halg => transcendental_jqModC (ResidueField ↥A)
        (halg.algHom (charLDegeneracyRoof (ResidueField ↥A) N ℓ).val))

  exact residue_map_eq N A R₁ Rℓ (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ)
    (heckeAlphaC (ResidueField ↥A) N ℓ) hV
    ⟨hj1, hφj, hj2, by rw [hresj', hj2]⟩ ⟨hn1, hφn, hn2, by rw [hresn', hn2]⟩

private theorem residue_heckeBetaBar_eq (ℓ : ℕ) [Fact ℓ.Prime]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField ↥A) p] (hpN : ¬ p ∣ N)
    (R₁ : RegularProlongation A (modularFunctionFieldBar N)
      (modularFunctionFieldC (ResidueField ↥A) N))
    (hj : ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
        ∈ R₁.integers,
      R₁.residue ⟨_, h⟩
        = ⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) N⟩)
    (hjN : ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full N (dvd_refl N))⟩ : modularFunctionFieldBar N)
        ∈ R₁.integers,
      R₁.residue ⟨_, h⟩
        = ⟨jqNModC (ResidueField ↥A) N, jqNModC_mem (ResidueField ↥A) N⟩)
    (Rℓ : RegularProlongation A (modularFunctionFieldBar (N * ℓ))
        (charLDegeneracyRoof (ResidueField ↥A) N ℓ))
    (hcoef : ∀ (y : LaurentSeries ↥A)
        (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar (N * ℓ)),
      ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar (N * ℓ)) ∈ Rℓ.integers,
        ((Rℓ.residue ⟨_, hint⟩ : charLDegeneracyRoof (ResidueField ↥A) N ℓ)
            : LaurentSeries (ResidueField ↥A))
          = coeffMap (IsLocalRing.residue ↥A) y) :
    ∀ f : R₁.integers,
      ∃ h : heckeBetaBar (AlgebraicClosure ℚ) N ℓ (f : modularFunctionFieldBar N)
          ∈ Rℓ.integers,
        Rℓ.residue ⟨_, h⟩ = heckeBetaC (ResidueField ↥A) N ℓ (R₁.residue f) := by

  have hyj : coeffMap A.subtype (qExpand A ℓ (jqModC A)) ∈ modularFunctionFieldBar (N * ℓ) := by
    rw [coeffMap_qExpand, ← coe_jB N A, ← coe_heckeBetaBar N ℓ (jB N)]
    exact SetLike.coe_mem _
  have hyn : coeffMap A.subtype (qExpand A ℓ (jqNModC A N)) ∈ modularFunctionFieldBar (N * ℓ) := by
    rw [coeffMap_qExpand, ← coe_jNB N A, ← coe_heckeBetaBar N ℓ (jNB N)]
    exact SetLike.coe_mem _
  obtain ⟨hintj, hresj⟩ := hcoef _ hyj
  obtain ⟨hintn, hresn⟩ := hcoef _ hyn
  have ej : (⟨coeffMap A.subtype (qExpand A ℓ (jqModC A)), hyj⟩ : modularFunctionFieldBar (N * ℓ))
      = heckeBetaBar (AlgebraicClosure ℚ) N ℓ (jB N) :=
    Subtype.ext (by
      rw [coe_heckeBetaBar, coe_jB N A]
      exact coeffMap_qExpand A.subtype ℓ (jqModC A))
  have en : (⟨coeffMap A.subtype (qExpand A ℓ (jqNModC A N)), hyn⟩ :
        modularFunctionFieldBar (N * ℓ))
      = heckeBetaBar (AlgebraicClosure ℚ) N ℓ (jNB N) :=
    Subtype.ext (by
      rw [coe_heckeBetaBar, coe_jNB N A]
      exact coeffMap_qExpand A.subtype ℓ (jqNModC A N))
  have hφj : heckeBetaBar (AlgebraicClosure ℚ) N ℓ (jB N) ∈ Rℓ.integers := ej ▸ hintj
  have hφn : heckeBetaBar (AlgebraicClosure ℚ) N ℓ (jNB N) ∈ Rℓ.integers := en ▸ hintn
  have hresj' : Rℓ.residue ⟨_, hφj⟩
      = heckeBetaC (ResidueField ↥A) N ℓ ⟨jqModC (ResidueField ↥A), jqModC_mem _ N⟩ := by
    apply Subtype.ext
    rw [coe_heckeBetaC, residue_congr Rℓ (show ((⟨_, hφj⟩ : Rℓ.integers) : modularFunctionFieldBar
      (N * ℓ)) = ((⟨_, hintj⟩ : Rℓ.integers) : modularFunctionFieldBar (N * ℓ)) from ej.symm),
      hresj, coeffMap_qExpand, coeffMap_jqModC]
  have hresn' : Rℓ.residue ⟨_, hφn⟩
      = heckeBetaC (ResidueField ↥A) N ℓ ⟨jqNModC (ResidueField ↥A) N, jqNModC_mem _ N⟩ := by
    apply Subtype.ext
    rw [coe_heckeBetaC, residue_congr Rℓ (show ((⟨_, hφn⟩ : Rℓ.integers) : modularFunctionFieldBar
      (N * ℓ)) = ((⟨_, hintn⟩ : Rℓ.integers) : modularFunctionFieldBar (N * ℓ)) from en.symm),
      hresn, coeffMap_qExpand, coeffMap_jqNModC]
  have hj' : ∃ h : jB N ∈ R₁.integers,
      R₁.residue ⟨_, h⟩ = ⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) N⟩ := hj
  have hjN' : ∃ h : jNB N ∈ R₁.integers,
      R₁.residue ⟨_, h⟩ = ⟨jqNModC (ResidueField ↥A) N, jqNModC_mem (ResidueField ↥A) N⟩ := hjN
  obtain ⟨hj1, hj2⟩ := hj'
  obtain ⟨hn1, hn2⟩ := hjN'

  have hV : comapIntegers (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) Rℓ = R₁.integers :=
    comapIntegers_eq N A p hpN R₁ ⟨hj1, hj2⟩ Rℓ (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hφj (by
      rw [hresj']
      exact fun halg => transcendental_jqNModC (ResidueField ↥A) ℓ
        (halg.algHom (charLDegeneracyRoof (ResidueField ↥A) N ℓ).val))

  exact residue_map_eq N A R₁ Rℓ (heckeBetaBar (AlgebraicClosure ℚ) N ℓ)
    (heckeBetaC (ResidueField ↥A) N ℓ) hV
    ⟨hj1, hφj, hj2, by rw [hresj', hj2]⟩ ⟨hn1, hφn, hn2, by rw [hresn', hn2]⟩

end Rigidity

end RoofRigidity
p2m_reactivate "P2MW.S_ModularCurve_exists_charLDegeneracyRoof_regularProlongation_heckeCompat_of_ne_of_residue_jq_jqN.RoofRigidity"

namespace RoofDegBeta

private theorem dedekindPsi_pos (N : ℕ) [NeZero N] : 0 < dedekindPsi N := by
  unfold dedekindPsi
  have h1 : (1 : ℕ) ∈ N.divisors.filter Squarefree :=
    Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr (NeZero.ne N), squarefree_one⟩
  have hle : N / 1 ≤ ∑ d ∈ N.divisors with Squarefree d, N / d :=
    Finset.single_le_sum (f := fun d => N / d) (fun _ _ => Nat.zero_le _) h1
  rw [Nat.div_one] at hle
  exact lt_of_lt_of_le (Nat.pos_of_ne_zero (NeZero.ne N)) hle

private theorem finrankAlong_heckeBetaC_mul (k : Type*) [Field k] (p : ℕ) [CharP k p]
    (N ℓ : ℕ) [NeZero N] [NeZero ℓ] [NeZero (N * ℓ)] (hp : ¬ p ∣ N * ℓ) :
    finrankAlong k (heckeBetaC k N ℓ) * dedekindPsi N = dedekindPsi (N * ℓ) := by
  have hpN : ¬ p ∣ N := fun h => hp (h.mul_right ℓ)
  have hNℓ : ((N * ℓ : ℕ) : k) ≠ 0 := fun h0 => hp ((CharP.cast_eq_zero_iff k p (N * ℓ)).mp h0)
  have hcomp : (charLDegeneracyRoof k N ℓ).val.comp (heckeBetaC k N ℓ)
      = (qExpandAlgHomC k ℓ).comp (modularFunctionFieldC k N).val :=
    AlgHom.ext fun _ => rfl
  have hfr : ((charLDegeneracyRoof k N ℓ).val.comp (heckeBetaC k N ℓ)).fieldRange
      = (modularFunctionFieldC k N).map (qExpandAlgHomC k ℓ) :=
    (congrArg (fun g : modularFunctionFieldC k N →ₐ[k] LaurentSeries k => g.fieldRange) hcomp).trans
      (IntermediateField.fieldRange_comp_val _ _)
  have h68 : finrankAlong k (heckeBetaC k N ℓ)
      = IntermediateField.relfinrank ((modularFunctionFieldC k N).map (qExpandAlgHomC k ℓ))
          (charLDegeneracyRoof k N ℓ) :=
    (finrankAlong_eq_relfinrank_fieldRange _ _ _).trans
      (congrArg (fun S => IntermediateField.relfinrank S (charLDegeneracyRoof k N ℓ)) hfr)
  have e1 : modularFunctionFieldC k N = modularFunctionFieldFullC k N :=
    modularFunctionFieldC_eq_modularFunctionFieldFullC k p N hpN
  have e2 : charLDegeneracyRoof k N ℓ = modularFunctionFieldFullC k (N * ℓ) :=
    charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul k p N ℓ hp
  rw [h68, e1, e2]
  exact (relfinrank_modularFunctionFieldFullC_mul_dedekindPsi k N ℓ hNℓ).2

private theorem finrankAlong_heckeBetaBar_mul (N ℓ : ℕ) [NeZero N] [NeZero ℓ] [NeZero (N * ℓ)] :
    finrankAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) * dedekindPsi N
      = dedekindPsi (N * ℓ) := by
  have hNℓ : ((N * ℓ : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne (N * ℓ))
  have hcomp : (modularFunctionFieldBar (N * ℓ)).val.comp (heckeBetaBar (AlgebraicClosure ℚ) N ℓ)
      = (qExpandAlgHomC (AlgebraicClosure ℚ) ℓ).comp (modularFunctionFieldBar N).val :=
    AlgHom.ext fun x => coe_heckeBetaBar N ℓ x
  have hfr : ((modularFunctionFieldBar (N * ℓ)).val.comp
        (heckeBetaBar (AlgebraicClosure ℚ) N ℓ)).fieldRange
      = (modularFunctionFieldBar N).map (qExpandAlgHomC (AlgebraicClosure ℚ) ℓ) :=
    (congrArg (fun g : modularFunctionFieldBar N →ₐ[AlgebraicClosure ℚ]
        LaurentSeries (AlgebraicClosure ℚ) => g.fieldRange) hcomp).trans
      (IntermediateField.fieldRange_comp_val _ _)
  have h68 : finrankAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N ℓ)
      = IntermediateField.relfinrank
          ((modularFunctionFieldBar N).map (qExpandAlgHomC (AlgebraicClosure ℚ) ℓ))
          (modularFunctionFieldBar (N * ℓ)) :=
    (finrankAlong_eq_relfinrank_fieldRange _ _ _).trans
      (congrArg (fun S => IntermediateField.relfinrank S (modularFunctionFieldBar (N * ℓ))) hfr)
  have e1 : modularFunctionFieldBar N = modularFunctionFieldFullC (AlgebraicClosure ℚ) N :=
    laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC (AlgebraicClosure ℚ) N
  have e2 : modularFunctionFieldBar (N * ℓ) = modularFunctionFieldFullC (AlgebraicClosure ℚ) (N * ℓ) :=
    laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC (AlgebraicClosure ℚ) (N * ℓ)
  rw [h68, e1, e2]
  exact (relfinrank_modularFunctionFieldFullC_mul_dedekindPsi (AlgebraicClosure ℚ) N ℓ hNℓ).2

private theorem Sc_degBeta (N ℓ q : ℕ) [NeZero N] [Fact ℓ.Prime] [NeZero (N * ℓ)] [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField ↥A) q] (hqNl : ¬ q ∣ N * ℓ)
    [IsAlgClosed (ResidueField ↥A)]
    (hβℓ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hβc : HeckeBetaCIntegral (ResidueField ↥A) N ℓ)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N)]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ))]
    [HasPrincipalDivisors (ResidueField ↥A) (charLDegeneracyRoof (ResidueField ↥A) N ℓ)]
    (hdeg1 : ∀ Y : Place (ResidueField ↥A) (charLDegeneracyRoof (ResidueField ↥A) N ℓ),
      Y.deg = 1)
    (r₁ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
      → Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N)) :
    ∀ v, Divisor.degree
        (Divisor.pullbackAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβℓ
          (Finsupp.single v 1))
      = Divisor.degree
        (Divisor.pullbackAlong (heckeBetaC (ResidueField ↥A) N ℓ) hβc
          (Finsupp.single (r₁ v) 1)) := by
  have _ := hdeg1
  intro v

  haveI : CharZero (modularFunctionFieldBar N) :=
    charZero_of_injective_algebraMap
      (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)).injective
  have hFI₀ : FundamentalIdentityAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N ℓ)
      hβℓ :=
    fundamentalIdentityAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβℓ
      (finiteAlong_heckeBetaBar_of_prime (AlgebraicClosure ℚ) N ℓ)
      (separableAlong_of_charZero (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβℓ)

  have hFIq : FundamentalIdentityAlong (ResidueField ↥A) (heckeBetaC (ResidueField ↥A) N ℓ) hβc :=
    fundamentalIdentityAlong (heckeBetaC (ResidueField ↥A) N ℓ) hβc
      (finiteAlong_heckeBetaC (ResidueField ↥A) N ℓ)
      (separableAlong_heckeAlphaC_heckeBetaC (ResidueField ↥A) N ℓ hqNl).2

  have hv : v.deg = 1 := deg_eq_one_modularFunctionFieldBar N v
  haveI : IsCurveOver (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N) :=
    isCurveOver_modularFunctionFieldC_of_perfectField (ResidueField ↥A) N
  have hw : (r₁ v).deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed (r₁ v)

  have hm : finrankAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N ℓ)
      = finrankAlong (ResidueField ↥A) (heckeBetaC (ResidueField ↥A) N ℓ) :=
    Nat.eq_of_mul_eq_mul_right (dedekindPsi_pos N)
      ((finrankAlong_heckeBetaBar_mul N ℓ).trans
        (finrankAlong_heckeBetaC_mul (ResidueField ↥A) q N ℓ hqNl).symm)
  rw [Divisor.degree_pullbackAlong _ hβℓ hFI₀, Divisor.degree_pullbackAlong _ hβc hFIq,
    Divisor.degree_single, Divisor.degree_single, hv, hw, hm]

end RoofDegBeta
p2m_reactivate "P2MW.S_ModularCurve_exists_charLDegeneracyRoof_regularProlongation_heckeCompat_of_ne_of_residue_jq_jqN.RoofRigidity"

namespace RoofDegAlpha

private theorem val_comp_inclusion_generic {K L : Type*} [Field K] [Field L]
    [Algebra K L] {S T : IntermediateField K L} (h : S ≤ T) :
    T.val.comp (IntermediateField.inclusion h) = S.val :=
  AlgHom.ext fun x => IntermediateField.coe_inclusion h x

private theorem finrankAlong_eq_relfinrank_of_val_comp {K L : Type*} [Field K] [Field L]
    [Algebra K L] {S T : IntermediateField K L} (φ : ↥S →ₐ[K] ↥T)
    (hcomp : T.val.comp φ = S.val) :
    AlgebraicCurve.finrankAlong K φ = IntermediateField.relfinrank S T :=
  (finrankAlong_eq_relfinrank_fieldRange _ _ _).trans
    (congrArg (fun X => IntermediateField.relfinrank X T)
      ((congrArg (fun f => f.fieldRange) hcomp).trans (IntermediateField.fieldRange_val S)))

private theorem dedekindPsi_pos (N : ℕ) [NeZero N] : 0 < dedekindPsi N := by
  unfold dedekindPsi
  have h1 : (1 : ℕ) ∈ N.divisors.filter Squarefree :=
    Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr (NeZero.ne N), squarefree_one⟩
  have hle : N / 1 ≤ ∑ d ∈ N.divisors with Squarefree d, N / d :=
    Finset.single_le_sum (f := fun d => N / d) (fun _ _ => Nat.zero_le _) h1
  rw [Nat.div_one] at hle
  exact lt_of_lt_of_le (Nat.pos_of_ne_zero (NeZero.ne N)) hle

private theorem finrankAlong_heckeAlphaC_mul (k : Type*) [Field k] (p : ℕ) [CharP k p]
    (N ℓ : ℕ) [NeZero N] [NeZero ℓ] [NeZero (N * ℓ)] (hp : ¬ p ∣ N * ℓ) :
    finrankAlong k (heckeAlphaC k N ℓ) * dedekindPsi N = dedekindPsi (N * ℓ) := by
  have hpN : ¬ p ∣ N := fun h => hp (h.mul_right ℓ)
  have hNℓ : ((N * ℓ : ℕ) : k) ≠ 0 := fun h0 => hp ((CharP.cast_eq_zero_iff k p (N * ℓ)).mp h0)
  have hcomp : (charLDegeneracyRoof k N ℓ).val.comp (heckeAlphaC k N ℓ)
      = (modularFunctionFieldC k N).val :=
    AlgHom.ext fun _ => rfl
  have h68 : finrankAlong k (heckeAlphaC k N ℓ)
      = IntermediateField.relfinrank (modularFunctionFieldC k N)
          (charLDegeneracyRoof k N ℓ) :=
    finrankAlong_eq_relfinrank_of_val_comp (heckeAlphaC k N ℓ) hcomp
  have e1 : modularFunctionFieldC k N = modularFunctionFieldFullC k N :=
    modularFunctionFieldC_eq_modularFunctionFieldFullC k p N hpN
  have e2 : charLDegeneracyRoof k N ℓ = modularFunctionFieldFullC k (N * ℓ) :=
    charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul k p N ℓ hp
  rw [h68, e1, e2]
  exact (relfinrank_modularFunctionFieldFullC_mul_dedekindPsi k N ℓ hNℓ).1

private theorem hcomp_alphaBar (N ℓ : ℕ) [NeZero N] [NeZero ℓ] [NeZero (N * ℓ)] :
    (modularFunctionFieldBar (N * ℓ)).val.comp (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ)
      = (modularFunctionFieldBar N).val :=
  val_comp_inclusion_generic _

private theorem h68_alphaBar (N ℓ : ℕ) [NeZero N] [NeZero ℓ] [NeZero (N * ℓ)] :
    finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ)
      = IntermediateField.relfinrank (modularFunctionFieldBar N)
          (modularFunctionFieldBar (N * ℓ)) :=
  finrankAlong_eq_relfinrank_of_val_comp (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ)
    (hcomp_alphaBar N ℓ)

private theorem finrankAlong_heckeAlphaBar_mul (N ℓ : ℕ) [NeZero N] [NeZero ℓ]
    [NeZero (N * ℓ)] :
    finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) * dedekindPsi N
      = dedekindPsi (N * ℓ) := by
  have hNℓ : ((N * ℓ : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne (N * ℓ))
  have h68 := h68_alphaBar N ℓ
  have e1 : modularFunctionFieldBar N
      = modularFunctionFieldFullC (AlgebraicClosure ℚ) N :=
    laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC
      (AlgebraicClosure ℚ) N
  have e2 : modularFunctionFieldBar (N * ℓ)
      = modularFunctionFieldFullC (AlgebraicClosure ℚ) (N * ℓ) :=
    laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC
      (AlgebraicClosure ℚ) (N * ℓ)
  rw [h68, e1, e2]
  exact (relfinrank_modularFunctionFieldFullC_mul_dedekindPsi (AlgebraicClosure ℚ) N ℓ hNℓ).1

private theorem Sc_degAlpha (N ℓ q : ℕ) [NeZero N] [Fact ℓ.Prime] [NeZero (N * ℓ)] [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField ↥A) q] (hqNl : ¬ q ∣ N * ℓ)
    [IsAlgClosed (ResidueField ↥A)]
    (hαℓ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hαc : HeckeAlphaCIntegral (ResidueField ↥A) N ℓ)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N)]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ))]
    [HasPrincipalDivisors (ResidueField ↥A) (charLDegeneracyRoof (ResidueField ↥A) N ℓ)]
    (hdeg1 : ∀ Y : Place (ResidueField ↥A) (charLDegeneracyRoof (ResidueField ↥A) N ℓ),
      Y.deg = 1)
    (r₁ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
      → Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N)) :
    ∀ v, Divisor.degree
        (Divisor.pullbackAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hαℓ
          (Finsupp.single v 1))
      = Divisor.degree
        (Divisor.pullbackAlong (heckeAlphaC (ResidueField ↥A) N ℓ) hαc
          (Finsupp.single (r₁ v) 1)) := by
  have _ := hdeg1
  intro v

  haveI : CharZero (modularFunctionFieldBar N) :=
    charZero_of_injective_algebraMap
      (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)).injective
  have hFI₀ : FundamentalIdentityAlong (AlgebraicClosure ℚ)
      (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hαℓ :=
    fundamentalIdentityAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hαℓ
      (finiteAlong_heckeAlphaBar_of_prime (AlgebraicClosure ℚ) N ℓ)
      (separableAlong_of_charZero (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hαℓ)

  have hFIq : FundamentalIdentityAlong (ResidueField ↥A) (heckeAlphaC (ResidueField ↥A) N ℓ)
      hαc :=
    fundamentalIdentityAlong (heckeAlphaC (ResidueField ↥A) N ℓ) hαc
      (finiteAlong_heckeAlphaC (ResidueField ↥A) N ℓ)
      (separableAlong_heckeAlphaC_heckeBetaC (ResidueField ↥A) N ℓ hqNl).1

  have hv : v.deg = 1 := deg_eq_one_modularFunctionFieldBar N v
  haveI : IsCurveOver (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N) :=
    isCurveOver_modularFunctionFieldC_of_perfectField (ResidueField ↥A) N
  have hw : (r₁ v).deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed (r₁ v)

  have hm : finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ)
      = finrankAlong (ResidueField ↥A) (heckeAlphaC (ResidueField ↥A) N ℓ) :=
    Nat.eq_of_mul_eq_mul_right (dedekindPsi_pos N)
      ((finrankAlong_heckeAlphaBar_mul N ℓ).trans
        (finrankAlong_heckeAlphaC_mul (ResidueField ↥A) q N ℓ hqNl).symm)
  rw [Divisor.degree_pullbackAlong _ hαℓ hFI₀, Divisor.degree_pullbackAlong _ hαc hFIq,
    Divisor.degree_single, Divisor.degree_single, hv, hw, hm]

end RoofDegAlpha
p2m_reactivate "P2MW.S_ModularCurve_exists_charLDegeneracyRoof_regularProlongation_heckeCompat_of_ne_of_residue_jq_jqN.RoofRigidity"

namespace RoofA

private theorem Sa_transport
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (N * ℓ)]
    (q : ℕ) (hq : q.Prime) (hqN : ¬ q ∣ N) (hℓq : ℓ ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    [IsAlgClosed (ResidueField ↥A)] :
    ∃ (Rℓ : RegularProlongation A (modularFunctionFieldBar (N * ℓ))
        (charLDegeneracyRoof (ResidueField ↥A) N ℓ))
      (rℓ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ))
        → Place (ResidueField ↥A) (charLDegeneracyRoof (ResidueField ↥A) N ℓ)),
      (∀ (y : LaurentSeries ↥A)
          (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar (N * ℓ)),
        ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar (N * ℓ)) ∈ Rℓ.integers,
          ((Rℓ.residue ⟨_, hint⟩ : charLDegeneracyRoof (ResidueField ↥A) N ℓ)
              : LaurentSeries (ResidueField ↥A))
            = coeffMap (IsLocalRing.residue ↥A) y)
      ∧ ∀ f : Rℓ.integers, Rℓ.residue f ≠ 0 →
          ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ)),
            (∀ P, D P = P.ord (f : modularFunctionFieldBar (N * ℓ))) →
          ∀ Q, Finsupp.mapDomain rℓ D Q = Q.ord (Rℓ.residue f) := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  haveI : CharP (ResidueField ↥A) q :=
    ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  have hqNℓ : ¬ q ∣ N * ℓ := by
    intro h
    rcases (Nat.Prime.dvd_mul hq).mp h with h1 | h2
    · exact hqN h1
    · exact hℓq ((Nat.prime_dvd_prime_iff_eq hq Fact.out).mp h2).symm
  have hroof : charLDegeneracyRoof (ResidueField ↥A) N ℓ
      = modularFunctionFieldFullC (ResidueField ↥A) (N * ℓ) :=
    charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul (ResidueField ↥A) q N ℓ hqNℓ
  have h := exists_regularProlongation_placeMap_modularFunctionFieldFullC_of_not_dvd
    (N * ℓ) q hqNℓ A hA
  rw [← hroof] at h
  exact h

end RoofA
p2m_reactivate "P2MW.S_ModularCurve_exists_charLDegeneracyRoof_regularProlongation_heckeCompat_of_ne_of_residue_jq_jqN.RoofRigidity"

theorem solution
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (hαℓ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hβℓ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hαc : HeckeAlphaCIntegral (ResidueField ↥A) N ℓ)
    (hβc : HeckeBetaCIntegral (ResidueField ↥A) N ℓ)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N)]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ))]
    [HasPrincipalDivisors (ResidueField ↥A) (charLDegeneracyRoof (ResidueField ↥A) N ℓ)]
    (hdeg1 : ∀ Y : Place (ResidueField ↥A) (charLDegeneracyRoof (ResidueField ↥A) N ℓ),
      Y.deg = 1)
    (R₁ : RegularProlongation A (modularFunctionFieldBar N)
      (modularFunctionFieldC (ResidueField ↥A) N))
    (r₁ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
      → Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N))
    (hr₁ : ∀ f : R₁.integers, R₁.residue f ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        (∀ P, D P = P.ord (f : modularFunctionFieldBar N)) →
      ∀ Q, Finsupp.mapDomain r₁ D Q = Q.ord (R₁.residue f))
    (hj : ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
        ∈ R₁.integers,
      R₁.residue ⟨_, h⟩
        = ⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) N⟩)
    (hjN : ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full N (dvd_refl N))⟩ : modularFunctionFieldBar N)
        ∈ R₁.integers,
      R₁.residue ⟨_, h⟩
        = ⟨jqNModC (ResidueField ↥A) N, jqNModC_mem (ResidueField ↥A) N⟩) :
    ∃ (Rℓ : RegularProlongation A (modularFunctionFieldBar (N * ℓ))
        (charLDegeneracyRoof (ResidueField ↥A) N ℓ))
      (rℓ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ))
        → Place (ResidueField ↥A) (charLDegeneracyRoof (ResidueField ↥A) N ℓ)),
      (∀ f : Rℓ.integers, Rℓ.residue f ≠ 0 →
        ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ)),
          (∀ P, D P = P.ord (f : modularFunctionFieldBar (N * ℓ))) →
        ∀ Q, Finsupp.mapDomain rℓ D Q = Q.ord (Rℓ.residue f))
      ∧ (∀ f : R₁.integers,
          ∃ h : heckeAlphaBar (AlgebraicClosure ℚ) N ℓ (f : modularFunctionFieldBar N)
              ∈ Rℓ.integers,
            Rℓ.residue ⟨_, h⟩ = heckeAlphaC (ResidueField ↥A) N ℓ (R₁.residue f))
      ∧ (∀ f : R₁.integers,
          ∃ h : heckeBetaBar (AlgebraicClosure ℚ) N ℓ (f : modularFunctionFieldBar N)
              ∈ Rℓ.integers,
            Rℓ.residue ⟨_, h⟩ = heckeBetaC (ResidueField ↥A) N ℓ (R₁.residue f))
      ∧ (∀ v, Divisor.degree
            (Divisor.pullbackAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hαℓ
              (Finsupp.single v 1))
          = Divisor.degree
            (Divisor.pullbackAlong (heckeAlphaC (ResidueField ↥A) N ℓ) hαc
              (Finsupp.single (r₁ v) 1)))
      ∧ ∀ v, Divisor.degree
            (Divisor.pullbackAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβℓ
              (Finsupp.single v 1))
          = Divisor.degree
            (Divisor.pullbackAlong (heckeBetaC (ResidueField ↥A) N ℓ) hβc
              (Finsupp.single (r₁ v) 1)) := by
  have _ := hr₁
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero (N * ℓ) :=
    ⟨Nat.mul_ne_zero (NeZero.ne N) (Fact.out : ℓ.Prime).ne_zero⟩
  haveI : CharP (ResidueField ↥A) q :=
    ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  haveI : IsAlgClosed (ResidueField ↥A) :=
    ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  have hqNl : ¬ q ∣ N * ℓ := by
    intro h
    rcases (Nat.Prime.dvd_mul hq).mp h with h1 | h2
    · exact hqN h1
    · exact hℓq (((Nat.prime_dvd_prime_iff_eq hq Fact.out).mp h2).symm)
  obtain ⟨Rℓ, rℓ, hcoef, hrℓ⟩ := RoofA.Sa_transport N ℓ q hq hqN hℓq A hA
  exact ⟨Rℓ, rℓ, hrℓ,
    RoofRigidity.residue_heckeAlphaBar_eq N A ℓ q hqN R₁ hj hjN Rℓ hcoef,
    RoofRigidity.residue_heckeBetaBar_eq N A ℓ q hqN R₁ hj hjN Rℓ hcoef,
    RoofDegAlpha.Sc_degAlpha N ℓ q A hqNl hαℓ hαc hdeg1 r₁,
    RoofDegBeta.Sc_degBeta N ℓ q A hqNl hβℓ hβc hdeg1 r₁⟩

end S_ModularCurve_exists_charLDegeneracyRoof_regularProlongation_heckeCompat_of_ne_of_residue_jq_jqN
end P2MW
export P2MW.S_ModularCurve_exists_charLDegeneracyRoof_regularProlongation_heckeCompat_of_ne_of_residue_jq_jqN (solution)
