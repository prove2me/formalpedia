-- Prove2me | solution 1 for ModularCurve.exists_uniform_dualGraphCovering_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/46be300e-48c9-5b27-a937-34b7bece6e56

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_ModularCurve_FinitePlaceLift
import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_ModularCurve_QAdicPlaceMod
import Definitions.Def_ModularCurve_ReductionModL
import Theorems.Thm_ModularCurve_exists_constantReduction_isGood_isPlaceReductionModL
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_AlgebraicCurve_ConstantReduction_isPointwise_of_hasPrincipalDivisors
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_ell_eq_degree_add_one_sub_genusFF_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_span_residue_eq_riemannRochSpace_of_isEmbBasis_of_isGood
import Theorems.Thm_ModularCurve_exists_uniform_window_smul_mem_integers
import Theorems.Thm_ModularCurve_exists_uniform_adapted_basis
import Theorems.Thm_AlgebraicCurve_ComponentChart_prox_eq_of_chartData_of_minor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_uniform_dualGraphCovering_of_not_dvd
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"
p2m_attr_erase "simp" "ModularCurve.cuspCount_one ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe"
p2m_attr_erase "simp" "ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero"
p2m_attr_erase "simp" "TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec"

set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve ModularCurve IsLocalRing

set_option autoImplicit false

noncomputable section

namespace GoodChart

open AlgebraicCurve IsLocalRing

variable {K : Type*} [Field K] {A : ValuationSubring K} {F : Type*} [Field F] [Algebra K F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

section PlaceLemmas

variable {L : Type*} {E : Type*} [Field L] [Field E] [Algebra L E] (w : Place L E)

private theorem ord_nonneg_of_mem {f : E} (hf : f ∈ w.toValuationSubring) : 0 ≤ w.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  have hle : w.adicValuation f ≤ 1 := by
    have h := w.adicValuation_coe ⟨f, hf⟩
    rw [show ((⟨f, hf⟩ : w.toValuationSubring) : E) = f from rfl] at h
    rw [h]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
  have hne := w.adicValuation_ne_zero hf0
  have hlog : WithZero.log (w.adicValuation f) ≤ 0 := by
    rw [WithZero.log_le_iff_le_exp hne, WithZero.exp_zero]
    exact hle
  unfold Place.ord
  omega

private theorem mem_of_ord_nonneg {f : E} (h : 0 ≤ w.ord f) : f ∈ w.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact zero_mem _
  · exact w.mem_toValuationSubring_of_ord_nonneg_alt hf0 h

private theorem evalAt_sub_of_mem (hw : w.IsRational) {f g : E} (hf : f ∈ w.toValuationSubring)
    (hg : g ∈ w.toValuationSubring) :
    w.evalAt (f - g) = w.evalAt f - w.evalAt g := by
  apply w.algebraMap_residueField_injective
  rw [map_sub, w.algebraMap_evalAt hw (sub_mem hf hg), w.algebraMap_evalAt hw hf,
    w.algebraMap_evalAt hw hg, ← map_sub]
  rfl

private theorem ord_pos_of_evalAt_eq_zero (hw : w.IsRational) {f : E} (hf0 : f ≠ 0)
    (hf : f ∈ w.toValuationSubring) (h0 : w.evalAt f = 0) : 0 < w.ord f := by
  have hnn := ord_nonneg_of_mem w hf
  rcases hnn.lt_or_eq with hlt | heq
  · exact hlt
  · exact absurd (w.evalAt_ne_zero_of_ord_eq_zero hw hf0 heq.symm) (not_not.mpr h0)

private theorem ne_zero_of_ord_eq_one {f : E} (h : w.ord f = 1) : f ≠ 0 := by
  rintro rfl
  rw [Place.ord_zero] at h
  exact zero_ne_one h

end PlaceLemmas

open Classical in

private theorem mapDomain_apply_eq_sum_of_subset {α β : Type*} (r : α → β) (D : α →₀ ℤ) (q : β)
    (T : Finset α) (hT : ∀ P ∈ D.support, r P = q → P ∈ T) :
    Finsupp.mapDomain r D q = ∑ P ∈ T.filter (fun P => r P = q), D P := by
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  unfold Finsupp.sum
  have h1 : ∑ P ∈ D.support, (Finsupp.single (r P) (D P)) q
      = ∑ P ∈ D.support.filter (fun P => r P = q), D P := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [Finsupp.single_apply]
  rw [h1]
  refine Finset.sum_subset ?_ ?_
  · intro P hP
    rw [Finset.mem_filter] at hP ⊢
    exact ⟨hT P hP.1 hP.2, hP.2⟩
  · intro P hPT hPn
    rw [Finset.mem_filter] at hPT hPn
    by_contra hD
    exact hPn ⟨Finsupp.mem_support_iff.mpr hD, hPT.2⟩

variable (R : ConstantReduction A F Fbar)

open Classical in

private theorem ord_eq_neg_on_fibre [HasPrincipalDivisors K F] {f : F} (hf : f ∈ R.integers)
    (hres : R.residue ⟨f, hf⟩ ≠ 0) (E : Divisor K F) (hE : ∀ w, -E w ≤ w.ord f)
    {Qbar : Place (ResidueField A) Fbar}
    (hord : Qbar.ord (R.residue ⟨f, hf⟩) = -(Finsupp.mapDomain R.placeMap E Qbar))
    (w : Place K F) (hw : R.placeMap w = Qbar) : w.ord f = -E w := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    apply hres
    have h0 : (⟨(0 : F), hf⟩ : R.integers) = 0 := rfl
    rw [h0, map_zero]
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  have hax := R.mapDomain_placeMap ⟨f, hf⟩ hres D hD Qbar

  set T : Finset (Place K F) := D.support ∪ E.support ∪ {w} with hT
  have hDT : ∀ P ∈ D.support, R.placeMap P = Qbar → P ∈ T := fun P hP _ => by
    rw [hT]; exact Finset.mem_union_left _ (Finset.mem_union_left _ hP)
  have hET : ∀ P ∈ E.support, R.placeMap P = Qbar → P ∈ T := fun P hP _ => by
    rw [hT]; exact Finset.mem_union_left _ (Finset.mem_union_right _ hP)
  have hsumD := mapDomain_apply_eq_sum_of_subset R.placeMap D Qbar T hDT
  have hsumE := mapDomain_apply_eq_sum_of_subset R.placeMap E Qbar T hET

  have hsum : ∑ P ∈ T.filter (fun P => R.placeMap P = Qbar), (D P + E P) = 0 := by
    rw [Finset.sum_add_distrib, ← hsumD, ← hsumE, hax, hord]
    ring
  have hnonneg : ∀ P ∈ T.filter (fun P => R.placeMap P = Qbar), 0 ≤ D P + E P := by
    intro P _
    rw [hD P]
    have := hE P
    omega
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum
  have hwT : w ∈ T.filter (fun P => R.placeMap P = Qbar) := by
    rw [Finset.mem_filter, hT]
    exact ⟨Finset.mem_union_right _ (Finset.mem_singleton_self w), hw⟩
  have h := hzero w hwT
  rw [hD w] at h
  omega

private theorem evalAt_placeMap_residue (hPW : R.IsPointwise) {P : Place K F} (hP : P.IsRational)
    {f : F} (hf : f ∈ R.integers)
    (hreg : ∀ w : Place K F, R.placeMap w = R.placeMap P → f ∈ w.toValuationSubring) :
    ∃ h : P.evalAt f ∈ A,
      (R.residue ⟨f, hf⟩ : Fbar) ∈ (R.placeMap P).toValuationSubring ∧
      (R.placeMap P).evalAt (R.residue ⟨f, hf⟩) = IsLocalRing.residue A ⟨P.evalAt f, h⟩ := by
  obtain ⟨hm, h, hcompat⟩ := hPW P hP f hf hreg
  refine ⟨h, hm, ?_⟩
  rw [(R.placeMap P).evalAt_of_mem hm, ← hcompat, Place.residueInv_algebraMap]

private theorem isDiscParam_sub_evalAt (hPW : R.IsPointwise) {P : Place K F} (hP : P.IsRational)
    {f : F} (hf : f ∈ R.integers)
    (hreg : ∀ w : Place K F, R.placeMap w = R.placeMap P → f ∈ w.toValuationSubring)
    (hord1 : (R.placeMap P).ord (R.residue ⟨f, hf⟩
      - algebraMap (ResidueField A) Fbar ((R.placeMap P).evalAt (R.residue ⟨f, hf⟩))) = 1) :
    R.IsDiscParam P (f - algebraMap K F (P.evalAt f)) := by
  obtain ⟨hA, -, hval⟩ := evalAt_placeMap_residue R hPW hP hf hreg
  set c : K := P.evalAt f with hc
  have hcmem : algebraMap K F c ∈ R.integers := (R.algebraMap_mem_iff c).mpr hA
  have hT : f - algebraMap K F c ∈ R.integers := sub_mem hf hcmem
  have hresT : R.residue ⟨f - algebraMap K F c, hT⟩
      = R.residue ⟨f, hf⟩ - algebraMap (ResidueField A) Fbar ((R.placeMap P).evalAt (R.residue ⟨f, hf⟩)) := by
    have helt : (⟨f - algebraMap K F c, hT⟩ : R.integers) = ⟨f, hf⟩ - ⟨algebraMap K F c, hcmem⟩ :=
      Subtype.ext rfl
    rw [helt, map_sub, R.residue_algebraMap ⟨c, hA⟩, hval]
  refine ⟨hT, ?_, ?_, ?_, ?_⟩
  ·
    rw [hresT]
    exact ne_zero_of_ord_eq_one _ hord1
  · rw [hresT]
    exact hord1
  ·
    have hPmem : f ∈ P.toValuationSubring := hreg P rfl
    have hcP : algebraMap K F c ∈ P.toValuationSubring := P.algebraMap_mem' c
    have hval0 : P.evalAt (f - algebraMap K F c) = 0 := by
      rw [evalAt_sub_of_mem P hP hPmem hcP, P.evalAt_algebraMap_eq, hc, sub_self]
    have hT0 : f - algebraMap K F c ≠ 0 := by
      intro h0
      have : R.residue ⟨f - algebraMap K F c, hT⟩ = 0 := by
        have h00 : (⟨f - algebraMap K F c, hT⟩ : R.integers) = 0 := Subtype.ext h0
        rw [h00, map_zero]
      rw [hresT] at this
      exact ne_zero_of_ord_eq_one _ hord1 this
    exact ord_pos_of_evalAt_eq_zero P hP hT0 (sub_mem hPmem hcP) hval0
  ·
    intro Q hQ
    exact ord_nonneg_of_mem Q (sub_mem (hreg Q hQ) (Q.algebraMap_mem' c))

end GoodChart

end

noncomputable section

namespace CuspUnitAssembly

open AlgebraicCurve ModularCurve IsLocalRing

variable {K : Type*} [Field K] {A : ValuationSubring K} {F : Type*} [Field F] [Algebra K F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

private theorem inv_mem_of_residue_ne_zero (R : ConstantReduction A F Fbar) {x : F} (hx : x ∈ R.integers)
    (hres : R.residue ⟨x, hx⟩ ≠ 0) :
    ∃ hinv : x⁻¹ ∈ R.integers, R.residue ⟨x⁻¹, hinv⟩ * R.residue ⟨x, hx⟩ = 1 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply hres
    have h0 : (⟨(0 : F), hx⟩ : R.integers) = 0 := rfl
    rw [h0, map_zero]
  have hnotmax : (⟨x, hx⟩ : R.integers) ∉ IsLocalRing.maximalIdeal R.integers := by
    rw [← R.ker_residue, RingHom.mem_ker]
    exact hres
  have hunit : IsUnit (⟨x, hx⟩ : R.integers) := by
    by_contra hnu
    exact hnotmax ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu))
  obtain ⟨u, hu⟩ := hunit
  have hmulinv : ((u : R.integers) : F) * (((u⁻¹ : (R.integers)ˣ) : R.integers) : F) = 1 := by
    have h := congrArg Subtype.val u.mul_inv
    push_cast at h
    exact h
  have huval : ((u : R.integers) : F) = x := by rw [hu]
  rw [huval] at hmulinv
  have hinv : (((u⁻¹ : (R.integers)ˣ) : R.integers) : F) = x⁻¹ := eq_inv_of_mul_eq_one_right hmulinv
  have hinvmem : x⁻¹ ∈ R.integers := hinv ▸ ((u⁻¹ : (R.integers)ˣ) : R.integers).2
  refine ⟨hinvmem, ?_⟩
  rw [← map_mul]
  have h1 : (⟨x⁻¹, hinvmem⟩ * ⟨x, hx⟩ : R.integers) = 1 := Subtype.ext (inv_mul_cancel₀ hx0)
  rw [h1, map_one]

end CuspUnitAssembly

end

noncomputable section

namespace ReducedChart

open AlgebraicCurve ModularCurve IsLocalRing

set_option synthInstance.maxHeartbeats 1600000

variable {k : Type*} [Field k] {Fb : Type*} [Field Fb] [Algebra k Fb]

private theorem ord_eq_of_mem_notMem {D : Divisor k Fb} {P : Place k Fb} {u : Fb}
    (hu1 : u ∈ riemannRochSpace D) (hu2 : u ∉ riemannRochSpace (D - Finsupp.single P 1)) :
    u ≠ 0 ∧ P.ord u = -D P := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hu2 (Submodule.zero_mem _)
  refine ⟨hu0, le_antisymm ?_ ?_⟩
  · by_contra hlt
    push Not at hlt
    apply hu2
    rw [mem_riemannRochSpace_iff]
    intro v
    refine Or.inr ?_
    rcases eq_or_ne v P with hvP | hvP
    · subst hvP
      rw [Finsupp.sub_apply, Finsupp.single_eq_same]
      omega
    · rw [Finsupp.sub_apply, Finsupp.single_eq_of_ne hvP, sub_zero]
      rcases (mem_riemannRochSpace_iff.mp hu1) v with h0 | hle
      · exact absurd h0 hu0
      · exact hle
  · rcases (mem_riemannRochSpace_iff.mp hu1) P with h0 | hle
    · exact absurd h0 hu0
    · exact hle

private theorem riemannRochSpace_sub_single_le (D : Divisor k Fb) (P : Place k Fb) :
    riemannRochSpace (D - Finsupp.single P 1) ≤ riemannRochSpace D := by
  intro f hf
  rw [mem_riemannRochSpace_iff] at hf ⊢
  intro v
  rcases hf v with h0 | hle
  · exact Or.inl h0
  · refine Or.inr ?_
    rcases eq_or_ne v P with hvP | hvP
    · subst hvP
      rw [Finsupp.sub_apply, Finsupp.single_eq_same] at hle
      omega
    · rw [Finsupp.sub_apply, Finsupp.single_eq_of_ne hvP, sub_zero] at hle
      exact hle

variable (k) in

private theorem exists_mem_notMem [IsAlgClosed k] (N : ℕ) [NeZero N]
    [IsCurveOver k (modularFunctionFieldFullC k N)]
    (D : Divisor k (modularFunctionFieldFullC k N))
    (hD : 2 * (genusFF k (modularFunctionFieldFullC k N) : ℤ) ≤ D.degree)
    (P : Place k (modularFunctionFieldFullC k N)) :
    ∃ u ∈ riemannRochSpace D, u ∉ riemannRochSpace (D - Finsupp.single P 1) := by
  have hdegP : (D - Finsupp.single P 1).degree = D.degree - 1 := by
    rw [map_sub, Divisor.degree_single, IsCurveOver.forall_deg_eq_one_of_isAlgClosed (K := k) P]
    push_cast
    ring
  have h1 := ell_eq_degree_add_one_sub_genusFF_modularFunctionFieldFullC k N D (by omega)
  have h2 := ell_eq_degree_add_one_sub_genusFF_modularFunctionFieldFullC k N (D - Finsupp.single P 1)
    (by rw [hdegP]; omega)
  have hlt : ell (D - Finsupp.single P 1) < ell D := by
    have h : (ell (D - Finsupp.single P 1) : ℤ) < ell D := by
      rw [h1, h2, hdegP]
      omega
    exact_mod_cast h
  have hne : ¬ (LSpace D ≤ LSpace (D - Finsupp.single P 1)) := by
    intro hle
    have heq : LSpace D = LSpace (D - Finsupp.single P 1) :=
      le_antisymm hle (riemannRochSpace_sub_single_le D P)
    have : ell D = ell (D - Finsupp.single P 1) := by
      unfold ell
      rw [heq]
    omega
  obtain ⟨u, hu1, hu2⟩ := SetLike.not_le_iff_exists.mp hne
  exact ⟨u, hu1, hu2⟩

variable (k) in
set_option maxHeartbeats 6400000 in

private theorem exists_indices [IsAlgClosed k] (N : ℕ) [NeZero N]
    [IsCurveOver k (modularFunctionFieldFullC k N)]
    {r : ℕ} (gb : Fin r → modularFunctionFieldFullC k N) (hg0 : ∀ i, gb i ≠ 0)
    (D : Divisor k (modularFunctionFieldFullC k N))
    (hdeg : D.degree = 2 * (genusFF k (modularFunctionFieldFullC k N) : ℤ) + 1)
    (hspan : Submodule.span k (Set.range gb) = riemannRochSpace D)
    (P : Place k (modularFunctionFieldFullC k N)) (hP : P.IsRational) :
    ∃ j i : Fin r, P.ord (gb j) = -D P ∧ (∀ i', 0 ≤ P.ord (gb i' * (gb j)⁻¹)) ∧
      P.ord (gb i * (gb j)⁻¹
        - algebraMap k (modularFunctionFieldFullC k N) (P.evalAt (gb i * (gb j)⁻¹))) = 1 := by

  have hmem : ∀ i, gb i ∈ riemannRochSpace D := fun i => by
    rw [← hspan]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hlow : ∀ i (v : Place k (modularFunctionFieldFullC k N)), -D v ≤ v.ord (gb i) := fun i v => by
    rcases (mem_riemannRochSpace_iff.mp (hmem i)) v with h0 | hle
    · exact absurd h0 (hg0 i)
    · exact hle

  obtain ⟨u, hu1, hu2⟩ := exists_mem_notMem k N D (by rw [hdeg]; omega) P
  have hj : ∃ j, P.ord (gb j) ≤ -D P := by
    by_contra hall
    push Not at hall
    apply hu2
    have hle : riemannRochSpace D ≤ riemannRochSpace (D - Finsupp.single P 1) := by
      rw [← hspan, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      show gb i ∈ riemannRochSpace (D - Finsupp.single P 1)
      rw [mem_riemannRochSpace_iff]
      intro v
      refine Or.inr ?_
      rcases eq_or_ne v P with hvP | hvP
      · subst hvP
        rw [Finsupp.sub_apply, Finsupp.single_eq_same]
        have := hall i
        omega
      · rw [Finsupp.sub_apply, Finsupp.single_eq_of_ne hvP, sub_zero]
        exact hlow i v
    exact hle hu1
  obtain ⟨j, hjle⟩ := hj
  have hjord : P.ord (gb j) = -D P := le_antisymm hjle (hlow j P)

  have hratio : ∀ i', 0 ≤ P.ord (gb i' * (gb j)⁻¹) := fun i' => by
    rw [P.ord_mul (hg0 i') (inv_ne_zero (hg0 j)), P.ord_inv, hjord]
    have := hlow i' P
    omega

  obtain ⟨w, hw1, hw2⟩ := exists_mem_notMem k N (D - Finsupp.single P 1)
    (by rw [map_sub, Divisor.degree_single, IsCurveOver.forall_deg_eq_one_of_isAlgClosed (K := k) P, hdeg]
        push_cast; omega) P

  set c : Fin r → k := fun i => P.evalAt (gb i * (gb j)⁻¹) with hc
  set x : Fin r → modularFunctionFieldFullC k N := fun i => gb i - c i • gb j with hx
  have hxmem : ∀ i, x i ∈ riemannRochSpace D := fun i =>
    sub_mem (hmem i) (Submodule.smul_mem _ _ (hmem j))

  have hρmem : ∀ i, gb i * (gb j)⁻¹ ∈ P.toValuationSubring := fun i =>
    GoodChart.mem_of_ord_nonneg P (hratio i)
  have hδ : ∀ i, gb i * (gb j)⁻¹ - algebraMap k (modularFunctionFieldFullC k N) (c i) ∈ P.toValuationSubring := fun i =>
    sub_mem (hρmem i) (P.algebraMap_mem' (c i))
  have hδval : ∀ i, P.evalAt (gb i * (gb j)⁻¹ - algebraMap k (modularFunctionFieldFullC k N) (c i)) = 0 := fun i => by
    rw [GoodChart.evalAt_sub_of_mem P hP (hρmem i) (P.algebraMap_mem' (c i)), P.evalAt_algebraMap_eq]
    exact sub_self _
  have hxeq : ∀ i, x i = (gb i * (gb j)⁻¹ - algebraMap k (modularFunctionFieldFullC k N) (c i)) * gb j := fun i => by
    rw [hx]
    dsimp only
    rw [sub_mul, mul_assoc, inv_mul_cancel₀ (hg0 j), mul_one, Algebra.smul_def]

  have hxmem1 : ∀ i, x i ∈ riemannRochSpace (D - Finsupp.single P 1) := fun i => by
    rw [mem_riemannRochSpace_iff]
    intro v
    rcases eq_or_ne (x i) 0 with h0 | hx0
    · exact Or.inl h0
    refine Or.inr ?_
    rcases eq_or_ne v P with hvP | hvP
    · subst hvP
      rw [Finsupp.sub_apply, Finsupp.single_eq_same]
      have hδ0 : gb i * (gb j)⁻¹ - algebraMap k (modularFunctionFieldFullC k N) (c i) ≠ 0 := by
        intro h
        apply hx0
        rw [hxeq i, h, zero_mul]
      have hpos := GoodChart.ord_pos_of_evalAt_eq_zero v hP hδ0 (hδ i) (hδval i)
      rw [hxeq i, v.ord_mul hδ0 (hg0 j), hjord]
      omega
    · rw [Finsupp.sub_apply, Finsupp.single_eq_of_ne hvP, sub_zero]
      rcases (mem_riemannRochSpace_iff.mp (hxmem i)) v with h0 | hle
      · exact absurd h0 hx0
      · exact hle

  have hjnot : gb j ∉ riemannRochSpace (D - Finsupp.single P 1) := by
    intro h
    rcases (mem_riemannRochSpace_iff.mp h) P with h0 | hle
    · exact hg0 j h0
    · rw [Finsupp.sub_apply, Finsupp.single_eq_same] at hle
      omega

  have hi : ∃ i, x i ∉ riemannRochSpace (D - Finsupp.single P 1 - Finsupp.single P 1) := by
    by_contra hall
    push Not at hall
    apply hw2

    have hwspan : w ∈ Submodule.span k (Set.range gb) := by
      rw [hspan]
      exact riemannRochSpace_sub_single_le D P hw1
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hwspan
    have hsum : w = (∑ i, b i • x i) + (∑ i, b i * c i) • gb j := by
      rw [← hb, Finset.sum_smul]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hx]
      dsimp only
      rw [smul_sub, mul_smul, sub_add_cancel]

    have hsmem : (∑ i, b i • x i) ∈ riemannRochSpace (D - Finsupp.single P 1) :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hxmem1 i)
    have hcoef : (∑ i, b i * c i) = 0 := by
      by_contra hne
      apply hjnot
      have hmem' : (∑ i, b i * c i) • gb j ∈ riemannRochSpace (D - Finsupp.single P 1) := by
        have h := sub_mem hw1 hsmem
        rw [hsum, add_sub_cancel_left] at h
        exact h
      have h := Submodule.smul_mem _ (∑ i, b i * c i)⁻¹ hmem'
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h
    rw [hsum, hcoef, zero_smul, add_zero]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hall i)
  obtain ⟨i, hinot⟩ := hi
  obtain ⟨hxi0, hxiord⟩ := ord_eq_of_mem_notMem (hxmem1 i) hinot
  refine ⟨j, i, hjord, hratio, ?_⟩
  have hδ0 : gb i * (gb j)⁻¹ - algebraMap k (modularFunctionFieldFullC k N) (c i) ≠ 0 := by
    intro h
    apply hxi0
    rw [hxeq i, h, zero_mul]
  have h := hxiord
  rw [hxeq i, P.ord_mul hδ0 (hg0 j), hjord, Finsupp.sub_apply, Finsupp.single_eq_same] at h
  show P.ord (gb i * (gb j)⁻¹ - algebraMap k (modularFunctionFieldFullC k N) (c i)) = 1
  omega

end ReducedChart

end

open AlgebraicCurve ModularCurve

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

private theorem exists_chartData_of_pinnedBasis
    (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (R : ConstantReduction A (modularFunctionFieldBar N)
      (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N))
    (hgood : R.IsGood) (hint : ∀ i, s i ∈ R.integers) (hres0 : ∀ i, R.residue ⟨s i, hint i⟩ ≠ 0)
    (hli : LinearIndependent (IsLocalRing.ResidueField A) (fun i => R.residue ⟨s i, hint i⟩))
    (xbar : Place (IsLocalRing.ResidueField A) (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)) :
    ∃ j i : Fin r, ∃ hratio : ∀ i', s i' * (s j)⁻¹ ∈ R.integers,
      xbar.ord (R.residue ⟨s j, hint j⟩) = -(Finsupp.mapDomain R.placeMap (embDivisor N) xbar) ∧
      (∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), R.placeMap w = xbar →
        w.ord (s j) = -(embDivisor N w) ∧ ∀ i', 0 ≤ w.ord (s i' * (s j)⁻¹)) ∧
      (∀ i', R.residue ⟨s i' * (s j)⁻¹, hratio i'⟩ = R.residue ⟨s i', hint i'⟩ * (R.residue ⟨s j, hint j⟩)⁻¹) ∧
      xbar.ord (R.residue ⟨s i * (s j)⁻¹, hratio i⟩
        - algebraMap (IsLocalRing.ResidueField A) (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)
            (xbar.evalAt (R.residue ⟨s i * (s j)⁻¹, hratio i⟩))) = 1 ∧
      ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), R.placeMap v = xbar →
        (∃ h : v.evalAt (s i * (s j)⁻¹) ∈ A,
          (xbar.evalAt (R.residue ⟨s i * (s j)⁻¹, hratio i⟩))
            = IsLocalRing.residue A ⟨v.evalAt (s i * (s j)⁻¹), h⟩) ∧
        R.IsDiscParam v (s i * (s j)⁻¹
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (v.evalAt (s i * (s j)⁻¹))) := by
  classical
  haveI hPD := hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  have hs0 : ∀ i, s i ≠ 0 := fun i => hs.1.ne_zero i

  haveI : IsAlgClosed (IsLocalRing.ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  haveI hco : IsCurveOver (IsLocalRing.ResidueField A)
      (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :=
    isCurveOver_modularFunctionFieldFullC (IsLocalRing.ResidueField A) N
  have hspan := span_residue_eq_riemannRochSpace_of_isEmbBasis_of_isGood N A R hgood s hs hint hli

  have hvbar : xbar.IsRational :=
    (Place.isRational_iff_deg_eq_one _).mpr (IsCurveOver.forall_deg_eq_one_of_isAlgClosed _)

  have hdegE : Divisor.degree (embDivisor N) = (embDegree N : ℤ) := by
    simp only [embDivisor]
    rw [map_zsmul, Divisor.degree_single, deg_eq_one_modularFunctionFieldBar N, Nat.cast_one, mul_one,
      smul_eq_mul, mul_one]
  have hdeg : Divisor.degree (Finsupp.mapDomain R.placeMap (embDivisor N))
      = 2 * (genusFF (IsLocalRing.ResidueField A)
        (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) : ℤ) + 1 := by
    rw [R.degree_mapDomain, hdegE]
    have hg : genusFF (IsLocalRing.ResidueField A) (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)
        = genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := hgood
    rw [hg]
    unfold embDegree
    push_cast
    ring

  obtain ⟨j, i, hjord, -, hiord⟩ := ReducedChart.exists_indices (IsLocalRing.ResidueField A) N
    (fun i => R.residue ⟨s i, hint i⟩) hres0 _ hdeg hspan xbar hvbar

  have hsE : ∀ i (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)), -(embDivisor N w) ≤ w.ord (s i) := by
    intro i w
    have hmem : s i ∈ riemannRochSpace (embDivisor N) := by
      rw [← hs.2]
      exact Submodule.subset_span ⟨i, rfl⟩
    rcases (mem_riemannRochSpace_iff.mp hmem) w with h0 | hle
    · exact absurd h0 (hs0 i)
    · exact hle
  have hfib : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), R.placeMap w = xbar →
      w.ord (s j) = -(embDivisor N w) :=
    fun w hw => GoodChart.ord_eq_neg_on_fibre R (hint j) (hres0 j) (embDivisor N) (hsE j) hjord w hw

  obtain ⟨hjinv, hjinvres⟩ := CuspUnitAssembly.inv_mem_of_residue_ne_zero R (hint j) (hres0 j)

  have hratio_mem : ∀ i', s i' * (s j)⁻¹ ∈ R.integers := fun i' => mul_mem (hint i') hjinv
  have hratio_ord : ∀ i' (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      R.placeMap w = xbar → 0 ≤ w.ord (s i' * (s j)⁻¹) := by
    intro i' w hw
    rw [w.ord_mul (hs0 i') (inv_ne_zero (hs0 j)), w.ord_inv, hfib w hw]
    have := hsE i' w
    omega
  have hratio_reg : ∀ i' (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      R.placeMap w = xbar → s i' * (s j)⁻¹ ∈ w.toValuationSubring :=
    fun i' w hw => GoodChart.mem_of_ord_nonneg w (hratio_ord i' w hw)

  have hratio_res : ∀ i', R.residue ⟨s i' * (s j)⁻¹, hratio_mem i'⟩
      = R.residue ⟨s i', hint i'⟩ * (R.residue ⟨s j, hint j⟩)⁻¹ := by
    intro i'
    have helt : (⟨s i' * (s j)⁻¹, hratio_mem i'⟩ : R.integers) = ⟨s i', hint i'⟩ * ⟨(s j)⁻¹, hjinv⟩ :=
      Subtype.ext rfl
    rw [helt, map_mul, eq_inv_of_mul_eq_one_left hjinvres]

  have hPW : R.IsPointwise := ConstantReduction.isPointwise_of_hasPrincipalDivisors R
  have hord1 : xbar.ord (R.residue ⟨s i * (s j)⁻¹, hratio_mem i⟩
      - algebraMap (IsLocalRing.ResidueField A) (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)
          (xbar.evalAt (R.residue ⟨s i * (s j)⁻¹, hratio_mem i⟩))) = 1 := by
    rw [hratio_res i]
    exact hiord
  refine ⟨j, i, hratio_mem, hjord, fun w hw => ⟨hfib w hw, fun i' => hratio_ord i' w hw⟩, hratio_res, hord1, ?_⟩
  intro v hv
  subst hv
  have hvrat : v.IsRational :=
    (Place.isRational_iff_deg_eq_one v).mpr (deg_eq_one_modularFunctionFieldBar N v)
  obtain ⟨hA, -, hval⟩ := GoodChart.evalAt_placeMap_residue R hPW hvrat (hratio_mem i) (hratio_reg i)
  exact ⟨⟨hA, hval⟩, GoodChart.isDiscParam_sub_evalAt R hPW hvrat (hratio_mem i) (hratio_reg i) hord1⟩

namespace UniformCoveringCase

private theorem isRational_of_isAlgClosed_aux {K F : Type*} [Field K] [IsAlgClosed K]
    [Field F] [Algebra K F] [IsCurveOver K F] (x : Place K F) : x.IsRational := by
  haveI hfin : Module.Finite K x.ResidueField := IsCurveOver.finiteResidue x
  haveI : Algebra.IsIntegral K x.ResidueField := Algebra.IsIntegral.of_finite K x.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := x.ResidueField)).2

open Classical in

private theorem fibre_mass_count {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*}
    [Field F] [Algebra L F] {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) {g : F} (hg : g ∈ C.integers) (hres : C.residue ⟨g, hg⟩ ≠ 0)
    {P : Place L F} (_ : P ∈ C.dom) (hPnn : C.placeMap P ∉ C.nodes)
    (D : Divisor L F) (hD : ∀ w, D w = w.ord g) :
    (C.placeMap P).ord (C.residue ⟨g, hg⟩)
      = ∑ w ∈ D.support.filter (fun w => w ∈ C.dom ∧ C.placeMap w = C.placeMap P), D w := by
  set D' := D.filter (fun w => w ∈ C.dom) with hD'
  have h1 : ∀ w ∈ C.dom, D' w = w.ord ((⟨g, hg⟩ : C.integers) : F) := fun w hw => by
    rw [hD', Finsupp.filter_apply_pos _ _ hw]; exact hD w
  have h2 : ∀ w, w ∉ C.dom → D' w = 0 := fun w hw => by
    rw [hD', Finsupp.filter_apply_neg _ _ hw]
  have hmd := C.mapDomain_placeMap ⟨g, hg⟩ hres D' h1 h2 (C.placeMap P) hPnn
  rw [← hmd]
  have hsupp : D'.support.filter (fun a => C.placeMap a = C.placeMap P)
      = D.support.filter (fun w => w ∈ C.dom ∧ C.placeMap w = C.placeMap P) := by
    rw [hD', Finsupp.support_filter, Finset.filter_filter]
  simp only [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.single_apply]
  rw [Finsupp.sum, Finset.sum_ite, Finset.sum_const_zero, add_zero, hsupp]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [Finset.mem_filter] at hw
  rw [hD', Finsupp.filter_apply_pos _ _ hw.2.1]

set_option maxHeartbeats 12800000 in

private theorem exists_minor_ne_zero_of_isEmbBasis (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ))
    (R : ConstantReduction A (modularFunctionFieldBar N)
      (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N))
    (hR : R.IsGood) {r : ℕ} (t : Fin r → modularFunctionFieldBar N) (ht : IsEmbBasis N t)
    (hint : ∀ i, t i ∈ R.integers)
    (hli : LinearIndependent (IsLocalRing.ResidueField A) (fun i => R.residue ⟨t i, hint i⟩))
    (cQ : Place (IsLocalRing.ResidueField A) (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) → Fin r)
    (hcQ : ∀ xbar : Place (IsLocalRing.ResidueField A) (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N),
      xbar.ord (R.residue ⟨t (cQ xbar), hint _⟩) = -(Finsupp.mapDomain R.placeMap (embDivisor N) xbar))
    (P Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hPQ : R.placeMap P ≠ R.placeMap Q)
    (hmP : ∀ j, t j * (t (cQ (R.placeMap P)))⁻¹ ∈ R.integers)
    (hmQ : ∀ j, t j * (t (cQ (R.placeMap Q)))⁻¹ ∈ R.integers) :
    ∃ i j, (R.placeMap P).evalAt (R.residue ⟨_, hmP i⟩) * (R.placeMap Q).evalAt (R.residue ⟨_, hmQ j⟩)
      ≠ (R.placeMap P).evalAt (R.residue ⟨_, hmP j⟩) * (R.placeMap Q).evalAt (R.residue ⟨_, hmQ i⟩) := by
  classical

  haveI : IsAlgClosed (IsLocalRing.ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  haveI hco : IsCurveOver (IsLocalRing.ResidueField A)
      (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :=
    isCurveOver_modularFunctionFieldFullC (IsLocalRing.ResidueField A) N
  have hspan := span_residue_eq_riemannRochSpace_of_isEmbBasis_of_isGood N A R hR t ht hint hli
  have hgb0 : ∀ i, R.residue ⟨t i, hint i⟩ ≠ 0 := fun i => hli.ne_zero i
  have hratP : (R.placeMap P).IsRational :=
    (Place.isRational_iff_deg_eq_one _).mpr (IsCurveOver.forall_deg_eq_one_of_isAlgClosed _)
  have hratQ : (R.placeMap Q).IsRational :=
    (Place.isRational_iff_deg_eq_one _).mpr (IsCurveOver.forall_deg_eq_one_of_isAlgClosed _)

  have hdegE : Divisor.degree (embDivisor N) = (embDegree N : ℤ) := by
    simp only [embDivisor]
    rw [map_zsmul, Divisor.degree_single, deg_eq_one_modularFunctionFieldBar N, Nat.cast_one, mul_one,
      smul_eq_mul, mul_one]
  have hdeg : Divisor.degree (Finsupp.mapDomain R.placeMap (embDivisor N))
      = 2 * (genusFF (IsLocalRing.ResidueField A)
        (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) : ℤ) + 1 := by
    rw [R.degree_mapDomain, hdegE]
    have hg : genusFF (IsLocalRing.ResidueField A) (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)
        = genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := hR
    rw [hg]
    unfold embDegree
    push_cast
    ring

  have hvanish : ∀ (v : Place (IsLocalRing.ResidueField A) (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N))
      (f : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N), 0 < v.ord f → v.evalAt f = 0 := by
    intro v f hpos
    have hf : f ∈ v.toValuationSubring := GoodChart.mem_of_ord_nonneg v hpos.le
    have hnu : ¬ IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
      intro hu
      obtain ⟨y, hy⟩ := hu.exists_right_inv
      have hfy : f * (y : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) = 1 := by
        exact congrArg Subtype.val hy
      have hinv : f⁻¹ ∈ v.toValuationSubring := by
        rw [← eq_inv_of_mul_eq_one_right hfy]
        exact y.2
      have hnn := GoodChart.ord_nonneg_of_mem v hinv
      rw [v.ord_inv] at hnn
      omega
    have hres : IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ = 0 := by
      by_contra h
      exact hnu ((IsLocalRing.residue_ne_zero_iff_isUnit _).mp h)
    rw [v.evalAt_of_mem hf, hres]
    have h0 := v.residueInv_algebraMap (0 : IsLocalRing.ResidueField A)
    rw [map_zero] at h0
    exact h0

  have hadd : ∀ (v : Place (IsLocalRing.ResidueField A) (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)),
      v.IsRational → ∀ {f g : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N},
      f ∈ v.toValuationSubring → g ∈ v.toValuationSubring → v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
    intro v hv f g hf hg
    apply v.algebraMap_residueField_injective
    rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg,
      ← map_add]
    rfl
  have hzero : ∀ v : Place (IsLocalRing.ResidueField A) (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N),
      v.evalAt (0 : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) = 0 := by
    intro v
    have h := v.evalAt_algebraMap_eq (0 : IsLocalRing.ResidueField A)
    rwa [map_zero] at h

  have hreg : ∀ (v : Place (IsLocalRing.ResidueField A) (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N))
      (a : Fin r), v.ord (R.residue ⟨t a, hint a⟩) = -(Finsupp.mapDomain R.placeMap (embDivisor N) v) →
      ∀ x ∈ riemannRochSpace (Finsupp.mapDomain R.placeMap (embDivisor N)),
        x * (R.residue ⟨t a, hint a⟩)⁻¹ ∈ v.toValuationSubring := by
    intro v a ha x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [zero_mul]
      exact zero_mem _
    refine GoodChart.mem_of_ord_nonneg v ?_
    rw [v.ord_mul hx0 (inv_ne_zero (hgb0 a)), v.ord_inv, ha]
    rcases (mem_riemannRochSpace_iff.mp hx) v with h0 | hle
    · exact absurd h0 hx0
    · omega
  have hregP : ∀ x ∈ Submodule.span (IsLocalRing.ResidueField A) (Set.range fun i => R.residue ⟨t i, hint i⟩),
      x * (R.residue ⟨t (cQ (R.placeMap P)), hint _⟩)⁻¹ ∈ (R.placeMap P).toValuationSubring :=
    fun x hx => hreg _ _ (hcQ (R.placeMap P)) x (le_of_eq hspan hx)
  have hregQ : ∀ x ∈ Submodule.span (IsLocalRing.ResidueField A) (Set.range fun i => R.residue ⟨t i, hint i⟩),
      x * (R.residue ⟨t (cQ (R.placeMap Q)), hint _⟩)⁻¹ ∈ (R.placeMap Q).toValuationSubring :=
    fun x hx => hreg _ _ (hcQ (R.placeMap Q)) x (le_of_eq hspan hx)

  have hresP : ∀ i, R.residue ⟨t i * (t (cQ (R.placeMap P)))⁻¹, hmP i⟩
      = R.residue ⟨t i, hint i⟩ * (R.residue ⟨t (cQ (R.placeMap P)), hint _⟩)⁻¹ := by
    intro i
    obtain ⟨hainv, hainvres⟩ :=
      CuspUnitAssembly.inv_mem_of_residue_ne_zero R (hint (cQ (R.placeMap P))) (hgb0 (cQ (R.placeMap P)))
    have helt : (⟨t i * (t (cQ (R.placeMap P)))⁻¹, hmP i⟩ : R.integers)
        = ⟨t i, hint i⟩ * ⟨(t (cQ (R.placeMap P)))⁻¹, hainv⟩ := Subtype.ext rfl
    rw [helt, map_mul, eq_inv_of_mul_eq_one_left hainvres]
  have hresQ : ∀ i, R.residue ⟨t i * (t (cQ (R.placeMap Q)))⁻¹, hmQ i⟩
      = R.residue ⟨t i, hint i⟩ * (R.residue ⟨t (cQ (R.placeMap Q)), hint _⟩)⁻¹ := by
    intro i
    obtain ⟨hbinv, hbinvres⟩ :=
      CuspUnitAssembly.inv_mem_of_residue_ne_zero R (hint (cQ (R.placeMap Q))) (hgb0 (cQ (R.placeMap Q)))
    have helt : (⟨t i * (t (cQ (R.placeMap Q)))⁻¹, hmQ i⟩ : R.integers)
        = ⟨t i, hint i⟩ * ⟨(t (cQ (R.placeMap Q)))⁻¹, hbinv⟩ := Subtype.ext rfl
    rw [helt, map_mul, eq_inv_of_mul_eq_one_left hbinvres]

  by_contra hall
  push Not at hall
  have hprop : ∀ i,
      (R.placeMap Q).evalAt (R.residue ⟨t i, hint i⟩ * (R.residue ⟨t (cQ (R.placeMap Q)), hint _⟩)⁻¹)
        = (R.placeMap P).evalAt (R.residue ⟨t i, hint i⟩ * (R.residue ⟨t (cQ (R.placeMap P)), hint _⟩)⁻¹)
          * (R.placeMap Q).evalAt (R.residue ⟨t (cQ (R.placeMap P)), hint _⟩
              * (R.residue ⟨t (cQ (R.placeMap Q)), hint _⟩)⁻¹) := by
    intro i
    have h := hall i (cQ (R.placeMap P))
    rw [hresP i, hresQ (cQ (R.placeMap P)), hresP (cQ (R.placeMap P)), hresQ i,
      mul_inv_cancel₀ (hgb0 (cQ (R.placeMap P))), Place.evalAt_one, one_mul] at h
    exact h.symm

  have key : ∀ x ∈ Submodule.span (IsLocalRing.ResidueField A) (Set.range fun i => R.residue ⟨t i, hint i⟩),
      (R.placeMap Q).evalAt (x * (R.residue ⟨t (cQ (R.placeMap Q)), hint _⟩)⁻¹)
        = (R.placeMap P).evalAt (x * (R.residue ⟨t (cQ (R.placeMap P)), hint _⟩)⁻¹)
          * (R.placeMap Q).evalAt (R.residue ⟨t (cQ (R.placeMap P)), hint _⟩
              * (R.residue ⟨t (cQ (R.placeMap Q)), hint _⟩)⁻¹) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hprop i
    | zero => simp [hzero]
    | add x y hx hy ihx ihy =>
      rw [add_mul, add_mul, hadd _ hratQ (hregQ x hx) (hregQ y hy), hadd _ hratP (hregP x hx) (hregP y hy),
        ihx, ihy]
      ring
    | smul c x hx ih =>
      rw [Algebra.smul_def, mul_assoc, mul_assoc,
        (R.placeMap Q).evalAt_mul_of_mem hratQ ((R.placeMap Q).algebraMap_mem' c) (hregQ x hx),
        (R.placeMap P).evalAt_mul_of_mem hratP ((R.placeMap P).algebraMap_mem' c) (hregP x hx),
        Place.evalAt_algebraMap_eq, Place.evalAt_algebraMap_eq, ih]
      ring

  obtain ⟨u, hu1, hu2⟩ := ReducedChart.exists_mem_notMem (IsLocalRing.ResidueField A) N
    (Finsupp.mapDomain R.placeMap (embDivisor N) - Finsupp.single (R.placeMap P) 1)
    (by rw [map_sub, Divisor.degree_single,
          IsCurveOver.forall_deg_eq_one_of_isAlgClosed (K := IsLocalRing.ResidueField A) (R.placeMap P), hdeg]
        push_cast
        omega)
    (R.placeMap Q)
  obtain ⟨hu0, huQ⟩ := ReducedChart.ord_eq_of_mem_notMem hu1 hu2
  rw [Finsupp.sub_apply, Finsupp.single_eq_of_ne hPQ.symm, sub_zero] at huQ
  have huD : u ∈ riemannRochSpace (Finsupp.mapDomain R.placeMap (embDivisor N)) :=
    ReducedChart.riemannRochSpace_sub_single_le (Finsupp.mapDomain R.placeMap (embDivisor N)) (R.placeMap P) hu1
  have huP : -(Finsupp.mapDomain R.placeMap (embDivisor N) (R.placeMap P)) + 1 ≤ (R.placeMap P).ord u := by
    rcases (mem_riemannRochSpace_iff.mp hu1) (R.placeMap P) with h0 | hle
    · exact absurd h0 hu0
    · rw [Finsupp.sub_apply, Finsupp.single_eq_same] at hle
      omega

  have hφP : (R.placeMap P).evalAt (u * (R.residue ⟨t (cQ (R.placeMap P)), hint _⟩)⁻¹) = 0 := by
    refine hvanish _ _ ?_
    rw [(R.placeMap P).ord_mul hu0 (inv_ne_zero (hgb0 (cQ (R.placeMap P)))), (R.placeMap P).ord_inv,
      hcQ (R.placeMap P)]
    omega
  have hφQ : (R.placeMap Q).evalAt (u * (R.residue ⟨t (cQ (R.placeMap Q)), hint _⟩)⁻¹) ≠ 0 := by
    refine (R.placeMap Q).evalAt_ne_zero_of_ord_eq_zero hratQ
      (mul_ne_zero hu0 (inv_ne_zero (hgb0 (cQ (R.placeMap Q))))) ?_
    rw [(R.placeMap Q).ord_mul hu0 (inv_ne_zero (hgb0 (cQ (R.placeMap Q)))), (R.placeMap Q).ord_inv,
      hcQ (R.placeMap Q)]
    omega
  have hk := key u (le_of_eq hspan.symm huD)
  rw [hφP, zero_mul] at hk
  exact hφQ hk

end UniformCoveringCase

open UniformCoveringCase

set_option maxHeartbeats 6400000 in

theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (p : ℕ) (hp : p.Prime)
    (hpN : ¬ p ∣ N) :
    ∃ (n m B k : ℕ) (Cc : ℝ), ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
    ∃ (Fbar : Fin n → Type) (_ : ∀ i, Field (Fbar i))
      (_ : ∀ i, Algebra (IsLocalRing.ResidueField ↥A) (Fbar i))
      (C : ∀ i, ComponentChart A (modularFunctionFieldBar N) (Fbar i))
      (An An' : Fin m → Annulus A (modularFunctionFieldBar N)) (src tgt : Fin m → Fin n)
      (xs : ∀ e, Place (IsLocalRing.ResidueField ↥A) (Fbar (src e)))
      (xt : ∀ e, Place (IsLocalRing.ResidueField ↥A) (Fbar (tgt e)))
      (T : ∀ i, Place (IsLocalRing.ResidueField ↥A) (Fbar i) → modularFunctionFieldBar N),
      (∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
        ((An e).modulus : AlgebraicClosure ℚ) ≠ 0 ∧
        (An' e).param * (An e).param
          = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ((An e).modulus : AlgebraicClosure ℚ)) ∧
      (∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e)) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)))
            (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)))
            (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E') ∧
      (∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
        (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom)) ∧
      (∃ i, cuspInftyBar N ∈ (C i).dom ∧
        ∀ l : Fin r, ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧ (p : AlgebraicClosure ℚ) ^ B * c ∈ A ∧
          (p : AlgebraicClosure ℚ) ^ B * c⁻¹ ∈ A ∧
          ∃ h : c • s l ∈ (C i).integers, (C i).residue ⟨c • s l, h⟩ ≠ 0) ∧
      (∀ i, HasPrincipalDivisors (IsLocalRing.ResidueField ↥A) (Fbar i) ∧
        ∀ x : Place (IsLocalRing.ResidueField ↥A) (Fbar i), x.IsRational) ∧
      (∀ i j : Fin n, Relation.ReflTransGen
        (fun a b : Fin n => ∃ e, (src e = a ∧ tgt e = b) ∨ (src e = b ∧ tgt e = a)) i j) ∧
      (∀ e, ∃ a : AlgebraicClosure ℚ, a ∈ A ∧
        (p : AlgebraicClosure ℚ) ^ k = ((An e).modulus : AlgebraicClosure ℚ) * a) ∧
      (∀ i, ∀ P ∈ (C i).dom,
        ∃ h : T i ((C i).placeMap P)
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (P.evalAt (T i ((C i).placeMap P)))
              ∈ (C i).integers,
          (C i).residue ⟨_, h⟩ ≠ 0 ∧ ((C i).placeMap P).ord ((C i).residue ⟨_, h⟩) = 1 ∧
          0 < P.ord (T i ((C i).placeMap P)
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (P.evalAt (T i ((C i).placeMap P)))) ∧
          ∀ Q ∈ (C i).dom, (C i).placeMap Q = (C i).placeMap P → Q ≠ P →
            Q.ord (T i ((C i).placeMap P)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (P.evalAt (T i ((C i).placeMap P)))) = 0) ∧
      (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
        (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
        ∀ e, ∀ P ∈ (An e).dom, ∀ Q ∈ (An e).dom, P ≠ Q →
          (∃ i j, evalVec s P i * evalVec s Q j ≠ evalVec s P j * evalVec s Q i) →
          |prox μ (evalVec s P) (evalVec s Q)
              + Real.log (μ (P.evalAt (An e).param - Q.evalAt (An e).param))|
            ≤ Cc * (-Real.log (μ ((An e).modulus : AlgebraicClosure ℚ)))) ∧
      (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
        (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
        ∀ i, ∀ P ∈ (C i).dom, ∀ Q ∈ (C i).dom, P ≠ Q →
          (∃ i' j', evalVec s P i' * evalVec s Q j' ≠ evalVec s P j' * evalVec s Q i') →
          ((C i).placeMap P = (C i).placeMap Q →
            |prox μ (evalVec s P) (evalVec s Q)
                + Real.log (μ (P.evalAt (T i ((C i).placeMap P)) - Q.evalAt (T i ((C i).placeMap P))))|
              ≤ Cc * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
          ((C i).placeMap P ≠ (C i).placeMap Q →
            |prox μ (evalVec s P) (evalVec s Q)| ≤ Cc * (-Real.log (μ (p : AlgebraicClosure ℚ))))) ∧
      (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
        (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
        ∀ P Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
          (∀ i, P ∈ (C i).dom → Q ∉ (C i).dom) → (∀ e, P ∈ (An e).dom → Q ∉ (An e).dom) →
          |prox μ (evalVec s P) (evalVec s Q)| ≤ Cc * (-Real.log (μ (p : AlgebraicClosure ℚ)))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨B₁, hwin⟩ := ModularCurve.exists_uniform_window_smul_mem_integers N s hs p hp hpN
  obtain ⟨B₂, hadapt⟩ := ModularCurve.exists_uniform_adapted_basis N s hs p hp hpN

  refine ⟨1, 0, B₁, 0, (B₂ : ℝ), ?_⟩
  intro A hA

  obtain ⟨R, hGood, hDeur⟩ :=
    ModularCurve.exists_constantReduction_isGood_isPlaceReductionModL N hpN A hA
  haveI := ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  have hR : R.IsPointwise :=
    AlgebraicCurve.ConstantReduction.isPointwise_of_hasPrincipalDivisors R

  obtain ⟨s', hs', hint, hli, hdistort⟩ := hadapt A hA R hGood hDeur
  have hres0 : ∀ l, R.residue ⟨s' l, hint l⟩ ≠ 0 := fun l => hli.ne_zero l
  have hsne' : ∀ l, s' l ≠ 0 := fun l => hs'.1.ne_zero l

  have hCD := fun xbar =>
    exists_chartData_of_pinnedBasis N s' hs' A R hGood hint hres0 hli xbar

  let cQ : Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N) → Fin r :=
    fun xbar => (hCD xbar).choose
  let iQ : Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N) → Fin r :=
    fun xbar => (hCD xbar).choose_spec.choose
  have hCDspec : ∀ xbar, ∃ hratio : ∀ i', s' i' * (s' (cQ xbar))⁻¹ ∈ R.integers,
      xbar.ord (R.residue ⟨s' (cQ xbar), hint _⟩) = -(Finsupp.mapDomain R.placeMap (embDivisor N) xbar) ∧
      (∀ w, R.placeMap w = xbar → w.ord (s' (cQ xbar)) = -(embDivisor N w) ∧
        ∀ i', 0 ≤ w.ord (s' i' * (s' (cQ xbar))⁻¹)) ∧
      (∀ i', R.residue ⟨s' i' * (s' (cQ xbar))⁻¹, hratio i'⟩
        = R.residue ⟨s' i', hint i'⟩ * (R.residue ⟨s' (cQ xbar), hint _⟩)⁻¹) ∧
      xbar.ord (R.residue ⟨s' (iQ xbar) * (s' (cQ xbar))⁻¹, hratio _⟩
        - algebraMap (ResidueField ↥A) _ (xbar.evalAt (R.residue ⟨_, hratio (iQ xbar)⟩))) = 1 ∧
      ∀ v, R.placeMap v = xbar →
        (∃ h : v.evalAt (s' (iQ xbar) * (s' (cQ xbar))⁻¹) ∈ A,
          xbar.evalAt (R.residue ⟨_, hratio (iQ xbar)⟩) = IsLocalRing.residue A ⟨_, h⟩) ∧
        R.IsDiscParam v (s' (iQ xbar) * (s' (cQ xbar))⁻¹
          - algebraMap (AlgebraicClosure ℚ) _ (v.evalAt (s' (iQ xbar) * (s' (cQ xbar))⁻¹))) :=
    fun xbar => (hCD xbar).choose_spec.choose_spec

  refine ⟨fun _ => modularFunctionFieldFullC (ResidueField ↥A) N,
    fun _ => inferInstance, fun _ => inferInstance,
    fun _ => ComponentChart.ofConstantReduction R hR,
    Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, ?T,
    ?c1, ?c2, ?c3, ?cEND, ?c4, ?c5, ?cRES, ?cCONN, ?cTHICK, ?cDISC, ?cCMP, ?cCHARTCMP, ?cFAR⟩

  case T =>
    exact fun _ xbar => s' (iQ xbar) * (s' (cQ xbar))⁻¹

  case c1 => exact fun e => e.elim0
  case c2 => exact fun e => e.elim0
  case c3 =>
    intro i x hx
    exact absurd hx (by simp [ComponentChart.ofConstantReduction_nodes])

  case cEND =>
    intro i x hx
    exact absurd hx (by simp [ComponentChart.ofConstantReduction_nodes])
  case c4 =>
    intro P
    exact Or.inl ⟨0, by simp [ComponentChart.ofConstantReduction_dom],
      fun j _ => Subsingleton.elim j 0, fun e => e.elim0⟩
  case cTHICK => exact fun e => e.elim0
  case cCMP => exact fun _ _ _ e => e.elim0

  case cCONN => exact fun i j => Subsingleton.elim i j ▸ Relation.ReflTransGen.refl

  case cFAR =>
    intro μ _ _ P Q hPQ _
    exact absurd (by simp [ComponentChart.ofConstantReduction_dom] : Q ∈ _) (hPQ 0 (by
      simp [ComponentChart.ofConstantReduction_dom]))
  case c5 =>
    refine ⟨0, by simp [ComponentChart.ofConstantReduction_dom], fun l => ?_⟩
    obtain ⟨c, hc0, hcB, hcB', hcmem, hcres⟩ := hwin A hA R hGood hDeur l
    refine ⟨c, hc0, hcB, hcB', ?_⟩
    simp only [ComponentChart.ofConstantReduction_integers]
    exact ⟨hcmem, hcres⟩

  case cRES =>
    intro i
    haveI hAC : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A
    haveI hCO : IsCurveOver (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N) :=
      ModularCurve.isCurveOver_modularFunctionFieldFullC (ResidueField ↥A) N
    exact ⟨IsCurveOver.hasPrincipalDivisors, fun x => UniformCoveringCase.isRational_of_isAlgClosed_aux x⟩

  case cDISC =>
    intro i P _

    simp only [ComponentChart.ofConstantReduction_placeMap,
      ComponentChart.ofConstantReduction_integers,
      ComponentChart.ofConstantReduction_dom, Set.mem_univ, forall_true_left] at *

    obtain ⟨hratio, -, -, -, hord1, hpt⟩ := hCDspec (R.placeMap P)
    obtain ⟨-, hDP⟩ := hpt P rfl
    obtain ⟨hTmem, hTres0, hTord, hPpos, hQnn⟩ := hDP
    refine ⟨hTmem, hTres0, hTord, hPpos, ?iso⟩

    intro Q hQP hne
    classical

    have hT_ne : s' (iQ (R.placeMap P)) * (s' (cQ (R.placeMap P)))⁻¹
        - algebraMap (AlgebraicClosure ℚ) _
            (P.evalAt (s' (iQ (R.placeMap P)) * (s' (cQ (R.placeMap P)))⁻¹)) ≠ 0 := by
      intro h
      apply hTres0
      have : (⟨_, hTmem⟩ : R.integers) = 0 := Subtype.ext h
      rw [this, map_zero]
    haveI := ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
    obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) _ hT_ne

    have hsum := UniformCoveringCase.fibre_mass_count (ComponentChart.ofConstantReduction R hR) hTmem hTres0
      (P := P) (by simp [ComponentChart.ofConstantReduction_dom])
      (by simp [ComponentChart.ofConstantReduction_nodes]) D hD
    simp only [ComponentChart.ofConstantReduction_placeMap,
      ComponentChart.ofConstantReduction_dom, Set.mem_univ, true_and] at hsum

    have hsum1 : (1 : ℤ)
        = ∑ w ∈ D.support.filter (fun w => R.placeMap w = R.placeMap P), D w := by
      rw [← hTord]; exact hsum
    clear hsum
    set S := D.support.filter (fun w => R.placeMap w = R.placeMap P) with hS
    have hnn : ∀ w ∈ S, 0 ≤ D w := fun w hwS => by
      rw [hD w]; exact hQnn w (Finset.mem_filter.mp hwS).2
    have hPordD : D P = P.ord _ := hD P
    have hPS : P ∈ S := by
      rw [hS, Finset.mem_filter, Finsupp.mem_support_iff, hD P]
      exact ⟨by omega, rfl⟩

    by_cases hQS : Q ∈ S
    · have hsum' : ∑ w ∈ S, D w = 1 := hsum1.symm
      have hDPle : D P ≤ 1 :=
        le_of_le_of_eq (Finset.single_le_sum hnn hPS) hsum'
      have hDQnn : 0 ≤ D Q := hnn Q hQS
      have : D P + D Q ≤ ∑ w ∈ S, D w := by
        have hins : ({P, Q} : Finset _) ⊆ S := by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with h | h <;> subst h <;> assumption
        calc D P + D Q = ∑ w ∈ ({P, Q} : Finset _), D w := by
              rw [Finset.sum_pair hne.symm]
          _ ≤ ∑ w ∈ S, D w :=
              Finset.sum_le_sum_of_subset_of_nonneg hins (fun w hw _ => hnn w hw)
      rw [hsum'] at this
      have : D Q = 0 := by omega
      rw [← hD Q]; exact this
    · rw [← hD Q]
      by_contra hDQ
      exact hQS (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hDQ, hQP⟩)
  case cCHARTCMP =>
    intro μ hμ hμA i P _ Q _ hPQ hnp
    simp only [ComponentChart.ofConstantReduction_placeMap,
      ComponentChart.ofConstantReduction_dom, Set.mem_univ] at *
    haveI hAC : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A
    haveI hCO : IsCurveOver (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N) :=
      ModularCurve.isCurveOver_modularFunctionFieldFullC (ResidueField ↥A) N
    haveI hCOBar : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
      ModularCurve.isCurveOver_modularFunctionFieldBar N
    have hrat' : ∀ P' ∈ (ComponentChart.ofConstantReduction R hR).dom,
        P'.IsRational ∧ ((ComponentChart.ofConstantReduction R hR).placeMap P').IsRational := by
      intro P' _
      simp only [ComponentChart.ofConstantReduction_placeMap]
      exact ⟨UniformCoveringCase.isRational_of_isAlgClosed_aux P',
        UniformCoveringCase.isRational_of_isAlgClosed_aux (R.placeMap P')⟩
    have hcQ' : ∀ P' ∈ (ComponentChart.ofConstantReduction R hR).dom,
        (ComponentChart.ofConstantReduction R hR).residue
          ⟨s' (cQ ((ComponentChart.ofConstantReduction R hR).placeMap P')), hint _⟩ ≠ 0 := by
      intro P' _
      exact hres0 (cQ (R.placeMap P'))
    have hratio' : ∀ P' ∈ (ComponentChart.ofConstantReduction R hR).dom,
        ∀ j, s' j * (s' (cQ ((ComponentChart.ofConstantReduction R hR).placeMap P')))⁻¹
          ∈ (ComponentChart.ofConstantReduction R hR).integers := by
      intro P' _ j
      exact (hCDspec (R.placeMap P')).choose j

    have hreg' : ∀ P' ∈ (ComponentChart.ofConstantReduction R hR).dom,
        ∀ j, s' j * (s' (cQ ((ComponentChart.ofConstantReduction R hR).placeMap P')))⁻¹
          ∈ P'.toValuationSubring := by
      intro P' _ j
      have hnn := ((hCDspec (R.placeMap P')).choose_spec.2.1 P' rfl).2 j
      exact P'.mem_toValuationSubring_of_ord_nonneg_alt
        (mul_ne_zero (hsne' j) (inv_ne_zero (hsne' _))) hnn

    have himm' : ∀ P' ∈ (ComponentChart.ofConstantReduction R hR).dom,
        ∀ hmem : s' (iQ ((ComponentChart.ofConstantReduction R hR).placeMap P'))
            * (s' (cQ ((ComponentChart.ofConstantReduction R hR).placeMap P')))⁻¹
          ∈ (ComponentChart.ofConstantReduction R hR).integers,
        ((ComponentChart.ofConstantReduction R hR).placeMap P').ord
          ((ComponentChart.ofConstantReduction R hR).residue ⟨_, hmem⟩
            - algebraMap (ResidueField ↥A) _
                (((ComponentChart.ofConstantReduction R hR).placeMap P').evalAt
                  ((ComponentChart.ofConstantReduction R hR).residue ⟨_, hmem⟩))) = 1 := by
      intro P' _ hmem
      exact (hCDspec (R.placeMap P')).choose_spec.2.2.2.1
    have hcQord : ∀ xbar : Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N),
        xbar.ord (R.residue ⟨s' (cQ xbar), hint _⟩) = -(Finsupp.mapDomain R.placeMap (embDivisor N) xbar) :=
      fun xbar => (hCDspec xbar).choose_spec.1
    have hsep' : ∀ P' ∈ (ComponentChart.ofConstantReduction R hR).dom,
        ∀ Q' ∈ (ComponentChart.ofConstantReduction R hR).dom,
        (ComponentChart.ofConstantReduction R hR).placeMap P'
          ≠ (ComponentChart.ofConstantReduction R hR).placeMap Q' →
        ∀ (hmP : ∀ j, s' j * (s' (cQ ((ComponentChart.ofConstantReduction R hR).placeMap P')))⁻¹
            ∈ (ComponentChart.ofConstantReduction R hR).integers)
          (hmQ : ∀ j, s' j * (s' (cQ ((ComponentChart.ofConstantReduction R hR).placeMap Q')))⁻¹
            ∈ (ComponentChart.ofConstantReduction R hR).integers),
        ∃ i j, ((ComponentChart.ofConstantReduction R hR).placeMap P').evalAt
              ((ComponentChart.ofConstantReduction R hR).residue ⟨_, hmP i⟩)
            * ((ComponentChart.ofConstantReduction R hR).placeMap Q').evalAt
              ((ComponentChart.ofConstantReduction R hR).residue ⟨_, hmQ j⟩)
          ≠ ((ComponentChart.ofConstantReduction R hR).placeMap P').evalAt
              ((ComponentChart.ofConstantReduction R hR).residue ⟨_, hmP j⟩)
            * ((ComponentChart.ofConstantReduction R hR).placeMap Q').evalAt
              ((ComponentChart.ofConstantReduction R hR).residue ⟨_, hmQ i⟩) := by
      intro P' _ Q' _ hne hmP hmQ
      exact UniformCoveringCase.exists_minor_ne_zero_of_isEmbBasis N A R hGood s' hs' hint hli cQ hcQord
        P' Q' hne hmP hmQ
    have hDJ := AlgebraicCurve.ComponentChart.prox_eq_of_chartData_of_minor
      (ComponentChart.ofConstantReduction R hR) s' hint cQ iQ
      hrat' hcQ' hratio' hreg' himm' hsep' μ hμ hμA P
      (by simp [ComponentChart.ofConstantReduction_dom]) Q
      (by simp [ComponentChart.ofConstantReduction_dom]) hPQ
    simp only [ComponentChart.ofConstantReduction_placeMap] at hDJ

    have hregP : ∀ j, 0 ≤ P.ord (s' j * (s' (cQ (R.placeMap P)))⁻¹) :=
      ((hCDspec (R.placeMap P)).choose_spec.2.1 P rfl).2
    have hregQ : ∀ j, 0 ≤ Q.ord (s' j * (s' (cQ (R.placeMap Q)))⁻¹) :=
      ((hCDspec (R.placeMap Q)).choose_spec.2.1 Q rfl).2
    refine ⟨fun hsame => ?_, fun hdiff => ?_⟩
    ·
      have hregQ' : ∀ j, 0 ≤ Q.ord (s' j * (s' (cQ (R.placeMap P)))⁻¹) :=
        ((hCDspec (R.placeMap P)).choose_spec.2.1 Q hsame.symm).2
      have hdist := hdistort μ hμ hμA P Q (cQ (R.placeMap P)) (cQ (R.placeMap P)) hregP hregQ' hnp
      have hE : prox (μ : AlgebraicClosure ℚ → ℝ)
            (fun j => P.evalAt (s' j * (s' (cQ (R.placeMap P)))⁻¹))
            (fun j => Q.evalAt (s' j * (s' (cQ (R.placeMap P)))⁻¹))
          = -Real.log (μ (Q.evalAt (s' (iQ (R.placeMap P)) * (s' (cQ (R.placeMap P)))⁻¹)
              - P.evalAt (s' (iQ (R.placeMap P)) * (s' (cQ (R.placeMap P)))⁻¹))) := hDJ.2 hsame
      have hsign : μ (Q.evalAt (s' (iQ (R.placeMap P)) * (s' (cQ (R.placeMap P)))⁻¹)
              - P.evalAt (s' (iQ (R.placeMap P)) * (s' (cQ (R.placeMap P)))⁻¹))
          = μ (P.evalAt (s' (iQ (R.placeMap P)) * (s' (cQ (R.placeMap P)))⁻¹)
              - Q.evalAt (s' (iQ (R.placeMap P)) * (s' (cQ (R.placeMap P)))⁻¹)) := by
        exact μ.map_sub _ _
      rw [hE, sub_neg_eq_add, hsign] at hdist
      exact hdist
    ·
      have hdist := hdistort μ hμ hμA P Q (cQ (R.placeMap P)) (cQ (R.placeMap Q)) hregP hregQ hnp
      have hE : prox (μ : AlgebraicClosure ℚ → ℝ)
            (fun j => P.evalAt (s' j * (s' (cQ (R.placeMap P)))⁻¹))
            (fun j => Q.evalAt (s' j * (s' (cQ (R.placeMap Q)))⁻¹)) = 0 := hDJ.1 hdiff
      rw [hE, sub_zero] at hdist
      exact hdist

#print axioms solution

end S_ModularCurve_exists_uniform_dualGraphCovering_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_exists_uniform_dualGraphCovering_of_not_dvd (solution)
