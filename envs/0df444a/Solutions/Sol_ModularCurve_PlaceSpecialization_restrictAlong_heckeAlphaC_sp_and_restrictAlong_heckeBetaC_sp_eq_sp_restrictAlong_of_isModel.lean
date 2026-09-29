-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.restrictAlong_heckeAlphaC_sp_and_restrictAlong_heckeBetaC_sp_eq_sp_restrictAlong_of_isModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/2dfa87c2-dedc-5839-9eb4-9924cc2614f2

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_regularProlongation_sp_jq_jqN
import Theorems.Thm_ModularCurve_exists_charLDegeneracyRoof_regularProlongation_heckeCompat_restrictAlong_eq_of_ne
import Theorems.Thm_ModularCurve_regularProlongation_integers_eq_and_coe_residue_eq_of_residue_jq_jqN
import Theorems.Thm_AlgebraicCurve_RegularProlongation_placeMap_unique_of_forall_mapDomain_eq_ord
import Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldC_mul
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_relfinrank_full_eq_dedekindPsi
import Theorems.Thm_ModularCurve_relfinrank_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_AlgebraicCurve_Place_restrictAlong_inclusion_of_le_of_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_restrictAlong_heckeAlphaC_sp_and_restrictAlong_heckeBetaC_sp_eq_sp_restrictAlong_of_isModel
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply"
p2m_attr_erase "simp" "ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.cuspCount_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero"
p2m_attr_erase "simp" "WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec"

set_option autoImplicit false
set_option Elab.async false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~dedekindPsi_pos"

namespace SpecSquare

section Seam

variable {k : Type*} [Field k] {E : Type*} [Field E] [Algebra k E]

theorem restrictAlong_inclusion_bijective_of_eq {S T : IntermediateField k E} (h : S = T)
    (hle : S ≤ T) (hι : (IntermediateField.inclusion hle).toRingHom.IsIntegral) :
    Function.Bijective
        (Place.restrictAlong (K := k) (IntermediateField.inclusion hle) hι) ∧
      ∀ (Q : Place k T) (y : S),
        (Q.restrictAlong (IntermediateField.inclusion hle) hι).ord y
          = Q.ord (IntermediateField.inclusion hle y) := by
  subst h
  obtain ⟨hrt, -, -, hord⟩ :=
    AlgebraicCurve.Place.restrictAlong_inclusion_of_le_of_le hle hle hι hι
  have hinv : Function.Involutive
      (Place.restrictAlong (K := k) (IntermediateField.inclusion hle) hι) := hrt
  exact ⟨hinv.bijective, hord⟩

theorem isCurveOver_of_eq {S T : IntermediateField k E} (h : S = T) (hT : IsCurveOver k T) :
    IsCurveOver k S := by
  subst h
  exact hT

end Seam

section Degree

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

theorem comap_val_adjoin_simple (M : IntermediateField K E) (z : M) :
    (IntermediateField.adjoin K ({(z : E)} : Set E)).comap M.val
      = IntermediateField.adjoin K ({z} : Set M) := by
  ext y
  change (y : E) ∈ IntermediateField.adjoin K ({(z : E)} : Set E) ↔ _
  rw [← IntermediateField.lift_adjoin_simple K M z]
  exact IntermediateField.mem_lift y

theorem finrank_adjoin_simple_eq_relfinrank (M : IntermediateField K E) (z : M) :
    Module.finrank (IntermediateField.adjoin K ({z} : Set M)) M
      = IntermediateField.relfinrank (IntermediateField.adjoin K ({(z : E)} : Set E)) M := by
  rw [← comap_val_adjoin_simple M z, IntermediateField.finrank_comap,
    IntermediateField.fieldRange_val]

end Degree

section LevelN

theorem dedekindPsi_pos (N : ℕ) [NeZero N] : 0 < dedekindPsi N := by
  unfold dedekindPsi
  have h1 : (1 : ℕ) ∈ N.divisors.filter Squarefree :=
    Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr (NeZero.ne N), squarefree_one⟩
  have hle : N / 1 ≤ ∑ d ∈ N.divisors with Squarefree d, N / d :=
    Finset.single_le_sum (f := fun d => N / d) (fun _ _ => Nat.zero_le _) h1
  rw [Nat.div_one] at hle
  exact lt_of_lt_of_le (Nat.pos_of_ne_zero (NeZero.ne N)) hle

noncomputable def jB (N : ℕ) [NeZero N] : modularFunctionFieldBar N :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩

noncomputable def jNB (N : ℕ) [NeZero N] : modularFunctionFieldBar N :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (dvd_refl N))⟩

theorem finrank_adjoin_jB (N : ℕ) [NeZero N] :
    Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({jB N} : Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N)
      = dedekindPsi N := by
  refine (finrank_adjoin_simple_eq_relfinrank (modularFunctionFieldBar N) (jB N)).trans ?_
  change IntermediateField.relfinrank (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({coeffEmb (AlgebraicClosure ℚ) jq} : Set (LaurentSeries (AlgebraicClosure ℚ))))
    (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) = _
  rw [relfinrank_laurentBaseChange_modularFunctionFieldFull, relfinrank_full_eq_dedekindPsi]

theorem finrank_adjoin_jqModC (k : Type*) [Field k] (N : ℕ) [NeZero N]
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

theorem finrank_adjoin_pos_of_eq (k : Type*) [Field k] (M : ℕ) [NeZero M]
    (p : ℕ) [Fact p.Prime] [CharP k p] (hpM : ¬ p ∣ M)
    {S : IntermediateField k (LaurentSeries k)} (hS : S = modularFunctionFieldC k M)
    (y : S) (hy : (y : LaurentSeries k) = jqModC k) :
    0 < Module.finrank (IntermediateField.adjoin k ({y} : Set S)) S := by
  subst hS
  obtain rfl : y = ⟨jqModC k, jqModC_mem k M⟩ := Subtype.ext hy
  rw [finrank_adjoin_jqModC k M p hpM]
  exact dedekindPsi_pos M

theorem heckeAlphaBar_jB (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] :
    heckeAlphaBar (AlgebraicClosure ℚ) N ℓ (jB N) = jB (N * ℓ) :=
  Subtype.ext (coe_heckeAlphaBar N ℓ (jB N))

theorem heckeBetaBar_jNB (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] :
    heckeBetaBar (AlgebraicClosure ℚ) N ℓ (jNB N) = jNB (N * ℓ) := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  apply Subtype.ext
  rw [coe_heckeBetaBar]
  show qExpand (AlgebraicClosure ℚ) ℓ (coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (qExpand ℚ N jq))
    = coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (qExpand ℚ (N * ℓ) jq)
  rw [coeffMap_qExpand, coeffMap_qExpand, qExpand_qExpand, qExpand_congr (Nat.mul_comm ℓ N)]

theorem coe_heckeAlphaC_jqModC (k : Type*) [Field k] (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] :
    ((heckeAlphaC k N ℓ ⟨jqModC k, jqModC_mem k N⟩ : charLDegeneracyRoof k N ℓ) :
      LaurentSeries k) = jqModC k :=
  coe_heckeAlphaC k N ℓ _

theorem coe_heckeBetaC_jqNModC (k : Type*) [Field k] (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] :
    ((heckeBetaC k N ℓ ⟨jqNModC k N, jqNModC_mem k N⟩ : charLDegeneracyRoof k N ℓ) :
      LaurentSeries k) = jqNModC k (N * ℓ) := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  rw [coe_heckeBetaC]
  show qExpand k ℓ (qExpand k N (jqModC k)) = qExpand k (N * ℓ) (jqModC k)
  rw [qExpand_qExpand, qExpand_congr (Nat.mul_comm ℓ N)]

end LevelN

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem squares_of_laws
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (N * ℓ)
    letI : Algebra (ResidueField A) (charLDegeneracyRoof (ResidueField A) N ℓ) := inferInstance
    ∀ (hαℓ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hβℓ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hαC : (heckeAlphaC (ResidueField A) N ℓ).toRingHom.IsIntegral)
    (hβC : (heckeBetaC (ResidueField A) N ℓ).toRingHom.IsIntegral)
    (hroof' : charLDegeneracyRoof (ResidueField A) N ℓ
      ≤ modularFunctionFieldC (ResidueField A) (N * ℓ))
    (hι' : (IntermediateField.inclusion hroof').toRingHom.IsIntegral)
    (R₁ : RegularProlongation A (modularFunctionFieldBar N)
      (modularFunctionFieldC (ResidueField A) N))
    (r₁ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
      → Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N))
    (hr₁ : ∀ f : R₁.integers, R₁.residue f ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        (∀ V, D V = V.ord (f : modularFunctionFieldBar N)) →
      ∀ Q, Finsupp.mapDomain r₁ D Q = Q.ord (R₁.residue f))
    (hj : ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
        ∈ R₁.integers,
      R₁.residue ⟨_, h⟩
        = ⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩)
    (hjN : ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full N (dvd_refl N))⟩ : modularFunctionFieldBar N)
        ∈ R₁.integers,
      R₁.residue ⟨_, h⟩
        = ⟨jqNModC (ResidueField A) N, jqNModC_mem (ResidueField A) N⟩)
    (R₁ᵣ : RegularProlongation A (modularFunctionFieldBar (N * ℓ))
      (modularFunctionFieldC (ResidueField A) (N * ℓ)))
    (r₁ᵣ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ))
      → Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (N * ℓ)))
    (hr₁ᵣ : ∀ f : R₁ᵣ.integers, R₁ᵣ.residue f ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ)),
        (∀ V, D V = V.ord (f : modularFunctionFieldBar (N * ℓ))) →
      ∀ Q, Finsupp.mapDomain r₁ᵣ D Q = Q.ord (R₁ᵣ.residue f))
    (hjᵣ : ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full (N * ℓ) (jq_mem (N * ℓ)))⟩ :
              modularFunctionFieldBar (N * ℓ))
        ∈ R₁ᵣ.integers,
      R₁ᵣ.residue ⟨_, h⟩
        = ⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) (N * ℓ)⟩)
    (hjNᵣ : ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (N * ℓ) jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full (N * ℓ) (dvd_refl (N * ℓ)))⟩ : modularFunctionFieldBar (N * ℓ))
        ∈ R₁ᵣ.integers,
      R₁ᵣ.residue ⟨_, h⟩
        = ⟨jqNModC (ResidueField A) (N * ℓ), jqNModC_mem (ResidueField A) (N * ℓ)⟩)
    (W₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ))),
    ((r₁ᵣ W₀).restrictAlong (IntermediateField.inclusion hroof') hι').restrictAlong
        (heckeAlphaC (ResidueField A) N ℓ) hαC
      = r₁ (W₀.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hαℓ) ∧
    ((r₁ᵣ W₀).restrictAlong (IntermediateField.inclusion hroof') hι').restrictAlong
        (heckeBetaC (ResidueField A) N ℓ) hβC
      = r₁ (W₀.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβℓ) := by
  intro hαℓ hβℓ hαC hβC hroof' hι' R₁ r₁ hr₁ hj hjN R₁ᵣ r₁ᵣ hr₁ᵣ hjᵣ hjNᵣ W₀

  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (N * ℓ)
  letI : Algebra (ResidueField A) (charLDegeneracyRoof (ResidueField A) N ℓ) := inferInstance

  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  have hqNl : ¬ q ∣ N * ℓ := by
    intro h
    rcases (Nat.Prime.dvd_mul hq).mp h with h1 | h2
    · exact hqN h1
    · exact hℓq (((Nat.prime_dvd_prime_iff_eq hq Fact.out).mp h2).symm)
  have hqℓ : q ≠ ℓ := fun h => hℓq h.symm

  have hroofeq : charLDegeneracyRoof (ResidueField A) N ℓ
      = modularFunctionFieldC (ResidueField A) (N * ℓ) :=
    charLDegeneracyRoof_eq_modularFunctionFieldC_mul (ResidueField A) q N ℓ hqN hqℓ

  haveI : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    isCurveOver_modularFunctionFieldBar N
  haveI : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ)) :=
    isCurveOver_modularFunctionFieldBar (N * ℓ)
  haveI hcurve : IsCurveOver (ResidueField A) (charLDegeneracyRoof (ResidueField A) N ℓ) :=
    isCurveOver_of_eq hroofeq
      (isCurveOver_modularFunctionFieldC_of_perfectField (ResidueField A) (N * ℓ))
  haveI hpd : HasPrincipalDivisors (ResidueField A) (charLDegeneracyRoof (ResidueField A) N ℓ) :=
    hcurve.toHasPrincipalDivisors
  have hdeg1 : ∀ Y : Place (ResidueField A) (charLDegeneracyRoof (ResidueField A) N ℓ),
      Y.deg = 1 := fun Y => IsCurveOver.deg_eq_one_of_isAlgClosed Y

  obtain ⟨Rℓ, rℓ, hrℓ, hRα, hRβ, -, -, hsqα, hsqβ⟩ :=
    @ModularCurve.exists_charLDegeneracyRoof_regularProlongation_heckeCompat_restrictAlong_eq_of_ne
      N q _ hq hqN A hA ℓ _ hℓq hαℓ hβℓ hαC hβC _ _ hpd hdeg1 R₁ r₁ hr₁ hj hjN

  obtain ⟨hj1, hj2⟩ := hj
  obtain ⟨hn1, hn2⟩ := hjN
  have hj2' : R₁.residue ⟨jB N, hj1⟩
      = ⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ := hj2
  have hn2' : R₁.residue ⟨jNB N, hn1⟩
      = ⟨jqNModC (ResidueField A) N, jqNModC_mem (ResidueField A) N⟩ := hn2
  obtain ⟨hmα, hresα⟩ := hRα ⟨jB N, hj1⟩
  obtain ⟨hmβ, hresβ⟩ := hRβ ⟨jNB N, hn1⟩
  have hmℓ : jB (N * ℓ) ∈ Rℓ.integers := heckeAlphaBar_jB N ℓ ▸ hmα
  have hnℓ : jNB (N * ℓ) ∈ Rℓ.integers := heckeBetaBar_jNB N ℓ ▸ hmβ
  have hpinj : (Rℓ.residue ⟨jB (N * ℓ), hmℓ⟩ : LaurentSeries (ResidueField A))
      = jqModC (ResidueField A) := by
    have e : (⟨jB (N * ℓ), hmℓ⟩ : Rℓ.integers)
        = ⟨heckeAlphaBar (AlgebraicClosure ℚ) N ℓ (jB N), hmα⟩ :=
      Subtype.ext (heckeAlphaBar_jB N ℓ).symm
    calc (Rℓ.residue ⟨jB (N * ℓ), hmℓ⟩ : LaurentSeries (ResidueField A))
        = (Rℓ.residue ⟨heckeAlphaBar (AlgebraicClosure ℚ) N ℓ (jB N), hmα⟩ :
            LaurentSeries (ResidueField A)) := by rw [e]
      _ = ((heckeAlphaC (ResidueField A) N ℓ (R₁.residue ⟨jB N, hj1⟩) :
            charLDegeneracyRoof (ResidueField A) N ℓ) : LaurentSeries (ResidueField A)) :=
          congrArg Subtype.val hresα
      _ = ((heckeAlphaC (ResidueField A) N ℓ
            ⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ :
            charLDegeneracyRoof (ResidueField A) N ℓ) : LaurentSeries (ResidueField A)) :=
          congrArg (fun x => ((heckeAlphaC (ResidueField A) N ℓ x :
            charLDegeneracyRoof (ResidueField A) N ℓ) : LaurentSeries (ResidueField A))) hj2'
      _ = jqModC (ResidueField A) := coe_heckeAlphaC_jqModC (ResidueField A) N ℓ
  have hpinjN : (Rℓ.residue ⟨jNB (N * ℓ), hnℓ⟩ : LaurentSeries (ResidueField A))
      = jqNModC (ResidueField A) (N * ℓ) := by
    have e : (⟨jNB (N * ℓ), hnℓ⟩ : Rℓ.integers)
        = ⟨heckeBetaBar (AlgebraicClosure ℚ) N ℓ (jNB N), hmβ⟩ :=
      Subtype.ext (heckeBetaBar_jNB N ℓ).symm
    calc (Rℓ.residue ⟨jNB (N * ℓ), hnℓ⟩ : LaurentSeries (ResidueField A))
        = (Rℓ.residue ⟨heckeBetaBar (AlgebraicClosure ℚ) N ℓ (jNB N), hmβ⟩ :
            LaurentSeries (ResidueField A)) := by rw [e]
      _ = ((heckeBetaC (ResidueField A) N ℓ (R₁.residue ⟨jNB N, hn1⟩) :
            charLDegeneracyRoof (ResidueField A) N ℓ) : LaurentSeries (ResidueField A)) :=
          congrArg Subtype.val hresβ
      _ = ((heckeBetaC (ResidueField A) N ℓ
            ⟨jqNModC (ResidueField A) N, jqNModC_mem (ResidueField A) N⟩ :
            charLDegeneracyRoof (ResidueField A) N ℓ) : LaurentSeries (ResidueField A)) :=
          congrArg (fun x => ((heckeBetaC (ResidueField A) N ℓ x :
            charLDegeneracyRoof (ResidueField A) N ℓ) : LaurentSeries (ResidueField A))) hn2'
      _ = jqNModC (ResidueField A) (N * ℓ) := coe_heckeBetaC_jqNModC (ResidueField A) N ℓ
  obtain ⟨hj1ᵣ, hj2ᵣ⟩ := hjᵣ
  obtain ⟨hn1ᵣ, hn2ᵣ⟩ := hjNᵣ

  obtain ⟨hint, hres⟩ :=
    ModularCurve.regularProlongation_integers_eq_and_coe_residue_eq_of_residue_jq_jqN
      (N * ℓ) q hq hqNl A hA hroofeq rfl Rℓ R₁ᵣ ⟨hmℓ, hpinj⟩ ⟨hnℓ, hpinjN⟩
      ⟨hj1ᵣ, congrArg Subtype.val hj2ᵣ⟩ ⟨hn1ᵣ, congrArg Subtype.val hn2ᵣ⟩

  obtain ⟨⟨hinj, hsurj⟩, hord⟩ := restrictAlong_inclusion_bijective_of_eq hroofeq hroof' hι'
  have hinjι : Function.Injective (IntermediateField.inclusion hroof') :=
    IntermediateField.inclusion_injective hroof'
  have h₂ : ∀ f : Rℓ.integers, Rℓ.residue f ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ)),
        (∀ V, D V = V.ord (f : modularFunctionFieldBar (N * ℓ))) →
      ∀ Q, Finsupp.mapDomain
          (Place.restrictAlong (IntermediateField.inclusion hroof') hι' ∘ r₁ᵣ) D Q
        = Q.ord (Rℓ.residue f) := by
    intro f hf D hD Q
    obtain ⟨Q', rfl⟩ := hsurj Q
    have hf' : (f : modularFunctionFieldBar (N * ℓ)) ∈ R₁ᵣ.integers := hint ▸ f.2
    have hιres : IntermediateField.inclusion hroof' (Rℓ.residue f) = R₁ᵣ.residue ⟨f, hf'⟩ :=
      Subtype.ext (by
        rw [IntermediateField.coe_inclusion]
        exact hres f f.2 hf')
    have hf0 : R₁ᵣ.residue ⟨f, hf'⟩ ≠ 0 := by
      intro h0
      apply hf
      apply hinjι
      rw [hιres, h0, map_zero]
    calc Finsupp.mapDomain (Place.restrictAlong (IntermediateField.inclusion hroof') hι' ∘ r₁ᵣ)
          D (Place.restrictAlong (IntermediateField.inclusion hroof') hι' Q')
        = Finsupp.mapDomain (Place.restrictAlong (IntermediateField.inclusion hroof') hι')
            (Finsupp.mapDomain r₁ᵣ D)
            (Place.restrictAlong (IntermediateField.inclusion hroof') hι' Q') := by
          rw [Finsupp.mapDomain_comp]
      _ = Finsupp.mapDomain r₁ᵣ D Q' := Finsupp.mapDomain_apply hinj _ Q'
      _ = Q'.ord (R₁ᵣ.residue ⟨f, hf'⟩) := hr₁ᵣ ⟨f, hf'⟩ hf0 D hD Q'
      _ = Q'.ord (IntermediateField.inclusion hroof' (Rℓ.residue f)) := by rw [hιres]
      _ = (Place.restrictAlong (IntermediateField.inclusion hroof') hι' Q').ord
            (Rℓ.residue f) := (hord Q' (Rℓ.residue f)).symm

  have hfin : 0 < Module.finrank (IntermediateField.adjoin (ResidueField A)
      ({Rℓ.residue ⟨jB (N * ℓ), hmℓ⟩} :
        Set (charLDegeneracyRoof (ResidueField A) N ℓ)))
      (charLDegeneracyRoof (ResidueField A) N ℓ) :=
    finrank_adjoin_pos_of_eq (ResidueField A) (N * ℓ) q hqNl hroofeq _ hpinj
  have hfinF : 0 < Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({((⟨jB (N * ℓ), hmℓ⟩ : Rℓ.integers) : modularFunctionFieldBar (N * ℓ))} :
        Set (modularFunctionFieldBar (N * ℓ)))) (modularFunctionFieldBar (N * ℓ)) := by
    show 0 < Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({jB (N * ℓ)} : Set (modularFunctionFieldBar (N * ℓ)))) (modularFunctionFieldBar (N * ℓ))
    rw [finrank_adjoin_jB]
    exact dedekindPsi_pos _
  have huniq :=
    @AlgebraicCurve.RegularProlongation.placeMap_unique_of_forall_mapDomain_eq_ord _ _ _ A
      _ _ _ _ _ _ _ hcurve Rℓ ⟨jB (N * ℓ), hmℓ⟩ hfin hfinF rℓ
      (Place.restrictAlong (IntermediateField.inclusion hroof') hι' ∘ r₁ᵣ) hrℓ h₂
  have e : rℓ W₀ = (r₁ᵣ W₀).restrictAlong (IntermediateField.inclusion hroof') hι' :=
    congrFun huniq W₀
  rw [← e]
  exact ⟨hsqα W₀, hsqβ W₀⟩

end SpecSquare

set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R : PlaceSpecialization.ProlongationTuple P), R.IsModel → R.OrderLawFixed →
      ∀ (ℓ : Nat.Primes), (ℓ : ℕ) ≠ q →
        haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
        letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (N * ℓ)
        ∀ (hαᵣ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (N * ℓ) q)
          (hβᵣ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (N * ℓ) q)
          (Pᵣ : PlaceSpecialization A q (N * ℓ) data hKr (ResidueField A) (IsLocalRing.residue A) hαᵣ hβᵣ)
          (Rᵣ : PlaceSpecialization.ProlongationTuple Pᵣ), Rᵣ.IsModel → Rᵣ.OrderLawFixed →
        ∀ (hαℓ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
          (hβℓ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
          (hαC : (heckeAlphaC (ResidueField A) N ℓ).toRingHom.IsIntegral)
          (hβC : (heckeBetaC (ResidueField A) N ℓ).toRingHom.IsIntegral)
          (hroof' : charLDegeneracyRoof (ResidueField A) N ℓ ≤ modularFunctionFieldC (ResidueField A) (N * ℓ))
          (hι' : (IntermediateField.inclusion hroof').toRingHom.IsIntegral)
          (W₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ))),
          ((Pᵣ.sp W₀).restrictAlong (IntermediateField.inclusion hroof') hι').restrictAlong
              (heckeAlphaC (ResidueField A) N ℓ) hαC
            = P.sp (W₀.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hαℓ) ∧
          ((Pᵣ.sp W₀).restrictAlong (IntermediateField.inclusion hroof') hι').restrictAlong
              (heckeBetaC (ResidueField A) N ℓ) hβC
            = P.sp (W₀.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβℓ) := by
  intro data hKr hα hβ P R hmodel hO ℓ hℓq hαᵣ hβᵣ Pᵣ Rᵣ hmodelᵣ hOᵣ hαℓ hβℓ hαC hβC hroof' hι' W₀
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (N * ℓ)
  have hqNl : ¬ q ∣ N * ℓ := by
    intro h
    rcases (Nat.Prime.dvd_mul hq).mp h with h1 | h2
    · exact hqN h1
    · exact hℓq (((Nat.prime_dvd_prime_iff_eq hq ℓ.2).mp h2).symm)

  obtain ⟨R₁, hr₁, hj, hjN⟩ :=
    ModularCurve.PlaceSpecialization.exists_regularProlongation_sp_jq_jqN N q hq hqN A hA
      data hKr hα hβ P R hmodel hO
  obtain ⟨R₁ᵣ, hr₁ᵣ, hjᵣ, hjNᵣ⟩ :=
    ModularCurve.PlaceSpecialization.exists_regularProlongation_sp_jq_jqN (N * ℓ) q hq hqNl A hA
      data hKr hαᵣ hβᵣ Pᵣ Rᵣ hmodelᵣ hOᵣ
  exact SpecSquare.squares_of_laws N q hq hqN A hA ℓ hℓq hαℓ hβℓ hαC hβC hroof' hι'
    R₁ P.sp hr₁ hj hjN R₁ᵣ Pᵣ.sp hr₁ᵣ hjᵣ hjNᵣ W₀

end S_ModularCurve_PlaceSpecialization_restrictAlong_heckeAlphaC_sp_and_restrictAlong_heckeBetaC_sp_eq_sp_restrictAlong_of_isModel
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_restrictAlong_heckeAlphaC_sp_and_restrictAlong_heckeBetaC_sp_eq_sp_restrictAlong_of_isModel (solution)
