-- Prove2me | solution 1 for ModularCurve.eisensteinQuotientRational_closure_fg_heckeModuleBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/0590214e-9539-5fab-88fd-df551950cce1

import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_HeckeModule
import Theorems.Thm_ModularCurve_jZeroTorsionFinite
import Theorems.Thm_ModularCurve_JZero_divisible
import Theorems.Thm_ModularCurve_heckeSubalgebraBar_fg
import Theorems.Thm_ModularCurve_smulCommClass_JZero_of_heckeOperatorsCommuteBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eisensteinQuotientRational_closure_fg_heckeModuleBar
p2m_attr_erase "instance" "CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree WeierstrassCurve.Affine.Point.instFinite ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply"
p2m_attr_erase "simp" "HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"

set_option autoImplicit false

noncomputable section

open ModularCurve AlgebraicCurve Polynomial

private theorem BLOCKED_SEAM (p : ℕ) [NeZero p] :
    (Subalgebra.toSubmodule (Algebra.adjoin ℤ (Set.range (heckeOperatorBar p)))).FG :=
  ModularCurve.heckeSubalgebraBar_fg p

private theorem BLOCKED_DIV (p : ℕ) [NeZero p] :
    ∀ n : ℕ, 0 < n → ∀ x : JZero p, ∃ y : JZero p, n • y = x :=
  fun n hn x => ModularCurve.JZero.divisible p n hn.ne' x

private def annIn {R E : Type*} [CommRing R] [Ring E] [Algebra R E] (T : Submodule R E) (s : E) :
    Submodule R ↥T where
  carrier := {a | s * (a : E) = 0}
  zero_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [Submodule.coe_add, mul_add, ha, hb, add_zero]
  smul_mem' n a ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [Submodule.coe_smul, mul_smul_comm, ha, smul_zero]

private theorem mem_annIn {R E : Type*} [CommRing R] [Ring E] [Algebra R E] (T : Submodule R E)
    (s : E) (a : ↥T) : a ∈ annIn T s ↔ s * (a : E) = 0 :=
  Iff.rfl

private theorem exists_universal_witness {R A E : Type*} [CommRing R] [IsNoetherianRing R]
    [CommRing A] [Ring E] [Algebra R E]
    (ρ : A →+* E) (T : Submodule R E) (hT : T.FG) (hρT : ∀ t, ρ t ∈ T) (I : Ideal A) :
    ∃ i₀ ∈ I, ∀ i ∈ I, ∀ t : A, ρ ((1 + i) * t) = 0 → ρ ((1 + i₀) * t) = 0 := by
  haveI : IsNoetherian R ↥T := isNoetherian_of_fg_of_noetherian T hT
  obtain ⟨M', ⟨i₀, hi₀, rfl⟩, hmax⟩ := set_has_maximal_iff_noetherian.mpr this
    {K | ∃ i ∈ I, K = annIn T (ρ (1 + i))} ⟨_, 0, I.zero_mem, rfl⟩
  refine ⟨i₀, hi₀, fun i hi t ht => ?_⟩
  have hi' : i₀ + i + i₀ * i ∈ I := I.add_mem (I.add_mem hi₀ hi) (I.mul_mem_left _ hi)
  have e1 : (1 + (i₀ + i + i₀ * i)) = (1 + i₀) * (1 + i) := by ring
  have h1 : annIn T (ρ (1 + i₀)) ≤ annIn T (ρ (1 + (i₀ + i + i₀ * i))) := by
    intro a ha
    rw [mem_annIn] at ha ⊢
    rw [e1, mul_comm (1 + i₀), map_mul, mul_assoc, ha, mul_zero]
  have h2 := eq_of_le_of_not_lt h1 (hmax _ ⟨_, hi', rfl⟩)
  have ht' : ρ (1 + i) * ρ t = 0 := by rw [← map_mul]; exact ht
  have h3 : (⟨ρ t, hρT t⟩ : ↥T) ∈ annIn T (ρ (1 + (i₀ + i + i₀ * i))) := by
    rw [mem_annIn]
    change ρ (1 + (i₀ + i + i₀ * i)) * ρ t = 0
    rw [e1, map_mul, mul_assoc, ht', mul_zero]
  rw [← h2, mem_annIn] at h3
  change ρ (1 + i₀) * ρ t = 0 at h3
  rw [map_mul]
  exact h3

private theorem poly_surgery {R : Type*} [CommRing R] (P : R[X]) (hP : P ≠ 0) :
    ∃ (m : ℕ) (q : R[X]), P = X ^ m * q ∧ q.coeff 0 ≠ 0 := by
  obtain ⟨q, hq, hdvd⟩ := P.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hP 0
  refine ⟨P.rootMultiplicity 0, q, by simpa using hq, fun h => hdvd ?_⟩
  rw [map_zero, sub_zero]
  exact X_dvd_iff.mpr h

private theorem middle_abstract {R A E : Type*} [CommRing R] [IsNoetherianRing R] [Nontrivial R]
    [CommRing A] [Algebra R A] [Ring E] [Algebra R E]
    (ρ : A →+* E) (hρc : ∀ c : R, ρ (algebraMap R A c) = algebraMap R E c)
    (S : Subalgebra R E) (hS : (Subalgebra.toSubmodule S).FG) (hρS : ∀ t, ρ t ∈ S)
    (I : Ideal A) :
    ∃ (c : R) (η t₀ : A), c ≠ 0 ∧
      (∃ i₀ ∈ I, ρ ((1 + i₀) * t₀) = 0) ∧
      (∀ i ∈ I, ∀ t : A, ρ ((1 + i) * t) = 0 → ρ (η * t) = 0) ∧
      algebraMap R A c = η + t₀ := by

  obtain ⟨i₀, hi₀, UW⟩ := exists_universal_witness ρ (Subalgebra.toSubmodule S) hS hρS I

  obtain ⟨P, hPm, hP0⟩ := IsIntegral.of_mem_of_fg S hS (ρ (1 + i₀)) (hρS (1 + i₀))

  obtain ⟨m, q, hPq, hq0⟩ := poly_surgery P hPm.ne_zero

  have hcomp : ρ.comp (algebraMap R A) = algebraMap R E := RingHom.ext hρc
  have hev : ∀ g : R[X], ρ (g.eval₂ (algebraMap R A) (1 + i₀)) =
      g.eval₂ (algebraMap R E) (ρ (1 + i₀)) := by
    intro g
    rw [Polynomial.hom_eval₂, hcomp]

  have hpow : ∀ k : ℕ, ∃ j ∈ I, (1 + i₀) ^ k = 1 + j := by
    intro k
    induction k with
    | zero => exact ⟨0, I.zero_mem, by simp⟩
    | succ k ih =>
      obtain ⟨j, hj, hk⟩ := ih
      refine ⟨j + i₀ + j * i₀, I.add_mem (I.add_mem hj hi₀) (I.mul_mem_left _ hi₀), ?_⟩
      rw [pow_succ, hk]
      ring

  have stab : ∀ (k : ℕ) (t : A), ρ ((1 + i₀) ^ k * t) = 0 → ρ ((1 + i₀) * t) = 0 := by
    intro k t ht
    obtain ⟨j, hj, hk⟩ := hpow k
    rw [hk] at ht
    exact UW j hj t ht

  obtain ⟨r, hr⟩ : ∃ r : A, r = q.divX.eval₂ (algebraMap R A) (1 + i₀) := ⟨_, rfl⟩
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : A, t₀ = q.eval₂ (algebraMap R A) (1 + i₀) := ⟨_, rfl⟩
  have hq : t₀ = (1 + i₀) * r + algebraMap R A (q.coeff 0) := by
    rw [ht₀, hr]
    conv_lhs => rw [← X_mul_divX_add q]
    rw [eval₂_add, eval₂_mul, eval₂_X, eval₂_C]

  have hkill : ρ ((1 + i₀) * t₀) = 0 := by
    apply stab m
    have : (1 + i₀) ^ m * t₀ = P.eval₂ (algebraMap R A) (1 + i₀) := by
      rw [hPq, eval₂_mul, eval₂_pow, eval₂_X, ht₀]
    rw [this, hev, hP0]
  obtain ⟨η, hη⟩ : ∃ η : A, η = algebraMap R A (q.coeff 0) - t₀ := ⟨_, rfl⟩
  refine ⟨q.coeff 0, η, t₀, hq0, ⟨i₀, hi₀, hkill⟩, fun i hi t ht => ?_, by rw [hη, sub_add_cancel]⟩
  have h2 : ρ ((1 + i₀) * t) = 0 := UW i hi t ht
  have e3 : η * t = -(r * ((1 + i₀) * t)) := by
    rw [hη, hq]; ring
  rw [e3, map_neg, neg_eq_zero, map_mul]
  exact mul_eq_zero_of_right _ h2

private theorem forall_smul_eq_zero_iff {N : ℕ} [NeZero N] (hcomm : HeckeOperatorsCommuteBar N)
    (t : HeckeAlg) :
    (∀ x : JZero N, (letI := heckeModuleBar N; t • x) = 0) ↔ heckeEvalBar hcomm t = 0 := by
  constructor
  · intro h
    ext x
    rw [LinearMap.zero_apply, ← heckeModuleBar_smul_def hcomm]
    exact h x
  · intro h x
    rw [heckeModuleBar_smul_def hcomm, h, LinearMap.zero_apply]

private theorem kills_kernelSubmodule {N : ℕ} [NeZero N] (hcomm : HeckeOperatorsCommuteBar N)
    (I : Ideal HeckeAlg) (η : HeckeAlg)
    (hη : ∀ i ∈ I, ∀ t : HeckeAlg,
      heckeEvalBar hcomm ((1 + i) * t) = 0 → heckeEvalBar hcomm (η * t) = 0) :
    letI := heckeModuleBar N
    ∀ y ∈ eisensteinKernel (JZero N) I • (⊤ : Submodule HeckeAlg (JZero N)), η • y = 0 := by
  letI := heckeModuleBar N
  intro y hy
  refine Submodule.smul_induction_on hy ?_ ?_
  · intro t ht x _
    obtain ⟨i, hi, hti⟩ := ht
    have h3 : heckeEvalBar hcomm (η * t) = 0 :=
      hη i hi t ((forall_smul_eq_zero_iff hcomm _).mp hti)
    have h4 : (η * t) • x = 0 := (forall_smul_eq_zero_iff hcomm _).mpr h3 x
    calc η • t • x
        = heckeEvalBar hcomm η (t • x) := heckeModuleBar_smul_def hcomm _ _
      _ = heckeEvalBar hcomm η (heckeEvalBar hcomm t x) :=
          congrArg (fun z => heckeEvalBar hcomm η z) (heckeModuleBar_smul_def hcomm t x)
      _ = (heckeEvalBar hcomm η * heckeEvalBar hcomm t) x := (Module.End.mul_apply _ _ _).symm
      _ = heckeEvalBar hcomm (η * t) x :=
          (DFunLike.congr_fun (map_mul (heckeEvalBar hcomm) _ _) x).symm
      _ = (η * t) • x := (heckeModuleBar_smul_def hcomm _ _).symm
      _ = 0 := h4
  · intro a b ha hb
    rw [heckeModuleBar_smul_def hcomm] at ha hb ⊢
    rw [(heckeEvalBar hcomm η).map_add a b, ha, hb, add_zero]

private theorem middle_triple (p : ℕ) [Fact p.Prime] (hcomm : HeckeOperatorsCommuteBar p)
    (hSEAM : (Subalgebra.toSubmodule (Algebra.adjoin ℤ (Set.range (heckeOperatorBar p)))).FG) :
    letI := heckeModuleBar p
    ∃ (n : ℕ) (η t₀ : HeckeAlg), 0 < n ∧
      t₀ ∈ eisensteinKernel (JZero p) (eisensteinIdeal p) ∧
      (∀ y ∈ eisensteinKernelSubmodule p (heckeModuleBar p), η • y = 0) ∧
      MvPolynomial.C (n : ℤ) = η + t₀ := by
  letI := heckeModuleBar p
  have hρS : ∀ t, heckeEvalBar hcomm t ∈ Algebra.adjoin ℤ (Set.range (heckeOperatorBar p)) :=
    fun t => (heckeEvalBarAux hcomm t).2
  have hρc : ∀ c : ℤ, heckeEvalBar hcomm (algebraMap ℤ HeckeAlg c) =
      algebraMap ℤ (Module.End ℤ (JZero p)) c := by
    intro c
    rw [(algebraMap ℤ HeckeAlg).eq_intCast', (algebraMap ℤ (Module.End ℤ (JZero p))).eq_intCast',
      eq_intCast (Int.castRingHom HeckeAlg), eq_intCast (Int.castRingHom (Module.End ℤ (JZero p)))]
    exact map_intCast (heckeEvalBar hcomm) c
  obtain ⟨c, η, t₀, hc0, ⟨i₀, hi₀, hkill⟩, hK1, hK2⟩ :=
    middle_abstract (heckeEvalBar hcomm) hρc _ hSEAM hρS (eisensteinIdeal p)
  rw [(algebraMap ℤ HeckeAlg).eq_intCast', eq_intCast (Int.castRingHom HeckeAlg),
    ← eq_intCast (MvPolynomial.C : ℤ →+* HeckeAlg)] at hK2
  have K0 : t₀ ∈ eisensteinKernel (JZero p) (eisensteinIdeal p) :=
    ⟨i₀, hi₀, (forall_smul_eq_zero_iff hcomm _).mpr hkill⟩
  have K1 : ∀ y ∈ eisensteinKernelSubmodule p (heckeModuleBar p), η • y = 0 :=
    kills_kernelSubmodule hcomm (eisensteinIdeal p) η hK1
  rcases Int.natAbs_eq c with hc | hc
  · refine ⟨c.natAbs, η, t₀, Int.natAbs_pos.mpr hc0, K0, K1, ?_⟩
    rw [← hc]
    exact hK2
  · have hc' : -c = (c.natAbs : ℤ) := neg_eq_iff_eq_neg.mpr hc
    have hK1' : ∀ i ∈ eisensteinIdeal p, ∀ t : HeckeAlg,
        heckeEvalBar hcomm ((1 + i) * t) = 0 → heckeEvalBar hcomm ((-η) * t) = 0 := by
      intro i hi t ht
      rw [neg_mul, map_neg, hK1 i hi t ht, neg_zero]
    refine ⟨c.natAbs, -η, -t₀, Int.natAbs_pos.mpr hc0, Submodule.neg_mem _ K0,
      kills_kernelSubmodule hcomm (eisensteinIdeal p) (-η) hK1', ?_⟩
    rw [← hc', map_neg, hK2, neg_add]

namespace N1FG

local notation "G" => AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

variable (p : ℕ) [Fact p.Prime]

private scoped instance : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

local notation "γSM" => eisensteinKernelSubmodule p (heckeModuleBar p)
local notation "EisQuot" => EisensteinQuotient p (heckeModuleBar p)
local notation "FixedPts" => FixedPoints.addSubgroup G (JZero p)
local notation "mkQ" => eisensteinQuotientMk p (heckeModuleBar p)

private def preimageSubgroup : AddSubgroup (JZero p) where
  carrier := {x : JZero p | ∀ σ : G, σ • x - x ∈ γSM}
  zero_mem' := fun σ => by simp
  add_mem' := by
    intro a b ha hb σ
    have : σ • (a + b) - (a + b) = (σ • a - a) + (σ • b - b) := by
      rw [smul_add]; abel
    rw [this]
    exact (γSM).add_mem (ha σ) (hb σ)
  neg_mem' := by
    intro a ha σ
    have : σ • (-a) - (-a) = -(σ • a - a) := by rw [smul_neg]; abel
    rw [this]
    exact (γSM).neg_mem (ha σ)

private theorem mem_preimageSubgroup (x : JZero p) :
    x ∈ preimageSubgroup p ↔ ∀ σ : G, σ • x - x ∈ γSM := Iff.rfl

private theorem closure_eq_map :
    AddSubgroup.closure (eisensteinQuotientRational p (heckeModuleBar p))
      = (preimageSubgroup p).map mkQ := by
  rw [show eisensteinQuotientRational p (heckeModuleBar p)
        = mkQ '' (preimageSubgroup p : Set (JZero p)) from rfl,
      ← AddSubgroup.coe_map, AddSubgroup.closure_eq]

section Endgame

private theorem kernelSubmodule_div
    (hDIV : ∀ n : ℕ, 0 < n → ∀ x : JZero p, ∃ y : JZero p, n • y = x)
    (n : ℕ) (hn : 0 < n) :
    ∀ y ∈ γSM, ∃ z ∈ γSM, n • z = y := by
  letI := heckeModuleBar p
  intro y hy
  refine Submodule.smul_induction_on hy ?_ ?_
  · intro t ht w _
    obtain ⟨v, hv⟩ := hDIV n hn w
    refine ⟨t • v, Submodule.smul_mem_smul ht trivial, ?_⟩
    rw [smul_comm n t v, hv]
  · rintro a b ⟨za, hza, rfl⟩ ⟨zb, hzb, rfl⟩
    exact ⟨za + zb, add_mem hza hzb, nsmul_add za zb n⟩

private theorem quot_torsion_sub_image
    (hDIV : ∀ n : ℕ, 0 < n → ∀ x : JZero p, ∃ y : JZero p, n • y = x)
    (n : ℕ) (hn : 0 < n) (y : EisQuot) (hy : n • y = 0) :
    ∃ x : JZero p, (n : ℤ) • x = 0 ∧ mkQ x = y := by
  letI := heckeModuleBar p
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hNx : n • x ∈ γSM := by
    have := (Submodule.Quotient.mk_eq_zero _).mp (by exact_mod_cast hy : Submodule.Quotient.mk (n • x) = 0)
    exact this
  obtain ⟨z, hz, hNz⟩ := kernelSubmodule_div p hDIV n hn (n • x) hNx
  refine ⟨x - z, ?_, ?_⟩
  · have h1 : (n : ℤ) • z = (n : ℤ) • x := by rw [natCast_zsmul, natCast_zsmul, hNz]
    have h2 : (n : ℤ) • (x - z) = (n : ℤ) • x - (n : ℤ) • z := smul_sub (n : ℤ) x z
    rw [h2, h1, sub_self]
  · show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [Submodule.Quotient.eq]
    simpa using hz

private theorem finite_quot_torsion
    (hDIV : ∀ n : ℕ, 0 < n → ∀ x : JZero p, ∃ y : JZero p, n • y = x)
    (n : ℕ) (hn : 0 < n) :
    {y : EisQuot | n • y = 0}.Finite := by
  have hfin : Finite (Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar p) n) :=
    ModularCurve.jZeroTorsionFinite p n hn
  have hsub : {y : EisQuot | n • y = 0}
      ⊆ mkQ '' (Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar p) n : Set (JZero p)) := by
    intro y hy
    obtain ⟨x, hx0, hxq⟩ := quot_torsion_sub_image p hDIV n hn y hy
    exact ⟨x, Pic0.mem_torsion.mpr hx0, hxq⟩
  exact ((Set.finite_coe_iff.mp hfin).image _).subset hsub

private theorem eta_smul_mem_fixedPts (hcomm : HeckeOperatorsCommuteBar p) (η : HeckeAlg)
    (hη : letI := heckeModuleBar p; ∀ y ∈ γSM, η • y = 0)
    (x : JZero p) (hx : x ∈ preimageSubgroup p) :
    (letI := heckeModuleBar p; η • x) ∈ FixedPts := by
  letI := heckeModuleBar p
  haveI := ModularCurve.smulCommClass_JZero_of_heckeOperatorsCommuteBar p hcomm
  intro σ
  rw [smul_comm σ η x, ← sub_eq_zero, ← smul_sub]
  exact hη _ (hx σ)

private theorem endgame (hcomm : HeckeOperatorsCommuteBar p)
    (hMW : AddGroup.FG ↥(FixedPoints.addSubgroup G (JZero p)))
    (hDIV : ∀ n : ℕ, 0 < n → ∀ x : JZero p, ∃ y : JZero p, n • y = x)
    (n : ℕ) (hn : 0 < n) (η t₀ : HeckeAlg)
    (ht₀ : letI := heckeModuleBar p; t₀ ∈ eisensteinKernel (JZero p) (eisensteinIdeal p))
    (hη : letI := heckeModuleBar p; ∀ y ∈ eisensteinKernelSubmodule p (heckeModuleBar p), η • y = 0)
    (hsum : MvPolynomial.C (n : ℤ) = η + t₀) :
    letI := heckeModuleBar p
    AddGroup.FG ↥(AddSubgroup.closure (eisensteinQuotientRational p (heckeModuleBar p))) := by
  letI := heckeModuleBar p
  rw [closure_eq_map p]

  let ηmap : JZero p →+ JZero p := (DistribSMul.toAddMonoidHom (JZero p) η)
  have hker : ∀ y ∈ (γSM).toAddSubgroup, ηmap y = 0 := fun y hy => hη y hy

  let ηbar : EisQuot →+ JZero p := QuotientAddGroup.lift _ ηmap hker

  let M := (preimageSubgroup p).map mkQ
  have himg : ∀ z ∈ M, ηbar z ∈ FixedPts := by
    rintro z ⟨x, hx, rfl⟩
    exact eta_smul_mem_fixedPts p hcomm η hη x hx
  let φ : ↥M →ₗ[ℤ] ↥FixedPts :=
    (((ηbar.comp M.subtype).codRestrict FixedPts (fun z => himg z z.2))).toIntLinearMap

  rw [← Module.Finite.iff_addGroup_fg]
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker φ ?_ ?_⟩
  ·
    haveI : Module.Finite ℤ ↥FixedPts := Module.Finite.iff_addGroup_fg.mpr hMW
    exact IsNoetherian.noetherian _
  ·
    rw [top_inf_eq]
    have hkerN : ∀ z : ↥M, φ z = 0 → n • (z : EisQuot) = 0 := by
      rintro ⟨z, x, hx, rfl⟩ hφz
      have hηx0 : η • x = 0 := Subtype.ext_iff.mp hφz
      have hnx : n • x = t₀ • x := by
        have hC : (MvPolynomial.C (n : ℤ) : HeckeAlg) • x = (n : ℤ) • x :=
          heckeModuleBar_C_smul (n : ℤ) x
        rw [hsum, add_smul, hηx0, zero_add] at hC
        rw [← natCast_zsmul, ← hC]
      have ht₀x : t₀ • x ∈ γSM := Submodule.smul_mem_smul ht₀ trivial
      show n • (Submodule.Quotient.mk x) = 0
      have hmk : (n • Submodule.Quotient.mk x : EisQuot) = Submodule.Quotient.mk (n • x) :=
        (map_nsmul ((γSM).mkQ) n x).symm
      rw [hmk, (Submodule.Quotient.mk_eq_zero _)]
      exact hnx ▸ ht₀x
    have hfin : (LinearMap.ker φ : Set ↥M).Finite := by
      have hfinN := finite_quot_torsion p hDIV n hn
      refine (hfinN.preimage (Subtype.val_injective.injOn)).subset ?_
      rintro z hz
      exact hkerN z hz
    haveI : Finite ↥(LinearMap.ker φ) := hfin
    exact Submodule.FG.of_finite

end Endgame

end N1FG
p2m_reactivate "P2MW.S_ModularCurve_eisensteinQuotientRational_closure_fg_heckeModuleBar.N1FG"

theorem solution (p : ℕ) [Fact p.Prime]
    (hcomm : HeckeOperatorsCommuteBar p)
    (hMW : AddGroup.FG ↥(FixedPoints.addSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (JZero p))) :
    letI := heckeModuleBar p
    AddGroup.FG ↥(AddSubgroup.closure (eisensteinQuotientRational p (heckeModuleBar p))) := by
  obtain ⟨n, η, t₀, hn, ht₀, hη, hsum⟩ := middle_triple p hcomm (BLOCKED_SEAM p)
  exact N1FG.endgame p hcomm hMW (BLOCKED_DIV p) n hn η t₀ ht₀ hη hsum

end
p2m_reactivate "P2MW.S_ModularCurve_eisensteinQuotientRational_closure_fg_heckeModuleBar.N1FG"

end S_ModularCurve_eisensteinQuotientRational_closure_fg_heckeModuleBar
end P2MW
export P2MW.S_ModularCurve_eisensteinQuotientRational_closure_fg_heckeModuleBar (solution)
