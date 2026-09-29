-- Prove2me | solution 1 for ModularCurve.exists_prime_torsion_of_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/716a6305-8c78-5aaa-85fe-bf418a318a03

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Theorems.Thm_ModularCurve_heckeSubalgebraBar_fg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_prime_torsion_of_isMaximal
p2m_attr_erase "instance" "CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree WeierstrassCurve.Affine.Point.instFinite ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply"
p2m_attr_erase "simp" "ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero"
p2m_attr_erase "simp" "ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero"
p2m_attr_erase "simp" "ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"

set_option Elab.async false

open ModularCurve

private noncomputable def d22_psi (N : ℕ) [NeZero N] (h : HeckeOperatorsCommuteBar N) :
    HeckeAlg →ₐ[ℤ] Module.End ℤ (JZero N) :=
  (Algebra.adjoin ℤ (Set.range (heckeOperatorBar N))).val.comp (heckeEvalBarAux h)

section abstract

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A]
  {B : Type*} [Ring B] [Algebra R B]

private theorem d22_range_fg [IsNoetherianRing R] (f : A →ₐ[R] B) (T : Subalgebra R B)
    (hT : (Subalgebra.toSubmodule T).FG) (hfT : ∀ t, f t ∈ T) :
    Module.Finite R ↥f.range := by
  haveI : IsNoetherian R ↥(Subalgebra.toSubmodule T) := isNoetherian_of_fg_of_noetherian _ hT
  have hle : Subalgebra.toSubmodule f.range ≤ Subalgebra.toSubmodule T := by
    intro y hy
    rw [Subalgebra.mem_toSubmodule] at hy ⊢
    obtain ⟨t, rfl⟩ := hy
    exact hfT t
  have hFG : (Subalgebra.toSubmodule f.range).FG := by
    have h1 := IsNoetherian.noetherian
      (Submodule.comap (Subalgebra.toSubmodule T).subtype (Subalgebra.toSubmodule f.range))
    have h2 := Submodule.FG.map (Subalgebra.toSubmodule T).subtype h1
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hle] at h2
  exact Module.Finite.iff_fg.mpr hFG

private theorem d22_fin_transport (f : A →ₐ[R] B) (𝔪 : Ideal A)
    (hle : RingHom.ker f.rangeRestrict ≤ 𝔪) (hfin : Module.Finite R ↥f.range) :
    Module.Finite R (A ⧸ 𝔪) := by
  have e := Ideal.quotientKerAlgEquivOfSurjective f.rangeRestrict_surjective
  haveI : Module.Finite R (A ⧸ RingHom.ker f.rangeRestrict) :=
    Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  have hfac : ∀ a ∈ RingHom.ker f.rangeRestrict, Ideal.Quotient.mkₐ R 𝔪 a = 0 := fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (hle ha)
  have hs : Function.Surjective ⇑(Ideal.Quotient.liftₐ _ (Ideal.Quotient.mkₐ R 𝔪) hfac) := by
    intro z
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨Ideal.Quotient.mk _ t, rfl⟩
  exact Module.Finite.of_surjective
    (Ideal.Quotient.liftₐ _ (Ideal.Quotient.mkₐ R 𝔪) hfac).toLinearMap hs

end abstract

private theorem d22_helper {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (q : ℕ) (𝔪 : Ideal R) (hmax : 𝔪.IsMaximal) (hq : IsUnit ((q : ℕ) : R ⧸ 𝔪))
    (K : Ideal R) (hK0 : ∀ t ∈ K, ∀ y : M, t • y = 0)
    (hfin : K ≤ 𝔪 → Module.Finite ℤ (R ⧸ 𝔪))
    (x : M) (hx : ∀ t ∈ 𝔪, t • x = 0) :
    ∃ p : ℕ, p.Prime ∧ p ≠ q ∧ p • x = 0 := by
  by_cases hle : K ≤ 𝔪
  ·

    letI : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    haveI hMF : Module.Finite ℤ (R ⧸ 𝔪) := hfin hle
    haveI : Algebra.IsIntegral ℤ (R ⧸ 𝔪) := @Algebra.IsIntegral.of_finite ℤ (R ⧸ 𝔪) _ _ _ hMF
    haveI hCharP : CharP (R ⧸ 𝔪) (ringChar (R ⧸ 𝔪)) := ringChar.charP (R ⧸ 𝔪)
    have hp : (ringChar (R ⧸ 𝔪)).Prime := by
      rcases CharP.char_is_prime_or_zero (R ⧸ 𝔪) (ringChar (R ⧸ 𝔪)) with hpr | hp0
      · exact hpr
      · exfalso
        haveI : CharP (R ⧸ 𝔪) 0 := hp0 ▸ hCharP
        haveI : CharZero (R ⧸ 𝔪) := CharP.charP_to_charZero (R ⧸ 𝔪)
        exact Int.not_isField
          ((Algebra.IsIntegral.isField_iff_isField
            (RingHom.injective_int (algebraMap ℤ (R ⧸ 𝔪)))).mpr (Field.toIsField (R ⧸ 𝔪)))
    have hcast : ((ringChar (R ⧸ 𝔪) : ℕ) : R ⧸ 𝔪) = 0 := CharP.cast_eq_zero (R ⧸ 𝔪) _
    have hpq : ringChar (R ⧸ 𝔪) ≠ q := by
      intro hEq
      apply not_isUnit_zero (M₀ := R ⧸ 𝔪)
      rw [← hcast, hEq]
      exact hq
    have hmem : ((ringChar (R ⧸ 𝔪) : ℕ) : R) ∈ 𝔪 := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact hcast
    refine ⟨ringChar (R ⧸ 𝔪), hp, hpq, ?_⟩
    have h1 : ((ringChar (R ⧸ 𝔪) : ℕ) : R) • x = 0 := hx _ hmem
    rwa [Nat.cast_smul_eq_nsmul] at h1
  ·
    obtain ⟨k, hkK, hkm⟩ := SetLike.not_le_iff_exists.mp hle
    obtain ⟨y, i, him, hyi⟩ := hmax.exists_inv hkm
    have hx0 : x = 0 := by
      have h1 : (y * k + i) • x = x := by rw [hyi, one_smul]
      rw [add_smul, mul_smul, hK0 k hkK x, smul_zero, hx i him, add_zero] at h1
      exact h1.symm
    obtain ⟨p, hqp, hp⟩ := Nat.exists_infinite_primes (q + 1)
    refine ⟨p, hp, ?_, by rw [hx0, smul_zero]⟩
    have hlt : q < p := by omega
    exact hlt.ne'

private theorem d22_ker_kills {N : ℕ} [NeZero N] (h : HeckeOperatorsCommuteBar N)
    (t : HeckeAlg) (ht : t ∈ RingHom.ker (d22_psi N h).rangeRestrict)
    (y : JZero N) : (letI := heckeModuleBar N; t • y) = 0 := by
  have h0 : (d22_psi N h).rangeRestrict t = 0 := RingHom.mem_ker.mp ht
  have h2 : heckeEvalBar h t = 0 := congrArg Subtype.val h0
  have h1 := heckeModuleBar_smul_def h t y
  rw [h1, h2]
  exact LinearMap.zero_apply y

private theorem d22_ker_kills_const {N : ℕ} [NeZero N] (h : ¬ HeckeOperatorsCommuteBar N)
    (t : HeckeAlg) (ht : t ∈ RingHom.ker (MvPolynomial.constantCoeff : HeckeAlg →+* ℤ))
    (y : JZero N) : (letI := heckeModuleBar N; t • y) = 0 := by
  have h1 := heckeModuleBar_smul_of_not h t y
  rw [h1, RingHom.mem_ker.mp ht]
  exact zero_smul ℤ y

private theorem d22_fin_of_commute {N : ℕ} [NeZero N] (h : HeckeOperatorsCommuteBar N)
    (𝔪 : Ideal HeckeAlg) (hle : RingHom.ker (d22_psi N h).rangeRestrict ≤ 𝔪) :
    Module.Finite ℤ (HeckeAlg ⧸ 𝔪) :=
  d22_fin_transport (d22_psi N h) 𝔪 hle
    (d22_range_fg (d22_psi N h) (Algebra.adjoin ℤ (Set.range (heckeOperatorBar N)))
      (heckeSubalgebraBar_fg N) (fun t => ((heckeEvalBarAux h) t).2))

private theorem d22_fin_of_const (𝔪 : Ideal HeckeAlg)
    (hle : RingHom.ker (MvPolynomial.constantCoeff : HeckeAlg →+* ℤ) ≤ 𝔪) :
    Module.Finite ℤ (HeckeAlg ⧸ 𝔪) := by
  refine Module.Finite.of_surjective (Algebra.linearMap ℤ (HeckeAlg ⧸ 𝔪)) ?_
  intro z
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨MvPolynomial.constantCoeff t, ?_⟩
  show ((MvPolynomial.constantCoeff t : ℤ) : HeckeAlg ⧸ 𝔪) = Ideal.Quotient.mk 𝔪 t
  rw [← map_intCast (Ideal.Quotient.mk 𝔪) (MvPolynomial.constantCoeff t),
    Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  apply hle
  rw [RingHom.mem_ker, map_sub, map_intCast, Int.cast_id]
  exact sub_self _

theorem solution (M : ℕ) [NeZero M] (q : ℕ) :
    letI := heckeModuleBar M
    ∀ 𝔪 : Ideal HeckeAlg, 𝔪.IsMaximal → IsUnit ((q : ℕ) : HeckeAlg ⧸ 𝔪) →
      ∀ x ∈ heckeTorsion (JZero M) 𝔪, ∃ p : ℕ, p.Prime ∧ p ≠ q ∧ p • x = 0 := by
  letI := heckeModuleBar M
  intro 𝔪 hmax hunit x hx
  have hx' : ∀ t ∈ 𝔪, t • x = 0 := (mem_heckeTorsion_iff (JZero M) 𝔪 x).mp hx
  by_cases h : HeckeOperatorsCommuteBar M
  · exact d22_helper q 𝔪 hmax hunit (RingHom.ker (d22_psi M h).rangeRestrict)
      (fun t ht y => d22_ker_kills h t ht y)
      (fun hle => d22_fin_of_commute h 𝔪 hle) x hx'
  · exact d22_helper q 𝔪 hmax hunit
      (RingHom.ker (MvPolynomial.constantCoeff : HeckeAlg →+* ℤ))
      (fun t ht y => d22_ker_kills_const h t ht y)
      (fun hle => d22_fin_of_const 𝔪 hle) x hx'

end S_ModularCurve_exists_prime_torsion_of_isMaximal
end P2MW
export P2MW.S_ModularCurve_exists_prime_torsion_of_isMaximal (solution)
