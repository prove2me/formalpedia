-- Prove2me | solution 1 for ModularCurve.freeAlgebra_lift_heckeOperatorBar_eq_zero_of_lift_heckeDiffBar_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/5765d173-1eff-58d0-af91-fef4c2199b61

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_ModularCurve_PeriodLattice
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Differential_correspondence_mem_regularDifferentials
import Theorems.Thm_ModularCurve_exists_linearEquiv_tensor_regularDifferentialsBar_cuspForm
import Theorems.Thm_ModularCurve_coeff_diffQExpBar_heckeDiffBar_of_not_dvd
import Theorems.Thm_ModularCurve_coeff_diffQExpBar_heckeDiffBar_of_dvd
import Theorems.Thm_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jZero_quotient_periodLattice
import Theorems.Thm_ModularCurve_periodLatticeHeckeStable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_freeAlgebra_lift_heckeOperatorBar_eq_zero_of_lift_heckeDiffBar_eq_zero
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion"
p2m_attr_erase "instance" "instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.cuspCount_one ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one"
p2m_attr_erase "simp" "ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄"
p2m_attr_erase "simp" "compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe"
p2m_attr_erase "simp" "ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped TensorProduct

namespace W7XI

section Conj

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable {E : Type*} [Field E] [Algebra K E]
variable {W : Type*} [AddCommGroup W] [Module E W]

noncomputable def conjBaseChange (e : E ⊗[K] V ≃ₗ[E] W) : Module.End K V →+* Module.End E W where
  toFun f := e.toLinearMap ∘ₗ f.baseChange E ∘ₗ e.symm.toLinearMap
  map_one' := by
    rw [LinearMap.baseChange_one]
    ext w
    simp
  map_mul' f g := by
    rw [LinearMap.baseChange_mul]
    ext w
    simp
  map_zero' := by
    rw [LinearMap.baseChange_zero]
    ext w
    simp
  map_add' f g := by
    rw [LinearMap.baseChange_add]
    ext w
    simp

theorem conjBaseChange_apply (e : E ⊗[K] V ≃ₗ[E] W) (f : Module.End K V) (w : W) :
    conjBaseChange e f w = e (f.baseChange E (e.symm w)) := rfl

theorem conjBaseChange_eq_of_tmul (e : E ⊗[K] V ≃ₗ[E] W) (f : Module.End K V) (T : Module.End E W)
    (h : ∀ v : V, e ((1 : E) ⊗ₜ[K] f v) = T (e ((1 : E) ⊗ₜ[K] v))) :
    conjBaseChange e f = T := by
  have key : e.toLinearMap ∘ₗ f.baseChange E = T ∘ₗ e.toLinearMap := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c v =>
        have hc : c ⊗ₜ[K] v = c • ((1 : E) ⊗ₜ[K] v) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
        rw [hc, map_smul, map_smul, map_smul, LinearMap.baseChange_tmul, h v, map_smul]
    | add x y hx hy =>
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, map_add] at hx hy ⊢
        rw [hx, hy]
  ext w
  have := LinearMap.congr_fun key (e.symm w)
  simpa [conjBaseChange_apply] using this

end Conj

end W7XI

open ModularForm Complex
p2m_open "UpperHalfPlane~I"

namespace W7XI
namespace QExp

local notation "𝕢" => Function.Periodic.qParam

lemma sum_range_rootOfUnity_pow {p : ℕ} (hp : p ≠ 0) (m : ℕ) :
    ∑ j ∈ Finset.range p, (cexp (2 * Real.pi * I / p) ^ m) ^ j
      = if p ∣ m then (p : ℂ) else 0 := by
  have hζ : IsPrimitiveRoot (cexp (2 * Real.pi * I / p)) p := Complex.isPrimitiveRoot_exp p hp
  split_ifs with hdvd
  · have h1 : cexp (2 * Real.pi * I / p) ^ m = 1 := (hζ.pow_eq_one_iff_dvd m).mpr hdvd
    simp [h1]
  · have h1 : cexp (2 * Real.pi * I / p) ^ m ≠ 1 := fun h => hdvd ((hζ.pow_eq_one_iff_dvd m).mp h)
    rw [geom_sum_eq h1, pow_right_comm, hζ.pow_eq_one, one_pow, sub_self, zero_div]

lemma qParam_heckeMatrix_pow {p : ℕ} (hp : p ≠ 0) (j : ℕ) (τ : ℍ) (m : ℕ) :
    𝕢 1 ((heckeMatrix p j • τ : ℍ) : ℂ) ^ m
      = cexp (2 * Real.pi * I * τ * m / p) * (cexp (2 * Real.pi * I / p) ^ m) ^ j := by
  rw [coe_heckeMatrix_smul hp j τ]
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one]
  rw [← Complex.exp_nat_mul, ← pow_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma qParam_one_pow (τ : ℍ) (n : ℕ) :
    𝕢 1 (τ : ℂ) ^ n = cexp (2 * Real.pi * I * τ * n) := by
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one]
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

theorem hasSum_heckeU {a : ℕ → ℂ} {F : ℍ → ℂ}
    (hF : ∀ τ : ℍ, HasSum (fun m ↦ a m * 𝕢 1 τ ^ m) (F τ)) (k : ℤ) {p : ℕ} (hp : p ≠ 0)
    (τ : ℍ) :
    HasSum (fun n ↦ a (n * p) * 𝕢 1 τ ^ n) (heckeU k p F τ) := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  set ζ : ℂ := cexp (2 * Real.pi * I / p) with hζdef
  set X : ℕ → ℂ := fun m ↦ cexp (2 * Real.pi * I * τ * m / p) with hXdef
  have h1 : ∀ j ∈ Finset.range p,
      HasSum (fun m ↦ a m * (X m * (ζ ^ m) ^ j)) (F (heckeMatrix p j • τ)) := by
    intro j _
    have := hF (heckeMatrix p j • τ)
    simpa only [qParam_heckeMatrix_pow hp j τ] using this
  have h2 : HasSum (fun m ↦ ∑ j ∈ Finset.range p, a m * (X m * (ζ ^ m) ^ j))
      (∑ j ∈ Finset.range p, F (heckeMatrix p j • τ)) := hasSum_sum h1
  have h3 : (fun m ↦ ∑ j ∈ Finset.range p, a m * (X m * (ζ ^ m) ^ j))
      = fun m ↦ a m * X m * (if p ∣ m then (p : ℂ) else 0) := by
    funext m
    rw [← sum_range_rootOfUnity_pow hp m, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h3] at h2
  have h4 := h2.mul_left ((p : ℂ)⁻¹)
  rw [← heckeU_apply k hp F τ] at h4
  have hinj : Function.Injective (fun n : ℕ ↦ n * p) := mul_left_injective₀ hp
  have hvan : ∀ m ∉ Set.range (fun n : ℕ ↦ n * p),
      (fun m ↦ (p : ℂ)⁻¹ * (a m * X m * (if p ∣ m then (p : ℂ) else 0))) m = 0 := by
    intro m hm
    have hndvd : ¬ p ∣ m := by
      rintro ⟨c, rfl⟩
      exact hm ⟨c, by simp [mul_comm]⟩
    simp [hndvd]
  have h5 := (hinj.hasSum_iff hvan).mpr h4
  convert h5 using 1
  funext n
  simp only [Function.comp_apply, Dvd.intro_left n rfl, if_true, hXdef]
  rw [qParam_one_pow, Nat.cast_mul, mul_div_assoc, mul_div_cancel_right₀ _ hp']
  field_simp

theorem hasSum_heckeDiag {a : ℕ → ℂ} {F : ℍ → ℂ}
    (hF : ∀ τ : ℍ, HasSum (fun m ↦ a m * 𝕢 1 τ ^ m) (F τ)) {p : ℕ} (hp : p ≠ 0) (τ : ℍ) :
    HasSum (fun n ↦ (if p ∣ n then a (n / p) else 0) * 𝕢 1 τ ^ n) (F (heckeDiagMatrix p • τ)) := by
  have hinj : Function.Injective (fun n : ℕ ↦ n * p) := mul_left_injective₀ hp
  have hvan : ∀ m ∉ Set.range (fun n : ℕ ↦ n * p),
      (fun n ↦ (if p ∣ n then a (n / p) else 0) * 𝕢 1 τ ^ n) m = 0 := by
    intro m hm
    have hndvd : ¬ p ∣ m := by
      rintro ⟨c, rfl⟩
      exact hm ⟨c, by simp [mul_comm]⟩
    simp [hndvd]
  refine (hinj.hasSum_iff hvan).mp ?_
  convert hF (heckeDiagMatrix p • τ) using 1
  funext m
  simp only [Function.comp_apply, Dvd.intro_left m rfl, if_true, Nat.mul_div_cancel _
    (Nat.pos_of_ne_zero hp)]
  congr 1
  rw [coe_heckeDiagMatrix_smul hp τ, qParam_one_pow]
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem hasSum_heckeT {a : ℕ → ℂ} {F : ℍ → ℂ}
    (hF : ∀ τ : ℍ, HasSum (fun m ↦ a m * 𝕢 1 τ ^ m) (F τ)) (k : ℤ) {p : ℕ} (hp : p ≠ 0)
    (τ : ℍ) :
    HasSum (fun n ↦ coeffHeckeT k p a n * 𝕢 1 τ ^ n) (heckeT k p F τ) := by
  have hU := hasSum_heckeU hF k hp τ
  have hD := (hasSum_heckeDiag hF hp τ).mul_left ((p : ℂ) ^ (k - 1))
  rw [heckeT, Pi.add_apply, slash_heckeDiagMatrix_apply k hp]
  convert hU.add hD using 1
  funext n
  rw [coeffHeckeT_apply]
  split_ifs <;> ring

lemma hasSum_qCoeff {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : ℍ) :
    HasSum (fun m ↦ ModularFormClass.qCoeff f m * 𝕢 1 τ ^ m) (f τ) := by
  have h1 : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp
  haveI : Fact (IsCusp OnePoint.infty (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos h1⟩
  have := hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f h1)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) τ
  first | (simpa only [smul_eq_mul] using this) | (have h__ := this; simp only [smul_eq_mul] at h__; exact h__) | (exact this)

theorem eq_of_qCoeff_eq {N : ℕ} {k : ℤ} (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k)
    (h : ∀ n, ModularFormClass.qCoeff f n = ModularFormClass.qCoeff g n) : f = g := by
  refine DFunLike.ext _ _ fun τ => ?_
  have hf := hasSum_qCoeff f τ
  have hg := hasSum_qCoeff g τ
  simp_rw [h] at hf
  exact hf.unique hg

theorem qCoeff_heckeTLin {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k)
    {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (n : ℕ) :
    ModularFormClass.qCoeff (CuspForm.heckeTLin k hp hpN f) n =
      coeffHeckeT k p (fun m ↦ ModularFormClass.qCoeff f m) n := by
  have h1 : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp
  haveI : Fact (IsCusp OnePoint.infty (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos h1⟩
  have hT : ∀ τ : ℍ, HasSum (fun n ↦ coeffHeckeT k p (fun m ↦ ModularFormClass.qCoeff f m) n • 𝕢 1 τ ^ n)
      ((CuspForm.heckeTLin k hp hpN f) τ) := fun τ => by
    simpa only [smul_eq_mul, CuspForm.heckeTLin_apply_apply] using
      hasSum_heckeT (hasSum_qCoeff f) k hp.ne_zero τ
  have han : AnalyticAt ℂ (cuspFunction 1 (CuspForm.heckeTLin k hp hpN f)) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero (CuspForm.heckeTLin k hp hpN f) one_pos h1
  exact (qExpansion_coeff_unique _ one_pos han hT n).symm

theorem qCoeff_heckeULin {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k)
    {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (n : ℕ) :
    ModularFormClass.qCoeff (CuspForm.heckeULin k hpN f) n = ModularFormClass.qCoeff f (n * p) := by
  have h1 : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp
  haveI : Fact (IsCusp OnePoint.infty (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos h1⟩
  have hT : ∀ τ : ℍ, HasSum (fun n ↦ ModularFormClass.qCoeff f (n * p) • 𝕢 1 τ ^ n)
      ((CuspForm.heckeULin k hpN f) τ) := fun τ => by
    simpa only [smul_eq_mul, CuspForm.heckeULin_apply_apply] using
      hasSum_heckeU (hasSum_qCoeff f) k hp.ne_zero τ
  have han : AnalyticAt ℂ (cuspFunction 1 (CuspForm.heckeULin k hpN f)) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero (CuspForm.heckeULin k hpN f) one_pos h1
  exact (qExpansion_coeff_unique _ one_pos han hT n).symm

end W7XI.QExp

namespace W7XI

p2m_open "ModularCurve~IsCusp AlgebraicCurve"
open scoped TensorProduct

section Assembly

variable {N : ℕ} [NeZero N]

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem neZero_prime (ℓ : Nat.Primes) : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩

theorem hα (hin : HeckeInputsAll N) (ℓ : Nat.Primes) :
    haveI := neZero_prime ℓ; HeckeAlphaBarIntegral ℚ̄ N ℓ := (hin ℓ).fst
theorem hβ (hin : HeckeInputsAll N) (ℓ : Nat.Primes) :
    haveI := neZero_prime ℓ; HeckeBetaBarIntegral ℚ̄ N ℓ := (hin ℓ).snd.fst
theorem hP (hin : HeckeInputsAll N) (ℓ : Nat.Primes) :
    HasPrincipalDivisors ℚ̄ (modularFunctionFieldBar (N * ℓ)) := (hin ℓ).snd.snd.fst
theorem hfin (hin : HeckeInputsAll N) (ℓ : Nat.Primes) :
    haveI := neZero_prime ℓ; FiniteAlong ℚ̄ (heckeAlphaBar ℚ̄ N ℓ) := (hin ℓ).snd.snd.snd.fst
theorem hFI (hin : HeckeInputsAll N) (ℓ : Nat.Primes) :
    haveI := neZero_prime ℓ; haveI := hP hin ℓ
    FundamentalIdentityAlong ℚ̄ (heckeBetaBar ℚ̄ N ℓ) (hβ hin ℓ) := (hin ℓ).snd.snd.snd.snd.1
theorem hNF (hin : HeckeInputsAll N) (ℓ : Nat.Primes) :
    haveI := neZero_prime ℓ
    NormFormulaAlong ℚ̄ (heckeAlphaBar ℚ̄ N ℓ) (hfin hin ℓ) := (hin ℓ).snd.snd.snd.snd.2

abbrev Fup (N : ℕ) (ℓ : Nat.Primes) : Type := ↥(modularFunctionFieldBar (N * ℓ))

abbrev legβ (N : ℕ) [NeZero N] (ℓ : Nat.Primes) : modularFunctionFieldBar N →ₐ[ℚ̄] Fup N ℓ :=
  haveI := neZero_prime ℓ; heckeBetaBar ℚ̄ N ℓ

abbrev legα (N : ℕ) [NeZero N] (ℓ : Nat.Primes) : modularFunctionFieldBar N →ₐ[ℚ̄] Fup N ℓ :=
  haveI := neZero_prime ℓ; heckeAlphaBar ℚ̄ N ℓ

theorem heckeOperatorBar_eq_correspondence (hin : HeckeInputsAll N) :
    heckeOperatorBar N = fun ℓ =>
      (haveI := hP hin ℓ
       (Pic0.correspondence (legβ N ℓ) (legα N ℓ) (hβ hin ℓ) (hα hin ℓ) (hFI hin ℓ) (hfin hin ℓ)
          (hNF hin ℓ)).toIntLinearMap) := by
  funext ℓ
  haveI := neZero_prime ℓ
  haveI := hP hin ℓ
  show (heckeOperatorAlong ℚ̄ N ℓ).toIntLinearMap = _
  rw [heckeOperatorAlong_eq (hα hin ℓ) (hβ hin ℓ) (hFI hin ℓ) (hfin hin ℓ) (hNF hin ℓ)]
  rfl

theorem heckeDiffBar_eq_correspondence :
    heckeDiffBar N = fun ℓ => Differential.correspondence (legβ N ℓ) (legα N ℓ) := rfl

theorem heckeDiffBar_mem (hin : HeckeInputsAll N) (ℓ : Nat.Primes) :
    ∀ ω ∈ regularDifferentialsBar N, heckeDiffBar N ℓ ω ∈ regularDifferentialsBar N := by
  intro ω hω
  haveI := neZero_prime ℓ
  haveI : IsCurveOver ℚ̄ (modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N
  haveI : IsCurveOver ℚ̄ (Fup N ℓ) := isCurveOver_modularFunctionFieldBar (N * ℓ)
  exact AlgebraicCurve.Differential.correspondence_mem_regularDifferentials ℚ̄
    (modularFunctionFieldBar N) (Fup N ℓ)
    (exists_transcendental_finiteDimensional_modularFunctionFieldBar N)
    (legβ N ℓ) (legα N ℓ) (hβ hin ℓ) (hα hin ℓ) (hfin hin ℓ) hω

def cRes (hin : HeckeInputsAll N) (ℓ : Nat.Primes) : (Module.End ℚ̄ ↥(regularDifferentialsBar N))ᵐᵒᵖ :=
  MulOpposite.op ((heckeDiffBar N ℓ).restrict (heckeDiffBar_mem hin ℓ))

theorem restrict_lift (hin : HeckeInputsAll N) (p : FreeAlgebra ℤ Nat.Primes) (v : ↥(regularDifferentialsBar N)) :
    ((MulOpposite.unop (FreeAlgebra.lift ℤ (cRes hin) p) v : ↥(regularDifferentialsBar N)) :
        Ω[modularFunctionFieldBar N⁄ℚ̄]) =
      MulOpposite.unop (FreeAlgebra.lift ℤ (fun ℓ => MulOpposite.op (heckeDiffBar N ℓ)) p)
        (v : Ω[modularFunctionFieldBar N⁄ℚ̄]) := by
  induction p using FreeAlgebra.induction generalizing v with
  | grade0 r =>
      rw [AlgHom.commutes, AlgHom.commutes, MulOpposite.algebraMap_apply, MulOpposite.unop_op,
        MulOpposite.algebraMap_apply, MulOpposite.unop_op, eq_intCast, eq_intCast,
        Module.End.intCast_apply, Module.End.intCast_apply, Submodule.coe_smul_of_tower]
  | grade1 ℓ =>
      simp only [FreeAlgebra.lift_ι_apply, cRes, MulOpposite.unop_op, LinearMap.coe_restrict_apply]
  | mul a b ha hb =>
      simp only [map_mul, MulOpposite.unop_mul, Module.End.mul_apply, ha, hb]
  | add a b ha hb =>
      simp only [map_add, MulOpposite.unop_add, LinearMap.add_apply, Submodule.coe_add, ha, hb]

def emb : ℚ̄ →+* ℂ :=
  haveI : Algebra.IsAlgebraic ℚ ℚ̄ := by
    convert AlgebraicClosure.isAlgebraic ℚ <;> first | rfl | exact Subsingleton.elim _ _
  (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := ℚ̄)).toRingHom

theorem tmul_value (hin : HeckeInputsAll N) (ℓ : Nat.Primes) (hℓN : ¬ (ℓ : ℕ) ∣ N)
    (e : letI := (emb).toAlgebra
      ℂ ⊗[ℚ̄] ↥(regularDifferentialsBar N) ≃ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (he : letI := (emb).toAlgebra
      ∀ (ω : ↥(regularDifferentialsBar N)) (n : ℕ),
        ModularFormClass.qCoeff (e (1 ⊗ₜ ω)) n =
          emb ((diffQExpBar N (ω : Ω[modularFunctionFieldBar N⁄ℚ̄])).coeff n))
    (v : ↥(regularDifferentialsBar N)) :
    letI := (emb).toAlgebra
    e ((1 : ℂ) ⊗ₜ[ℚ̄] ((heckeDiffBar N ℓ).restrict (heckeDiffBar_mem hin ℓ) v)) =
      CuspForm.heckeTLin 2 ℓ.prop hℓN (e ((1 : ℂ) ⊗ₜ[ℚ̄] v)) := by
  letI := (emb).toAlgebra
  haveI := neZero_prime ℓ
  haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
  apply QExp.eq_of_qCoeff_eq
  intro n
  rw [he, LinearMap.coe_restrict_apply, QExp.qCoeff_heckeTLin, ModularForm.coeffHeckeT_apply, he]
  have hT := ModularCurve.coeff_diffQExpBar_heckeDiffBar_of_not_dvd N ℓ hℓN (hβ hin ℓ)
    (v : Ω[modularFunctionFieldBar N⁄ℚ̄]) n
  have hℓ' : (⟨(ℓ : ℕ), Fact.out⟩ : Nat.Primes) = ℓ := Subtype.ext rfl
  rw [hℓ'] at hT
  rw [hT, map_add, map_mul, map_natCast, Nat.cast_mul]
  congr 1
  by_cases hdvd : (ℓ : ℕ) ∣ n
  · have hdvd' : ((ℓ : ℕ) : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.mpr hdvd
    rw [if_pos hdvd', if_pos hdvd, he, Int.natCast_div]
    have h21 : ((2 : ℤ) - 1) = 1 := by norm_num
    rw [h21, zpow_one]
  · have hdvd' : ¬ ((ℓ : ℕ) : ℤ) ∣ (n : ℤ) := fun h => hdvd (Int.natCast_dvd_natCast.mp h)
    rw [if_neg hdvd', if_neg hdvd, map_zero, mul_zero]

theorem tmul_value_dvd (hin : HeckeInputsAll N) (ℓ : Nat.Primes) (hℓN : (ℓ : ℕ) ∣ N)
    (e : letI := (emb).toAlgebra
      ℂ ⊗[ℚ̄] ↥(regularDifferentialsBar N) ≃ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (he : letI := (emb).toAlgebra
      ∀ (ω : ↥(regularDifferentialsBar N)) (n : ℕ),
        ModularFormClass.qCoeff (e (1 ⊗ₜ ω)) n =
          emb ((diffQExpBar N (ω : Ω[modularFunctionFieldBar N⁄ℚ̄])).coeff n))
    (v : ↥(regularDifferentialsBar N)) :
    letI := (emb).toAlgebra
    e ((1 : ℂ) ⊗ₜ[ℚ̄] ((heckeDiffBar N ℓ).restrict (heckeDiffBar_mem hin ℓ) v)) =
      CuspForm.heckeULin 2 hℓN (e ((1 : ℂ) ⊗ₜ[ℚ̄] v)) := by
  letI := (emb).toAlgebra
  haveI := neZero_prime ℓ
  haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
  apply QExp.eq_of_qCoeff_eq
  intro n
  rw [he, LinearMap.coe_restrict_apply, QExp.qCoeff_heckeULin _ ℓ.prop hℓN, he]
  have hU := ModularCurve.coeff_diffQExpBar_heckeDiffBar_of_dvd N ℓ hℓN
    (v : Ω[modularFunctionFieldBar N⁄ℚ̄]) n
  have hℓ' : (⟨(ℓ : ℕ), Fact.out⟩ : Nat.Primes) = ℓ := Subtype.ext rfl
  rw [hℓ'] at hU
  rw [hU, Nat.cast_mul]

theorem lift_cRes_eq_zero (hin : HeckeInputsAll N) (p : FreeAlgebra ℤ Nat.Primes)
    (hp : ∀ ω ∈ regularDifferentialsBar N,
      MulOpposite.unop (FreeAlgebra.lift ℤ (fun ℓ : Nat.Primes => MulOpposite.op (heckeDiffBar N ℓ)) p) ω = 0) :
    FreeAlgebra.lift ℤ (cRes hin) p = 0 := by
  apply MulOpposite.unop_injective
  refine LinearMap.ext fun v => Subtype.ext ?_
  rw [restrict_lift hin p v, MulOpposite.unop_zero, LinearMap.zero_apply, Submodule.coe_zero]
  exact hp v v.2

def sym : FreeAlgebra ℤ Nat.Primes →ₐ[ℤ] HeckeAlg := FreeAlgebra.lift ℤ heckeGen

theorem conj_unop_lift (hin : HeckeInputsAll N)
    (e : letI := (emb).toAlgebra
      ℂ ⊗[ℚ̄] ↥(regularDifferentialsBar N) ≃ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (he : letI := (emb).toAlgebra
      ∀ (ω : ↥(regularDifferentialsBar N)) (n : ℕ),
        ModularFormClass.qCoeff (e (1 ⊗ₜ ω)) n =
          emb ((diffQExpBar N (ω : Ω[modularFunctionFieldBar N⁄ℚ̄])).coeff n))
    (p : FreeAlgebra ℤ Nat.Primes) :
    letI := (emb).toAlgebra
    conjBaseChange e (MulOpposite.unop (FreeAlgebra.lift ℤ (cRes hin) p)) = cuspHeckeRep N (sym p) := by
  letI := (emb).toAlgebra
  induction p using FreeAlgebra.induction with
  | grade0 r =>
      simp only [eq_intCast, MulOpposite.unop_intCast, map_intCast]
  | grade1 ℓ =>
      rw [FreeAlgebra.lift_ι_apply, sym, FreeAlgebra.lift_ι_apply, cRes, MulOpposite.unop_op,
        cuspHeckeRep_heckeGen]
      by_cases hℓN : (ℓ : ℕ) ∣ N
      · rw [cuspHeckeGen_of_dvd N ℓ hℓN]
        exact conjBaseChange_eq_of_tmul e _ _ (tmul_value_dvd hin ℓ hℓN e he)
      · rw [cuspHeckeGen_of_not_dvd N ℓ hℓN]
        exact conjBaseChange_eq_of_tmul e _ _ (tmul_value hin ℓ hℓN e he)
  | mul a b ha hb =>
      simp only [map_mul, MulOpposite.unop_mul]
      rw [ha, hb]
      exact cuspHeckeRep_comm N _ _
  | add a b ha hb =>
      simp only [map_add, MulOpposite.unop_add]
      rw [ha, hb]

theorem cuspHeckeRep_sym_eq_zero (hin : HeckeInputsAll N) (p : FreeAlgebra ℤ Nat.Primes)
    (hp : ∀ ω ∈ regularDifferentialsBar N,
      MulOpposite.unop (FreeAlgebra.lift ℤ (fun ℓ : Nat.Primes => MulOpposite.op (heckeDiffBar N ℓ)) p) ω = 0) :
    cuspHeckeRep N (sym p) = 0 := by
  letI : Algebra ℚ̄ ℂ := (emb).toAlgebra
  obtain ⟨e, he⟩ := ModularCurve.exists_linearEquiv_tensor_regularDifferentialsBar_cuspForm N emb
  rw [← conj_unop_lift hin e he p, lift_cRes_eq_zero hin p hp, MulOpposite.unop_zero, map_zero]

theorem dualHeckeRep_sym_eq_zero (hin : HeckeInputsAll N) (p : FreeAlgebra ℤ Nat.Primes)
    (hp : ∀ ω ∈ regularDifferentialsBar N,
      MulOpposite.unop (FreeAlgebra.lift ℤ (fun ℓ : Nat.Primes => MulOpposite.op (heckeDiffBar N ℓ)) p) ω = 0) :
    dualHeckeRep N (sym p) = 0 := by
  have h := cuspHeckeRep_sym_eq_zero hin p hp
  refine LinearMap.ext fun φ => LinearMap.ext fun f => ?_
  rw [dualHeckeRep_apply_apply, h]
  simp only [LinearMap.zero_apply, map_zero]

theorem uniformization_lift
    (u : JZero N →+
      (Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) ⧸ periodLattice N))
    (hu : ∀ (ℓ : Nat.Primes) (x : JZero N)
        (φ : Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)),
        u x = Submodule.Quotient.mk φ →
        u (heckeOperatorBar N ℓ x) = Submodule.Quotient.mk (dualHeckeRep N (heckeGen ℓ) φ))
    (p : FreeAlgebra ℤ Nat.Primes) (x : JZero N)
    (φ : Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2))
    (hx : u x = Submodule.Quotient.mk φ) :
    u (FreeAlgebra.lift ℤ (heckeOperatorBar N) p x) =
      Submodule.Quotient.mk (dualHeckeRep N (sym p) φ) := by
  induction p using FreeAlgebra.induction generalizing x φ with
  | grade0 r =>
      simp only [eq_intCast, Module.End.intCast_apply, map_zsmul, map_intCast]
      rw [← Submodule.mkQ_apply, map_zsmul, Submodule.mkQ_apply, hx]
  | grade1 ℓ =>
      rw [FreeAlgebra.lift_ι_apply, sym, FreeAlgebra.lift_ι_apply]
      exact hu ℓ x φ hx
  | mul a b ha hb =>
      simp only [map_mul, Module.End.mul_apply]
      exact ha _ _ (hb x φ hx)
  | add a b ha hb =>
      simp only [map_add, LinearMap.add_apply, Submodule.Quotient.mk_add]
      rw [ha x φ hx, hb x φ hx]

end Assembly

end W7XI

p2m_open "ModularCurve~IsCusp"

theorem solution
    (N : ℕ) [NeZero N] (hin : ModularCurve.HeckeInputsAll N)
    (p : FreeAlgebra ℤ Nat.Primes)
    (hp : ∀ ω ∈ ModularCurve.regularDifferentialsBar N,
      MulOpposite.unop (FreeAlgebra.lift ℤ
        (fun ℓ : Nat.Primes => MulOpposite.op (ModularCurve.heckeDiffBar N ℓ)) p) ω = 0) :
    FreeAlgebra.lift ℤ (ModularCurve.heckeOperatorBar N) p = 0 := by
  classical

  obtain ⟨u, hu_inj, -, hu⟩ :=
    ModularCurve.exists_injective_heckeEquivariant_addMonoidHom_jZero_quotient_periodLattice N hin
      (ModularCurve.periodLatticeHeckeStable N)

  have hD := W7XI.dualHeckeRep_sym_eq_zero hin p hp
  refine LinearMap.ext fun x => ?_
  obtain ⟨φ, hφ⟩ := Submodule.Quotient.mk_surjective (periodLattice N) (u x)
  apply hu_inj
  rw [LinearMap.zero_apply, map_zero, W7XI.uniformization_lift u hu p x φ hφ.symm, hD,
    LinearMap.zero_apply, Submodule.Quotient.mk_zero]

end

end S_ModularCurve_freeAlgebra_lift_heckeOperatorBar_eq_zero_of_lift_heckeDiffBar_eq_zero
end P2MW
export P2MW.S_ModularCurve_freeAlgebra_lift_heckeOperatorBar_eq_zero_of_lift_heckeDiffBar_eq_zero (solution)
