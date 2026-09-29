-- Prove2me | solution 1 for ModularCurve.exists_linearEquiv_tensor_regularDifferentialsBar_cuspForm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/b6eaf84f-a106-538b-a473-2a36db48299b

import Mathlib
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Theorems.Thm_CuspForm_hasIntegralStructure_two
import Theorems.Thm_CuspForm_finrank_gamma0_weight_two_eq_genusFormula
import Theorems.Thm_CuspForm_finiteDimensional_Gamma0
import Theorems.Thm_ModularCurve_genus_modularFunctionFieldBar_eq_genusFormula
import Theorems.Thm_ModularCurve_hasCanonicalDivisor_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_exists_coeffMap_diffQExpBar_eq_qExpansion
import Theorems.Thm_ModularCurve_mem_regularDifferentialsBar_of_coeffMap_diffQExpBar_eq_qExpansion
import Theorems.Thm_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_linearEquiv_tensor_regularDifferentialsBar_cuspForm
p2m_attr_erase "instance" "CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange"
p2m_attr_erase "instance" "WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin"
p2m_attr_erase "simp" "CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe"
p2m_attr_erase "simp" "ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero"
p2m_attr_erase "simp" "Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"

open scoped TensorProduct
p2m_open "ModularCurve~IsCusp"

noncomputable section

namespace W7XGagaD

open ModularForm ModularFormClass Complex
p2m_open "UpperHalfPlane~I"

local notation "𝕢" => Function.Periodic.qParam
local notation "ℚ̄" => AlgebraicClosure ℚ

section Gamma0

variable {N : ℕ} {k : ℤ}

lemma one_mem_strictPeriods :
    (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

lemma hasSum_qCoeff (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : ℍ) :
    HasSum (fun m ↦ qCoeff f m * 𝕢 1 τ ^ m) (f τ) := by
  haveI : Fact (IsCusp OnePoint.infty (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos one_mem_strictPeriods⟩
  have := hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) τ
  (first | exact this | simpa only [smul_eq_mul] using this | (have h__ := this; simp only [smul_eq_mul] at h__; exact h__))

lemma qCoeff_zero (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) : qCoeff f 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero f one_pos one_mem_strictPeriods

lemma eq_zero_of_forall_qCoeff_eq_zero (f : CuspForm (CongruenceSubgroup.Gamma0 N) k)
    (h : ∀ n, qCoeff f n = 0) : f = 0 := by
  refine DFunLike.ext _ _ fun τ => ?_
  have hs := hasSum_qCoeff f τ
  have hz : (fun m ↦ qCoeff f m * 𝕢 1 τ ^ m) = fun _ => 0 := by
    funext m
    rw [h m, zero_mul]
  rw [hz] at hs
  simpa using hs.unique hasSum_zero

end Gamma0

section S2side

variable (N : ℕ)

def qCoeffLin (n : ℕ) : CuspForm (CongruenceSubgroup.Gamma0 N) 2 →ₗ[ℂ] ℂ where
  toFun f := qCoeff f n
  map_add' f g := by
    simp only [qCoeff, CuspForm.coe_add]
    rw [ModularForm.qExpansion_add one_pos one_mem_strictPeriods f g, map_add]
  map_smul' c f := by
    simp only [qCoeff, CuspForm.IsGLPos.coe_smul, RingHom.id_apply, smul_eq_mul]
    rw [ModularForm.qExpansion_smul one_pos one_mem_strictPeriods c f]
    simp

@[scoped simp] lemma qCoeffLin_apply (n : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    qCoeffLin N n f = qCoeff f n := rfl

end S2side

section EssFinite

variable (N : ℕ) [NeZero N]

theorem divisorExpansions_finite : (divisorExpansions N).Finite := by
  classical
  let g : ℕ → LaurentSeries ℚ :=
    fun d => if h : d = 0 then 0 else (haveI : NeZero d := ⟨h⟩; qExpand ℚ d jq)
  refine ((Set.finite_Iic N).image g).subset ?_
  rintro x ⟨d, hd, hdN, rfl⟩
  refine ⟨d, Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hdN, ?_⟩
  simp only [g, dif_neg hd.ne]

omit [NeZero N] in

theorem modularFunctionFieldBar_eq_adjoin :
    modularFunctionFieldBar N =
      IntermediateField.adjoin ℚ̄ (coeffEmb ℚ̄ '' divisorExpansions N) := by
  apply le_antisymm
  · change laurentBaseChange ℚ̄ (modularFunctionFieldFull N) ≤ _
    unfold laurentBaseChange
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    change y ∈ modularFunctionFieldFull N at hy
    unfold modularFunctionFieldFull at hy
    change y ∈ Subfield.closure
      (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ divisorExpansions N) at hy
    refine Subfield.closure_induction (p := fun y _ =>
      coeffEmb ℚ̄ y ∈ (IntermediateField.adjoin ℚ̄ (coeffEmb ℚ̄ '' divisorExpansions N)))
      ?_ ?_ ?_ ?_ ?_ ?_ hy
    · rintro z (⟨a, rfl⟩ | hz)
      · rw [eq_ratCast, map_ratCast]
        have h := IntermediateField.algebraMap_mem
          (IntermediateField.adjoin ℚ̄ (coeffEmb ℚ̄ '' divisorExpansions N)) (a : ℚ̄)
        rwa [map_ratCast] at h
      · exact IntermediateField.subset_adjoin _ _ ⟨z, hz, rfl⟩
    · show coeffEmb ℚ̄ 1 ∈ _
      rw [map_one]; exact one_mem _
    · intro a b _ _ ha hb
      show coeffEmb ℚ̄ (a + b) ∈ _
      rw [map_add]; exact add_mem ha hb
    · intro a _ ha
      show coeffEmb ℚ̄ (-a) ∈ _
      rw [map_neg]; exact neg_mem ha
    · intro a _ ha
      show coeffEmb ℚ̄ a⁻¹ ∈ _
      rw [map_inv₀]; exact inv_mem ha
    · intro a b _ _ ha hb
      show coeffEmb ℚ̄ (a * b) ∈ _
      rw [map_mul]; exact mul_mem ha hb
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    exact coeffEmb_mem_laurentBaseChange ℚ̄
      (IntermediateField.subset_adjoin ℚ (divisorExpansions N) hy)

theorem essFiniteType_bar : Algebra.EssFiniteType ℚ̄ (modularFunctionFieldBar N) := by
  have h : (modularFunctionFieldBar N).FG :=
    IntermediateField.fg_def.mpr
      ⟨_, (divisorExpansions_finite N).image _, (modularFunctionFieldBar_eq_adjoin N).symm⟩
  exact IntermediateField.essFiniteType_iff.mpr h

end EssFinite

section IntegralBasis

variable (N : ℕ) [NeZero N]

theorem exists_integral_basis :
    ∃ (s : Set (CuspForm (CongruenceSubgroup.Gamma0 N) 2))
      (b : Module.Basis s ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)),
      ∀ (i : s) (n : ℕ), ∃ m : ℤ, qCoeff (b i) n = (m : ℂ) := by
  set T : Set (CuspForm (CongruenceSubgroup.Gamma0 N) 2) :=
    {f | ∀ n : ℕ, ∃ m : ℤ, qCoeff f n = (m : ℂ)} with hTdef
  have hT : Submodule.span ℂ T = ⊤ := by
    have h : Submodule.span ℂ ((Submodule.span ℤ T :
        Submodule ℤ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) :
        Set (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) = ⊤ :=
      CuspForm.hasIntegralStructure_two N
    rwa [Submodule.span_span_of_tower] at h
  obtain ⟨s, hsT, hspan, hli⟩ := exists_linearIndependent ℂ T
  refine ⟨s, Module.Basis.mk hli ?_, fun i n => ?_⟩
  · rw [Subtype.range_coe_subtype, Set.setOf_mem_eq, hspan, hT]
  · rw [Module.Basis.mk_apply]
    exact hsT i.2 n

end IntegralBasis

section Coeff

variable (N : ℕ)

def coeffFun (n : ℕ) : ↥(regularDifferentialsBar N) →ₗ[ℚ̄] ℚ̄ where
  toFun ω := (diffQExpBar N (ω : Ω[modularFunctionFieldBar N⁄ℚ̄])).coeff (n : ℤ)
  map_add' ω₁ ω₂ := by
    simp only [Submodule.coe_add, map_add, HahnSeries.coeff_add]
  map_smul' c ω := by
    simp only [Submodule.coe_smul, RingHom.id_apply, smul_eq_mul]
    rw [← algebraMap_smul (modularFunctionFieldBar N) c (ω : Ω[modularFunctionFieldBar N⁄ℚ̄]),
      map_smul]
    change (((algebraMap ℚ̄ (modularFunctionFieldBar N) c : modularFunctionFieldBar N) :
        LaurentSeries ℚ̄) * diffQExpBar N (ω : Ω[modularFunctionFieldBar N⁄ℚ̄])).coeff (n : ℤ) = _
    change (algebraMap ℚ̄ (LaurentSeries ℚ̄) c * _).coeff _ = _
    rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul]

@[scoped simp] theorem coeffFun_apply (n : ℕ) (ω : ↥(regularDifferentialsBar N)) :
    coeffFun N n ω = (diffQExpBar N (ω : Ω[modularFunctionFieldBar N⁄ℚ̄])).coeff (n : ℤ) := rfl

variable [Algebra ℚ̄ ℂ]

def coeffFunC (n : ℕ) : ℂ ⊗[ℚ̄] ↥(regularDifferentialsBar N) →ₗ[ℂ] ℂ :=
  (Algebra.TensorProduct.lmul'' ℚ̄ (S := ℂ)).toLinearMap ∘ₗ
    (((Algebra.linearMap ℚ̄ ℂ).comp (coeffFun N n)).baseChange ℂ)

theorem coeffFunC_tmul (n : ℕ) (c : ℂ) (ω : ↥(regularDifferentialsBar N)) :
    coeffFunC N n (c ⊗ₜ ω) =
      c * algebraMap ℚ̄ ℂ ((diffQExpBar N (ω : Ω[modularFunctionFieldBar N⁄ℚ̄])).coeff (n : ℤ)) := by
  simp [coeffFunC, LinearMap.baseChange_tmul]
  rfl

end Coeff

section Main

variable (N : ℕ) [NeZero N]

theorem exists_regularDifferential_of_integral (ι₀ : ℚ̄ →+* ℂ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (hf : ∀ n : ℕ, ∃ m : ℤ, qCoeff f n = (m : ℂ)) :
    ∃ ω : ↥(regularDifferentialsBar N), ∀ n : ℕ,
      ι₀ ((diffQExpBar N (ω : Ω[modularFunctionFieldBar N⁄ℚ̄])).coeff (n : ℤ)) = qCoeff f n := by
  have hrange : ∀ n : ℕ, qCoeff f n ∈ ι₀.range := fun n => by
    obtain ⟨m, hm⟩ := hf n
    exact ⟨m, by rw [hm, map_intCast]⟩
  obtain ⟨ω, hωq⟩ := ModularCurve.exists_coeffMap_diffQExpBar_eq_qExpansion N ι₀ f hrange
  refine ⟨⟨ω, ModularCurve.mem_regularDifferentialsBar_of_coeffMap_diffQExpBar_eq_qExpansion
    N ι₀ f ω hωq⟩, fun n => ?_⟩
  have h := congrArg (fun x : LaurentSeries ℂ => x.coeff (n : ℤ)) hωq
  simp only [coeffMap_coeff, HahnSeries.ofPowerSeries_apply_coeff] at h
  exact h

theorem main (ι₀ : ℚ̄ →+* ℂ) :
    letI := ι₀.toAlgebra
    ∃ e : ℂ ⊗[ℚ̄] ↥(regularDifferentialsBar N) ≃ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma0 N) 2,
      ∀ (ω : ↥(regularDifferentialsBar N)) (n : ℕ),
        qCoeff (e (1 ⊗ₜ ω)) n =
          ι₀ ((diffQExpBar N (ω : Ω[modularFunctionFieldBar N⁄ℚ̄])).coeff n) := by
  letI : Algebra ℚ̄ ℂ := ι₀.toAlgebra

  obtain ⟨s, b, hb⟩ := exists_integral_basis N

  have hω : ∀ i : s, ∃ ω : ↥(regularDifferentialsBar N), ∀ n : ℕ,
      ι₀ ((diffQExpBar N (ω : Ω[modularFunctionFieldBar N⁄ℚ̄])).coeff (n : ℤ)) = qCoeff (b i) n :=
    fun i => exists_regularDifferential_of_integral N ι₀ (b i) (hb i)
  choose ω hω using hω

  let Ψ : CuspForm (CongruenceSubgroup.Gamma0 N) 2 →ₗ[ℂ] ℂ ⊗[ℚ̄] ↥(regularDifferentialsBar N) :=
    b.constr ℂ fun i => (1 : ℂ) ⊗ₜ[ℚ̄] ω i
  have hΨb : ∀ i, Ψ (b i) = (1 : ℂ) ⊗ₜ[ℚ̄] ω i := fun i => by
    simp only [Ψ, Module.Basis.constr_basis]

  have hQΨ : ∀ (n : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2),
      coeffFunC N n (Ψ f) = qCoeff f n := by
    intro n
    have hcomp : (coeffFunC N n).comp Ψ = qCoeffLin N n := by
      refine b.ext fun i => ?_
      rw [LinearMap.comp_apply, hΨb, coeffFunC_tmul, one_mul, qCoeffLin_apply]
      exact hω i n
    intro f
    simpa using LinearMap.congr_fun hcomp f

  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro f hf
    refine eq_zero_of_forall_qCoeff_eq_zero f fun n => ?_
    rw [← hQΨ n f, LinearMap.mem_ker.mp hf, map_zero]

  haveI : FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) :=
    CuspForm.finiteDimensional_Gamma0 N 2
  haveI := ModularCurve.hasCanonicalDivisor_modularFunctionFieldBar N
  haveI := ModularCurve.isCurveOver_modularFunctionFieldBar N
  haveI := essFiniteType_bar N
  obtain ⟨hfinΩ, hrankΩ⟩ :=
    AlgebraicCurve.finite_and_finrank_regularDifferentials_eq_genus
      (K := ℚ̄) (F := modularFunctionFieldBar N)
  haveI : Module.Finite ℚ̄ ↥(regularDifferentialsBar N) := hfinΩ
  have hdim : Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) =
      Module.finrank ℂ (ℂ ⊗[ℚ̄] ↥(regularDifferentialsBar N)) := by
    have h1 : Module.finrank ℂ (ℂ ⊗[ℚ̄] ↥(regularDifferentialsBar N)) =
        Module.finrank ℚ̄ ↥(regularDifferentialsBar N) :=
      Module.finrank_baseChange
    have h2 : (AlgebraicCurve.genus ℚ̄ ↥(modularFunctionFieldBar N) : ℚ) = genusFormula N :=
      ModularCurve.genus_modularFunctionFieldBar_eq_genusFormula N
    have h3 : (Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) : ℚ) =
        genusFormula N :=
      CuspForm.finrank_gamma0_weight_two_eq_genusFormula N
    have h4 : Module.finrank ℚ̄ ↥(regularDifferentialsBar N) =
        AlgebraicCurve.genus ℚ̄ ↥(modularFunctionFieldBar N) := hrankΩ
    have : (Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) : ℚ) =
        (Module.finrank ℂ (ℂ ⊗[ℚ̄] ↥(regularDifferentialsBar N)) : ℚ) := by
      rw [h3, ← h2, h1, h4]
    exact_mod_cast this

  let e₀ : CuspForm (CongruenceSubgroup.Gamma0 N) 2 ≃ₗ[ℂ] ℂ ⊗[ℚ̄] ↥(regularDifferentialsBar N) :=
    LinearMap.linearEquivOfInjective Ψ hinj hdim
  refine ⟨e₀.symm, fun ω' n => ?_⟩
  have he : Ψ (e₀.symm ((1 : ℂ) ⊗ₜ[ℚ̄] ω')) = (1 : ℂ) ⊗ₜ[ℚ̄] ω' := by
    show e₀ (e₀.symm _) = _
    exact e₀.apply_symm_apply _
  rw [← hQΨ n, he, coeffFunC_tmul, one_mul]
  rfl

end Main

end W7XGagaD
p2m_reactivate "P2MW.S_ModularCurve_exists_linearEquiv_tensor_regularDifferentialsBar_cuspForm.W7XGagaD"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_linearEquiv_tensor_regularDifferentialsBar_cuspForm.W7XGagaD"

open scoped TensorProduct in
p2m_open "ModularCurve~IsCusp" in
theorem solution (N : ℕ) [NeZero N]
    (ι₀ : AlgebraicClosure ℚ →+* ℂ) :
    letI := ι₀.toAlgebra
    ∃ e : ℂ ⊗[AlgebraicClosure ℚ] ↥(ModularCurve.regularDifferentialsBar N) ≃ₗ[ℂ]
        CuspForm (CongruenceSubgroup.Gamma0 N) 2,
      ∀ (ω : ↥(ModularCurve.regularDifferentialsBar N)) (n : ℕ),
        ModularFormClass.qCoeff (e (1 ⊗ₜ ω)) n =
          ι₀ ((ModularCurve.diffQExpBar N (ω : Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ])).coeff n) :=
  W7XGagaD.main N ι₀

end S_ModularCurve_exists_linearEquiv_tensor_regularDifferentialsBar_cuspForm
end P2MW
export P2MW.S_ModularCurve_exists_linearEquiv_tensor_regularDifferentialsBar_cuspForm (solution)
