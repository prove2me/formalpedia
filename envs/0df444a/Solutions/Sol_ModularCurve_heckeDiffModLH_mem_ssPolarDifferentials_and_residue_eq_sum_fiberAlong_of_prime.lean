-- Prove2me | solution 1 for ModularCurve.heckeDiffModLH_mem_ssPolarDifferentials_and_residue_eq_sum_fiberAlong_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/06a6605b-7988-5065-a1ee-495a88157a22

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_ModularCurve_XH
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Theorems.Thm_AlgebraicCurve_Place_isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_sum_traceAlong_of_separableAlong_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_mul_pullbackAlong_restrictAlong
import Theorems.Thm_ModularCurve_finiteAlong_and_separableAlong_heckeAlphaModLH_heckeBetaModLH_of_natCast_ne_zero
import Theorems.Thm_AlgebraicCurve_existsUnique_hasSimpleResidue_of_hasSimplePoleAt
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_essFiniteType_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_isCurveOver_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Theorems.Thm_ModularCurve_restrictAlong_heckeBetaModLH_mem_ssPlacesQExp_iff_and_restrictAlong_heckeAlphaModLH_mem_ssPlacesQExp_iff_of_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_heckeDiffModLH_mem_ssPolarDifferentials_and_residue_eq_sum_fiberAlong_of_prime
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion"
p2m_attr_erase "instance" "ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false

open scoped MatrixGroups
open AlgebraicCurve

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N) (H' : Subgroup (ZMod N)ˣ) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0)

    (res : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH N H') p) →ₗ[K]
      (AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) → K))
    (hres : ∀ (ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH N H') p))
      (v : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))),
      v ∈ ModularCurve.ssPlacesQExp K (CohCarrier.GammaH N H') p →
        v.HasSimpleResidue (ω : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K]) (res ω v))
    (hres0 : ∀ (ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH N H') p))
      (v : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))),
      v ∉ ModularCurve.ssPlacesQExp K (CohCarrier.GammaH N H') p → res ω v = 0)
    (hα : (ModularCurve.heckeAlphaModLH K N H' ℓ).toRingHom.IsIntegral)
    (hβ : (ModularCurve.heckeBetaModLH K N H' ℓ).toRingHom.IsIntegral)
    [AlgebraicCurve.HasPrincipalDivisors K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)))] :
    (∀ ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH N H') p),
        ModularCurve.heckeDiffModLH K N H' ℓ (ω : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K]) ∈
          ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH N H') p) ∧
    (∀ (ω ω' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH N H') p)),
        (ω' : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K]) =
          ModularCurve.heckeDiffModLH K N H' ℓ (ω : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K]) →
        ∀ v : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')),
          res ω' v =
            ∑ w ∈ AlgebraicCurve.Place.fiberAlong (ModularCurve.heckeBetaModLH K N H' ℓ) hβ v,
              (AlgebraicCurve.Place.ramificationIndexAlong (ModularCurve.heckeAlphaModLH K N H' ℓ) w : K) *
                res ω (AlgebraicCurve.Place.restrictAlong (ModularCurve.heckeAlphaModLH K N H' ℓ) hα w)) := by
  classical

  have hT : ModularGroup.T ∈ CohCarrier.GammaH N H' := ModularCurve.translation_mem_GammaH N H'
  have hT0 : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 (N * ℓ) := by
    rw [CongruenceSubgroup.Gamma0_mem]
    simp [ModularGroup.T]
  have hT' : ModularGroup.T ∈ CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ) := ⟨hT, hT0⟩
  haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne ℓ)⟩
  haveI : (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)).FiniteIndex := inferInstance
  obtain ⟨x, -, htr, hfd⟩ := ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed K (CohCarrier.GammaH N H') hT
  obtain ⟨x', -, htr', hfd'⟩ := ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed K
    (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)) hT'
  haveI : Algebra.EssFiniteType K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) := ModularCurve.essFiniteType_qExpFunctionFieldC_of_isAlgClosed K (CohCarrier.GammaH N H') hT
  haveI : AlgebraicCurve.IsCurveOver K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) := ModularCurve.isCurveOver_qExpFunctionFieldC_of_isAlgClosed K (CohCarrier.GammaH N H') hT
  haveI : AlgebraicCurve.HasCanonicalDivisor (K := K) (F := ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))) := AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver
  have hsep : AlgebraicCurve.SeparableAlong K (ModularCurve.heckeBetaModLH K N H' ℓ) :=
    (ModularCurve.finiteAlong_and_separableAlong_heckeAlphaModLH_heckeBetaModLH_of_natCast_ne_zero K N H' ℓ hℓ).2.2.2

  have TR := fun (v : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))) (η : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))⁄K]) =>
    AlgebraicCurve.Place.isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_sum_traceAlong_of_separableAlong_of_isAlgClosed
      htr hfd htr' hfd' (ModularCurve.heckeBetaModLH K N H' ℓ) hβ hsep v η
  have PB := fun (w : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)))) (ω : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K]) =>
    AlgebraicCurve.Place.isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_mul_pullbackAlong_restrictAlong
      htr hfd htr' hfd' (ModularCurve.heckeAlphaModLH K N H' ℓ) hα w ω
  have CP := fun (w : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)))) => (ModularCurve.restrictAlong_heckeBetaModLH_mem_ssPlacesQExp_iff_and_restrictAlong_heckeAlphaModLH_mem_ssPlacesQExp_iff_of_prime K p N hpN H' ℓ hℓ hα hβ w).1
  have hpol := fun (ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH N H') p)) => (ModularCurve.mem_ssPolarDifferentials_iff _).mp ω.2

  have hmem : ∀ ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH N H') p),
      ModularCurve.heckeDiffModLH K N H' ℓ (ω : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K]) ∈ ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH N H') p := by
    intro ω
    rw [ModularCurve.mem_ssPolarDifferentials_iff, ModularCurve.heckeDiffModLH_apply]
    intro v
    constructor
    · intro hv
      apply (TR v _).1
      intro w hw
      rw [AlgebraicCurve.Place.mem_fiberAlong] at hw
      have hα' : AlgebraicCurve.Place.restrictAlong (ModularCurve.heckeAlphaModLH K N H' ℓ) hα w ∉ ModularCurve.ssPlacesQExp K (CohCarrier.GammaH N H') p := fun h => hv (hw ▸ (CP w).mpr h)
      exact (PB w ω).1 ((hpol ω _).1 hα')
    · intro hv
      apply (TR v _).2.1
      intro w hw
      by_cases hαw : AlgebraicCurve.Place.restrictAlong (ModularCurve.heckeAlphaModLH K N H' ℓ) hα w ∈ ModularCurve.ssPlacesQExp K (CohCarrier.GammaH N H') p
      · exact (PB w ω).2.1 ((hpol ω _).2 hαw)
      · exact (PB w ω).2.1 ((hpol ω _).1 hαw).hasSimplePoleAt
  refine ⟨hmem, ?_⟩

  intro ω ω' hω' v
  have hsum : AlgebraicCurve.Place.HasSimpleResidue v (ω' : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K])
      (∑ w ∈ AlgebraicCurve.Place.fiberAlong (ModularCurve.heckeBetaModLH K N H' ℓ) hβ v,
        (AlgebraicCurve.Place.ramificationIndexAlong (ModularCurve.heckeAlphaModLH K N H' ℓ) w : K) * res ω (AlgebraicCurve.Place.restrictAlong (ModularCurve.heckeAlphaModLH K N H' ℓ) hα w)) := by
    rw [hω', ModularCurve.heckeDiffModLH_apply]
    apply (TR v _).2.2 (fun w => (AlgebraicCurve.Place.ramificationIndexAlong (ModularCurve.heckeAlphaModLH K N H' ℓ) w : K) * res ω (AlgebraicCurve.Place.restrictAlong (ModularCurve.heckeAlphaModLH K N H' ℓ) hα w))
    intro w hw
    by_cases hαw : AlgebraicCurve.Place.restrictAlong (ModularCurve.heckeAlphaModLH K N H' ℓ) hα w ∈ ModularCurve.ssPlacesQExp K (CohCarrier.GammaH N H') p
    · exact (PB w ω).2.2 _ (hres ω _ hαw)
    · obtain ⟨f, hf, hωf⟩ := (hpol ω _).1 hαw
      have h0 : (AlgebraicCurve.Place.restrictAlong (ModularCurve.heckeAlphaModLH K N H' ℓ) hα w).HasSimpleResidue (ω : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K]) 0 := by
        rw [hωf]
        exact AlgebraicCurve.Place.hasSimpleResidue_zero_of_mem hf
      rw [hres0 ω _ hαw]
      simpa using (PB w ω).2.2 0 h0
  by_cases hv : v ∈ ModularCurve.ssPlacesQExp K (CohCarrier.GammaH N H') p
  · obtain ⟨a, -, huniq⟩ := AlgebraicCurve.existsUnique_hasSimpleResidue_of_hasSimplePoleAt v (ω' : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K]) hsum.hasSimplePoleAt
    exact (huniq _ (hres ω' v hv)).trans (huniq _ hsum).symm
  · have hreg : v.IsRegularAt (ω' : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K]) := by
      rw [hω']
      exact ((ModularCurve.mem_ssPolarDifferentials_iff _).mp (hmem ω) v).1 hv
    obtain ⟨f, hf, hωf⟩ := hreg
    have h0 : v.HasSimpleResidue (ω' : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K]) 0 := by
      rw [hωf]
      exact AlgebraicCurve.Place.hasSimpleResidue_zero_of_mem hf
    obtain ⟨a, -, huniq⟩ := AlgebraicCurve.existsUnique_hasSimpleResidue_of_hasSimplePoleAt v (ω' : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K]) hsum.hasSimplePoleAt
    rw [hres0 ω' v hv]
    exact (huniq _ h0).trans (huniq _ hsum).symm

end S_ModularCurve_heckeDiffModLH_mem_ssPolarDifferentials_and_residue_eq_sum_fiberAlong_of_prime
end P2MW
export P2MW.S_ModularCurve_heckeDiffModLH_mem_ssPolarDifferentials_and_residue_eq_sum_fiberAlong_of_prime (solution)
