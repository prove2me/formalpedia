-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_mem_riemannRochSpace_residue_eq_of_isGoodDiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/fa7d13b1-21de-5581-958e-6e31e16bb045

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_linearIndependent_residuePair_of_riemannRochSpace
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_residue_mem_riemannRochSpace_mapDomain_and_hasValue_of_isGoodDiv
import Theorems.Thm_ModularCurve_ell_eq_degree_add_one_sub_genusFF_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_genusFF_modularFunctionFieldBar_mul_add_one_eq_of_ssPlaces
import Theorems.Thm_ModularCurve_degree_add_one_sub_genusFF_le_finrank_riemannRochSpace
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
import Theorems.Thm_ModularCurve_arithFrobC_smul_mem_ssPlaces_univ
import Theorems.Thm_ModularCurve_linearIndependent_map_prod_of_coe_eq_coeffMap
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_AlgebraicCurve_exists_mem_riemannRochSpace_forall_hasValue_mul_of_exists_not_mem
import Theorems.Thm_AlgebraicCurve_finrank_add_card_le_of_forall_exists_mem_riemannRochSpace_hasValue_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_mem_riemannRochSpace_residue_eq_of_isGoodDiv
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom"
p2m_attr_erase "simp" "ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl"
p2m_attr_erase "simp" "ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero"
p2m_attr_erase "simp" "TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_mem_riemannRochSpace_residue_eq_of_isGoodDiv.AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place.hasValue_one Place.hasValue_algebraMap Place Divisor Divisor.degree Divisor.degree_single IsCurveOver IsCurveOver.finiteResidue riemannRochSpace mem_riemannRochSpace_iff genusFF exists_mem_riemannRochSpace_forall_hasValue_mul_of_exists_not_mem finrank_add_card_le_of_forall_exists_mem_riemannRochSpace_hasValue_mul"
namespace EvalCount
p2m_open "AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ≠ 0) (h : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f :=
  ((v.adicValuation_le_one_iff).mp (v.adicValuation_le_one_of_mem h)).resolve_left hf

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h
  rw [hu, hn, zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem π.2 n)

theorem hasValue_zero_of_ord_pos (v : Place K F) {f : F} (h : f = 0 ∨ 0 < v.ord f) :
    v.HasValue f 0 := by
  rcases h with rfl | h
  · simpa using Place.hasValue_algebraMap v (0 : K)
  · have hf : f ≠ 0 := by
      rintro rfl
      simp at h
    have hlt : v.adicValuation f < 1 := by
      rw [v.adicValuation_eq_exp_neg_ord hf, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    have hmem : f ∈ v.toValuationSubring := v.mem_iff_adicValuation_le_one.mpr hlt.le
    refine ⟨hmem, ?_⟩
    have hmax : (⟨f, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
      (v.mem_maximalIdeal_iff_adicValuation_lt_one _).mpr hlt
    rw [map_zero, IsLocalRing.residue_eq_zero_iff]
    exact hmax

theorem hasValue_zero (v : Place K F) : v.HasValue (0 : F) 0 :=
  hasValue_zero_of_ord_pos v (Or.inl rfl)

theorem hvAdd {v : Place K F} {f g : F} {a b : K} (hf : v.HasValue f a) (hg : v.HasValue g b) :
    v.HasValue (f + g) (a + b) := by
  obtain ⟨hfm, hfr⟩ := hf
  obtain ⟨hgm, hgr⟩ := hg
  refine ⟨add_mem hfm hgm, ?_⟩
  have e : (⟨f + g, add_mem hfm hgm⟩ : v.toValuationSubring) = ⟨f, hfm⟩ + ⟨g, hgm⟩ := rfl
  rw [e, map_add, hfr, hgr, map_add]

theorem hvSmul {v : Place K F} {f : F} {a : K} (c : K) (hf : v.HasValue f a) :
    v.HasValue (c • f) (c * a) := by
  rw [Algebra.smul_def]
  exact (Place.hasValue_algebraMap v c).mul hf

theorem hvSum {v : Place K F} {ι : Type*} (s : Finset ι) (f : ι → F) (b : ι → K)
    (h : ∀ j ∈ s, v.HasValue (f j) (b j)) :
    v.HasValue (∑ j ∈ s, f j) (∑ j ∈ s, b j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasValue_zero v
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact hvAdd (h a (Finset.mem_insert_self a s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem riemannRochSpace_mono {D D' : Divisor K F} (h : D ≤ D') :
    riemannRochSpace D ≤ riemannRochSpace D' := by
  intro f hf
  rw [mem_riemannRochSpace_iff] at hf ⊢
  intro v
  rcases hf v with h0 | h0
  · exact Or.inl h0
  · exact Or.inr ((neg_le_neg (Finsupp.le_def.mp h v)).trans h0)

theorem ne_zero_and_ord_add_eq_zero {D : Divisor K F} {f : F} {w : Place K F}
    (hf : f ∈ riemannRochSpace D) (hf' : f ∉ riemannRochSpace (D - Finsupp.single w 1)) :
    f ≠ 0 ∧ w.ord f + D w = 0 := by
  rw [mem_riemannRochSpace_iff] at hf hf'
  push Not at hf'
  obtain ⟨v, hf0, hv⟩ := hf'
  have hvw : v = w := by
    by_contra hne
    have h1 : (D - Finsupp.single w 1 : Divisor K F) v = D v := by
      rw [Finsupp.sub_apply, Finsupp.single_eq_of_ne hne, sub_zero]
    rcases hf v with h | h
    · exact hf0 h
    · rw [h1] at hv
      exact absurd h (not_le.mpr hv)
  subst hvw
  refine ⟨hf0, ?_⟩
  rcases hf v with h | h
  · exact absurd h hf0
  · rw [Finsupp.sub_apply, Finsupp.single_eq_same] at hv
    omega

theorem exists_mem_riemannRochSpace_not_mem_of_finrank_lt {D D' : Divisor K F}
    [FiniteDimensional K ↥(riemannRochSpace D')]
    (h : Module.finrank K ↥(riemannRochSpace D') < Module.finrank K ↥(riemannRochSpace D)) :
    ∃ p ∈ riemannRochSpace D, p ∉ riemannRochSpace D' := by
  by_contra hcon
  push Not at hcon
  have hle : riemannRochSpace D ≤ riemannRochSpace D' := fun p hp => hcon p hp
  exact absurd (LinearMap.finrank_le_finrank_of_injective (Submodule.inclusion_injective hle)) (not_le.mpr h)

theorem twist_mul_mem {E : Divisor K F} {v : Place K F} {t p : F} (ht0 : t ≠ 0) (ht : v.ord t = E v)
    (hp : p ∈ riemannRochSpace E) : t * p ∈ v.toValuationSubring := by
  rcases eq_or_ne p 0 with rfl | hp0
  · rw [mul_zero]; exact zero_mem _
  · apply mem_of_ord_nonneg v (mul_ne_zero ht0 hp0)
    rcases (mem_riemannRochSpace_iff.mp hp) v with h | h
    · exact absurd h hp0
    · rw [v.ord_mul ht0 hp0, ht]
      omega

theorem exists_hasValue_twist_mul {E : Divisor K F} {v : Place K F} {t p : F}
    (hrat : Function.Surjective (algebraMap K v.ResidueField))
    (ht0 : t ≠ 0) (ht : v.ord t = E v) (hp : p ∈ riemannRochSpace E) :
    ∃ a : K, v.HasValue (t * p) a := by
  obtain ⟨a, ha, -⟩ := v.exists_hasValue_of_surjective hrat (twist_mul_mem ht0 ht hp)
  exact ⟨a, ha⟩

section TwistedPairs

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def twistedPairs {ι : Type*} (E₁ E₂ : Divisor K F) (v₁ v₂ : ι → Place K F) (t₁ t₂ : ι → F) (lam : ι → K) :
    Submodule K (F × F) where
  carrier := {p | p.1 ∈ riemannRochSpace E₁ ∧ p.2 ∈ riemannRochSpace E₂ ∧
    ∀ i, ∃ c : K, (v₁ i).HasValue (t₁ i * p.1) (lam i * c) ∧ (v₂ i).HasValue (t₂ i * p.2) c}
  zero_mem' := by
    refine ⟨zero_mem _, zero_mem _, fun i => ⟨0, ?_, ?_⟩⟩
    · rw [Prod.fst_zero, mul_zero, mul_zero]; exact hasValue_zero _
    · rw [Prod.snd_zero, mul_zero]; exact hasValue_zero _
  add_mem' := by
    rintro p q ⟨hp₁, hp₂, hp⟩ ⟨hq₁, hq₂, hq⟩
    refine ⟨add_mem hp₁ hq₁, add_mem hp₂ hq₂, fun i => ?_⟩
    obtain ⟨c, hc₁, hc₂⟩ := hp i
    obtain ⟨d, hd₁, hd₂⟩ := hq i
    refine ⟨c + d, ?_, ?_⟩
    · rw [Prod.fst_add, mul_add, mul_add]; exact hvAdd hc₁ hd₁
    · rw [Prod.snd_add, mul_add]; exact hvAdd hc₂ hd₂
  smul_mem' := by
    rintro a p ⟨hp₁, hp₂, hp⟩
    refine ⟨Submodule.smul_mem _ _ hp₁, Submodule.smul_mem _ _ hp₂, fun i => ?_⟩
    obtain ⟨c, hc₁, hc₂⟩ := hp i
    refine ⟨a * c, ?_, ?_⟩
    · rw [Prod.smul_fst, mul_smul_comm, mul_left_comm]; exact hvSmul a hc₁
    · rw [Prod.smul_snd, mul_smul_comm]; exact hvSmul a hc₂

theorem mem_twistedPairs_iff {ι : Type*} (E₁ E₂ : Divisor K F) (v₁ v₂ : ι → Place K F) (t₁ t₂ : ι → F)
    (lam : ι → K) (p : F × F) :
    p ∈ twistedPairs E₁ E₂ v₁ v₂ t₁ t₂ lam ↔ p.1 ∈ riemannRochSpace E₁ ∧ p.2 ∈ riemannRochSpace E₂ ∧
      ∀ i, ∃ c : K, (v₁ i).HasValue (t₁ i * p.1) (lam i * c) ∧ (v₂ i).HasValue (t₂ i * p.2) c :=
  Iff.rfl

end TwistedPairs

section Avoid

variable {k₀ K M : Type*} [Field k₀] [Field K] [AddCommGroup M] [Module K M]

def coeffPreimage (σ : k₀ →+* K) {n : ℕ} (p : Fin n → M) (H : Submodule K M) :
    Submodule k₀ (Fin n → k₀) where
  carrier := {μ | (∑ j, σ (μ j) • p j) ∈ H}
  zero_mem' := by
    show (∑ j, σ ((0 : Fin n → k₀) j) • p j) ∈ H
    simp only [Pi.zero_apply, map_zero, zero_smul, Finset.sum_const_zero]
    exact H.zero_mem
  add_mem' := by
    intro μ ν hμ hν
    show (∑ j, σ ((μ + ν) j) • p j) ∈ H
    simp only [Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]
    exact H.add_mem hμ hν
  smul_mem' := by
    intro c μ hμ
    show (∑ j, σ ((c • μ) j) • p j) ∈ H
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, ← Finset.smul_sum]
    exact H.smul_mem _ hμ

theorem mem_coeffPreimage_iff (σ : k₀ →+* K) {n : ℕ} (p : Fin n → M) (H : Submodule K M)
    (μ : Fin n → k₀) : μ ∈ coeffPreimage σ p H ↔ (∑ j, σ (μ j) • p j) ∈ H :=
  Iff.rfl

theorem exists_forall_sum_smul_notMem [Infinite k₀] (σ : k₀ →+* K) {n : ℕ} (p : Fin n → M)
    {ι : Type*} [Finite ι] (H : ι → Submodule K M)
    (hH : ∀ i, ¬ (Submodule.span K (Set.range p) ≤ H i)) :
    ∃ μ : Fin n → k₀, ∀ i, (∑ j, σ (μ j) • p j) ∉ H i := by
  classical
  have hne : ∀ i, coeffPreimage σ p (H i) ≠ ⊤ := by
    intro i htop
    apply hH i
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have hj : (Pi.single j (1 : k₀) : Fin n → k₀) ∈ coeffPreimage σ p (H i) := by
      rw [htop]; exact Submodule.mem_top
    have hsum : (∑ l, σ ((Pi.single j (1 : k₀) : Fin n → k₀) l) • p l) = p j := by
      rw [Finset.sum_eq_single j]
      · rw [Pi.single_eq_same, map_one, one_smul]
      · intro l _ hl
        rw [Pi.single_eq_of_ne hl, map_zero, zero_smul]
      · intro h
        exact absurd (Finset.mem_univ j) h
    have hj' : (∑ l, σ ((Pi.single j (1 : k₀) : Fin n → k₀) l) • p l) ∈ H i := hj
    rw [hsum] at hj'
    exact hj'
  obtain ⟨μ, hμ⟩ :=
    Submodule.exists_forall_notMem_of_forall_ne_top (fun i => coeffPreimage σ p (H i)) hne
  exact ⟨μ, fun i h => hμ i h⟩

end Avoid

section Closed

variable [IsAlgClosed K] [IsCurveOver K F]

theorem surjective_algebraMap_residueField (v : Place K F) :
    Function.Surjective (algebraMap K v.ResidueField) := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2

end Closed

end AlgebraicCurve.EvalCount

namespace FltWs21
namespace RealN

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_mem_riemannRochSpace_residue_eq_of_isGoodDiv.AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization"

section NodePairs

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def nodeCompatiblePairs (E₁ E₂ : Divisor K F) {ι : Type*} (v₁ v₂ : ι → Place K F) :
    Submodule K (F × F) where
  carrier := {p | p.1 ∈ riemannRochSpace E₁ ∧ p.2 ∈ riemannRochSpace E₂ ∧
    ∀ i, ∃ c : K, (v₁ i).HasValue p.1 c ∧ (v₂ i).HasValue p.2 c}
  zero_mem' := ⟨Submodule.zero_mem _, Submodule.zero_mem _,
    fun i => ⟨0, EvalCount.hasValue_zero _, EvalCount.hasValue_zero _⟩⟩
  add_mem' := by
    rintro p p' ⟨hp1, hp2, hp⟩ ⟨hq1, hq2, hq⟩
    refine ⟨Submodule.add_mem _ hp1 hq1, Submodule.add_mem _ hp2 hq2, fun i => ?_⟩
    obtain ⟨c, hc1, hc2⟩ := hp i
    obtain ⟨d, hd1, hd2⟩ := hq i
    exact ⟨c + d, EvalCount.hvAdd hc1 hd1, EvalCount.hvAdd hc2 hd2⟩
  smul_mem' := by
    rintro a p ⟨hp1, hp2, hp⟩
    refine ⟨Submodule.smul_mem _ a hp1, Submodule.smul_mem _ a hp2, fun i => ?_⟩
    obtain ⟨c, hc1, hc2⟩ := hp i
    exact ⟨a * c, EvalCount.hvSmul a hc1, EvalCount.hvSmul a hc2⟩

theorem mem_nodeCompatiblePairs_iff {E₁ E₂ : Divisor K F} {ι : Type*} {v₁ v₂ : ι → Place K F}
    {p : F × F} :
    p ∈ nodeCompatiblePairs E₁ E₂ v₁ v₂ ↔ p.1 ∈ riemannRochSpace E₁ ∧ p.2 ∈ riemannRochSpace E₂ ∧
      ∀ i, ∃ c : K, (v₁ i).HasValue p.1 c ∧ (v₂ i).HasValue p.2 c :=
  Iff.rfl

end NodePairs

section Descent

variable {k₀ k : Type*} [Field k₀] [Field k] (σ : k₀ →+* k)
    (F₀ : IntermediateField k₀ (LaurentSeries k₀)) (F : IntermediateField k (LaurentSeries k))
    (ι : F₀ →+* F) (hι : ∀ x : F₀, ((ι x : F) : LaurentSeries k) = coeffMap σ (x : LaurentSeries k₀))

include hι in

theorem map_algebraMap_eq (c : k₀) : ι (algebraMap k₀ F₀ c) = algebraMap k F (σ c) := by
  apply Subtype.ext
  rw [hι]
  change coeffMap σ (algebraMap k₀ (LaurentSeries k₀) c) = algebraMap k (LaurentSeries k) (σ c)
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

include hι in

theorem linearIndependent_of_map_prod {n : ℕ} (r : Fin n → F₀ × F₀)
    (h : LinearIndependent k (fun j => ((ι (r j).1 : F), (ι (r j).2 : F)))) :
    LinearIndependent k₀ r := by
  classical
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro c hc j
  have h1 : (∑ i, c i • (r i).1) = 0 := by
    have := congrArg Prod.fst hc
    rwa [Prod.fst_sum, Prod.fst_zero] at this
  have h2 : (∑ i, c i • (r i).2) = 0 := by
    have := congrArg Prod.snd hc
    rwa [Prod.snd_sum, Prod.snd_zero] at this
  have key : ∑ i, σ (c i) • ((ι (r i).1 : F), (ι (r i).2 : F)) = 0 := by
    have e1 : (∑ i, σ (c i) • (ι (r i).1 : F)) = 0 := by
      have := congrArg ι h1
      rw [map_sum, map_zero] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_algebraMap_eq σ F₀ F ι hι]
    have e2 : (∑ i, σ (c i) • (ι (r i).2 : F)) = 0 := by
      have := congrArg ι h2
      rw [map_sum, map_zero] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_algebraMap_eq σ F₀ F ι hι]
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum, Prod.fst_zero]; simpa only [Prod.smul_fst] using e1
    · rw [Prod.snd_sum, Prod.snd_zero]; simpa only [Prod.smul_snd] using e2
  have := h (fun i => σ (c i)) key j
  exact (map_eq_zero_iff σ σ.injective).mp this

include hι in
theorem mem_span_of_map_mem
    {n : ℕ} (r : Fin n → F₀ × F₀) (hr : LinearIndependent k₀ r)
    (T : Submodule k (F × F)) [FiniteDimensional k T]
    (hT : ∀ j, ((ι (r j).1 : F), (ι (r j).2 : F)) ∈ T) (hTn : Module.finrank k T ≤ n)
    (g : F₀ × F₀) (hg : ((ι g.1 : F), (ι g.2 : F)) ∈ T) :
    g ∈ Submodule.span k₀ (Set.range r) := by
  let φ : F₀ × F₀ → F × F := fun y => ((ι y.1 : F), (ι y.2 : F))
  have hpli : LinearIndependent k (φ ∘ r) := linearIndependent_map_prod_of_coe_eq_coeffMap σ F₀ F ι hι hr
  have hspan : Submodule.span k (Set.range (φ ∘ r)) = T := by
    refine Submodule.eq_of_le_of_finrank_le (Submodule.span_le.mpr ?_) ?_
    · rintro _ ⟨j, rfl⟩
      exact hT j
    · rw [finrank_span_eq_card hpli, Fintype.card_fin]
      exact hTn
  by_contra hnot
  have hli' : LinearIndependent k₀ (Fin.cons g r) := by
    first
      | exact linearIndependent_finCons.mpr ⟨hr, hnot⟩
      | exact linearIndependent_fin_cons.mpr ⟨hr, hnot⟩
  have himg : LinearIndependent k (φ ∘ Fin.cons g r) :=
    linearIndependent_map_prod_of_coe_eq_coeffMap σ F₀ F ι hι hli'
  rw [Fin.comp_cons] at himg
  first
    | (rw [linearIndependent_finCons, hspan] at himg; exact himg.2 hg)
    | (rw [linearIndependent_fin_cons, hspan] at himg; exact himg.2 hg)

end Descent

section Degrees

variable {K F K' F' : Type*} [Field K] [Field F] [Algebra K F] [Field K'] [Field F'] [Algebra K' F']

theorem degree_mapDomain_of_deg_eq_one (r : Place K F → Place K' F')
    (h1 : ∀ w : Place K F, w.deg = 1) (h1' : ∀ v : Place K' F', v.deg = 1) (D : Divisor K F) :
    Divisor.degree (Finsupp.mapDomain r D) = Divisor.degree D := by
  classical
  simp only [Divisor.degree, Finsupp.liftAddHom_apply]
  rw [Finsupp.sum_mapDomain_index]
  · refine Finsupp.sum_congr fun w _ => ?_
    show D w * ((r w).deg : ℤ) = D w * (w.deg : ℤ)
    rw [h1, h1']
  · intro v; exact zero_mul _
  · intro v m n; exact add_mul _ _ _

theorem degree_nonneg_of_deg_eq_one (h1 : ∀ w : Place K F, w.deg = 1) {D : Divisor K F} (hD : ∀ w, 0 ≤ D w) :
    0 ≤ Divisor.degree D := by
  simp only [Divisor.degree, Finsupp.liftAddHom_apply]
  refine Finset.sum_nonneg fun w _ => ?_
  show 0 ≤ D w * (w.deg : ℤ)
  rw [h1]; simpa using hD w

end Degrees

end FltWs21.RealN

namespace FltWs21
namespace RealN
p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_mem_riemannRochSpace_residue_eq_of_isGoodDiv.AlgebraicCurve"

theorem finsuppDegree_eq_divisorDegree {K F : Type*} [Field K] [Field F] [Algebra K F]
    (h1 : ∀ w : Place K F, w.deg = 1) (E : Divisor K F) : Finsupp.degree E = Divisor.degree E := by
  classical
  simp only [Finsupp.degree, Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  show E w = E w * (w.deg : ℤ)
  rw [h1]; simp
end FltWs21.RealN

namespace FltWs21
namespace RealN

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_mem_riemannRochSpace_residue_eq_of_isGoodDiv.AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

theorem mapDomain_reduceFst_fstDiv_eq_zero (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    {v : Place k ↥(modularFunctionFieldC k N)}
    (hv : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v) :
    Finsupp.mapDomain P.reduceFst (P.fstDiv D) v = 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  refine Finset.sum_eq_zero fun W hW => ?_
  rw [Finsupp.single_apply, if_neg]
  intro hWv
  have hW' : W ∈ (P.fstDiv D).support := hW
  unfold PlaceSpecialization.fstDiv at hW'
  rw [Finsupp.support_filter, Finset.mem_filter] at hW'
  have h1 : P.IsStrictFst W := hW'.2
  exact h1.2 (hWv ▸ hv)

theorem mapDomain_reduceSnd_sndDiv_eq_zero (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    {v : Place k ↥(modularFunctionFieldC k N)}
    (hv : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v) :
    Finsupp.mapDomain P.reduceSnd (P.sndDiv D) v = 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  refine Finset.sum_eq_zero fun W hW => ?_
  rw [Finsupp.single_apply, if_neg]
  intro hWv
  have hW' : W ∈ (P.sndDiv D).support := hW
  unfold PlaceSpecialization.sndDiv at hW'
  rw [Finsupp.support_filter, Finset.mem_filter] at hW'
  have h1 : P.IsStrictSnd W := hW'.2
  exact h1.2 (hWv ▸ hv)

theorem fstDiv_add_sndDiv (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hgood : P.IsGoodDiv D) :
    P.fstDiv D + P.sndDiv D = D := by
  classical
  ext W
  unfold PlaceSpecialization.fstDiv PlaceSpecialization.sndDiv
  rw [Finsupp.add_apply, Finsupp.filter_apply, Finsupp.filter_apply]
  by_cases h1 : P.IsStrictFst W
  · by_cases h2 : P.IsStrictSnd W
    · exfalso
      apply h1.2
      have e1 : frobOnPlacesGeomLevel k N data hKr (P.reduceFst W) = P.reduceSnd W := h1.1
      have e2 : P.reduceFst W = frobOnPlacesGeomLevel k N data hKr (P.reduceSnd W) := h2.1
      conv_rhs => rw [e2]
      rw [e1]
    · rw [if_pos h1, if_neg h2, add_zero]
  · by_cases h2 : P.IsStrictSnd W
    · rw [if_neg h1, if_pos h2, zero_add]
    · rw [if_neg h1, if_neg h2, add_zero]
      by_contra h
      rcases hgood W (Finsupp.mem_support_iff.mpr (Ne.symm h)) with h' | h'
      · exact h1 h'
      · exact h2 h'

set_option maxHeartbeats 6400000 in

theorem count (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    (W : Finset (Place k ↥(modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hD : 0 ≤ D) (hgood : P.IsGoodDiv D)
    (hdeg₁ : 2 * (genusFF k ↥(modularFunctionFieldC k N) : ℤ) - 1 + W.card ≤
      Divisor.degree (Finsupp.mapDomain P.reduceFst (P.fstDiv D)))
    (hdeg₂ : 2 * (genusFF k ↥(modularFunctionFieldC k N) : ℤ) - 1 ≤
      Divisor.degree (Finsupp.mapDomain P.reduceSnd (P.sndDiv D))) :
    FiniteDimensional k ↥(nodeCompatiblePairs (Finsupp.mapDomain P.reduceFst (P.fstDiv D))
        (Finsupp.mapDomain P.reduceSnd (P.sndDiv D))
        (fun w : ↥W => (w : Place k ↥(modularFunctionFieldC k N))) (fun w : ↥W => arithFrobC q k N • (w : Place k ↥(modularFunctionFieldC k N)))) ∧
      Module.finrank k ↥(nodeCompatiblePairs (Finsupp.mapDomain P.reduceFst (P.fstDiv D))
        (Finsupp.mapDomain P.reduceSnd (P.sndDiv D))
        (fun w : ↥W => (w : Place k ↥(modularFunctionFieldC k N))) (fun w : ↥W => arithFrobC q k N • (w : Place k ↥(modularFunctionFieldC k N))))
        ≤ Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace D) ∧
      FiniteDimensional (AlgebraicClosure ℚ) ↥(riemannRochSpace D) := by
  classical
  haveI : IsCurveOver k ↥(modularFunctionFieldC k N) := isCurveOver_modularFunctionFieldC_of_perfectField k N
  set E₁ := Finsupp.mapDomain P.reduceFst (P.fstDiv D) with hE₁
  set E₂ := Finsupp.mapDomain P.reduceSnd (P.sndDiv D) with hE₂
  set T := nodeCompatiblePairs E₁ E₂ (fun w : ↥W => (w : Place k ↥(modularFunctionFieldC k N)))
    (fun w : ↥W => arithFrobC q k N • (w : Place k ↥(modularFunctionFieldC k N))) with hT

  have hgen : (genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) : ℤ) + 1 = 2 * (genusFF k ↥(modularFunctionFieldC k N) : ℤ) + W.card := by
    exact_mod_cast genusFF_modularFunctionFieldBar_mul_add_one_eq_of_ssPlaces q N hqN k W hW
  have hRR : ∀ Dk : Divisor k ↥(modularFunctionFieldC k N), 2 * (genusFF k ↥(modularFunctionFieldC k N) : ℤ) - 1 ≤ Dk.degree →
      (Module.finrank k ↥(riemannRochSpace Dk) : ℤ) = Dk.degree + 1 - (genusFF k ↥(modularFunctionFieldC k N) : ℤ) := by
    have h := ell_eq_degree_add_one_sub_genusFF_modularFunctionFieldFullC k N
    rw [← modularFunctionFieldC_eq_modularFunctionFieldFullC k q N hqN] at h
    exact h
  have hRI := degree_add_one_sub_genusFF_le_finrank_riemannRochSpace (N * q) D
  have hdegBar : ∀ w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), w.deg = 1 := deg_eq_one_modularFunctionFieldBar (N * q)
  have hdegC : ∀ v : Place k ↥(modularFunctionFieldC k N), v.deg = 1 := deg_eq_one_modularFunctionFieldC k N
  have hd₁ : Divisor.degree E₁ = Divisor.degree (P.fstDiv D) := degree_mapDomain_of_deg_eq_one _ hdegBar hdegC _
  have hd₂ : Divisor.degree E₂ = Divisor.degree (P.sndDiv D) := degree_mapDomain_of_deg_eq_one _ hdegBar hdegC _
  have hsum : Divisor.degree (P.fstDiv D) + Divisor.degree (P.sndDiv D) = Divisor.degree D := by
    rw [← map_add, fstDiv_add_sndDiv P D hgood]

  set n : ℕ := W.card with hn
  have hcard : Fintype.card ↥W = n := Fintype.card_coe W
  have hfixW : ∀ w : ↥W, frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (w : Place k ↥(modularFunctionFieldC k N))) = w :=
    fun w => frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed k N hqN data hKr _ ((hW _).mp w.2)
  have hfixW' : ∀ w : ↥W, frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr
      (arithFrobC q k N • (w : Place k ↥(modularFunctionFieldC k N)))) = arithFrobC q k N • (w : Place k ↥(modularFunctionFieldC k N)) :=
    fun w => frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed k N hqN data hKr _
      (arithFrobC_smul_mem_ssPlaces_univ q N k _ ((hW _).mp w.2))
  have hE₁0 : ∀ w : ↥W, E₁ (w : Place k ↥(modularFunctionFieldC k N)) = 0 := fun w => mapDomain_reduceFst_fstDiv_eq_zero P D (hfixW w)
  have hE₂0 : ∀ w : ↥W, E₂ (arithFrobC q k N • (w : Place k ↥(modularFunctionFieldC k N))) = 0 :=
    fun w => mapDomain_reduceSnd_sndDiv_eq_zero P D (hfixW' w)
  have ht₁ : ∀ w : ↥W, (1 : ↥(modularFunctionFieldC k N)) ≠ 0 ∧ (w : Place k ↥(modularFunctionFieldC k N)).ord (1 : ↥(modularFunctionFieldC k N)) = E₁ (w : Place k ↥(modularFunctionFieldC k N)) :=
    fun w => ⟨one_ne_zero, by rw [hE₁0]; exact (Place.hasValue_one _).ord_eq_zero one_ne_zero⟩
  have ht₂ : ∀ w : ↥W, (1 : ↥(modularFunctionFieldC k N)) ≠ 0 ∧
      (arithFrobC q k N • (w : Place k ↥(modularFunctionFieldC k N))).ord (1 : ↥(modularFunctionFieldC k N)) = E₂ (arithFrobC q k N • (w : Place k ↥(modularFunctionFieldC k N))) :=
    fun w => ⟨one_ne_zero, by rw [hE₂0]; exact (Place.hasValue_one _).ord_eq_zero one_ne_zero⟩

  have hfr₁ := hRR E₁ (by omega)
  have hfr₂ := hRR E₂ (by omega)
  have hD₂nn : ∀ V, 0 ≤ P.sndDiv D V := fun V => by
    unfold PlaceSpecialization.sndDiv; rw [Finsupp.filter_apply]; split_ifs
    · exact hD V
    · exact le_rfl
  have hd₂nn : 0 ≤ Divisor.degree (P.sndDiv D) := degree_nonneg_of_deg_eq_one hdegBar hD₂nn
  haveI hfin₁ : FiniteDimensional k ↥(riemannRochSpace E₁) := Module.finite_of_finrank_pos (by omega)
  haveI hfin₂ : FiniteDimensional k ↥(riemannRochSpace E₂) := Module.finite_of_finrank_pos (by omega)
  have hfin_of_le : ∀ Dk : Divisor k ↥(modularFunctionFieldC k N), Dk ≤ E₁ → FiniteDimensional k ↥(riemannRochSpace Dk) :=
    fun Dk hDk => Module.Finite.of_injective (Submodule.inclusion (AlgebraicCurve.EvalCount.riemannRochSpace_mono hDk))
      (Submodule.inclusion_injective _)
  have hdegsum : ∀ (s : Finset ↥W), Divisor.degree (∑ j ∈ s, Finsupp.single ((j : ↥W) : Place k ↥(modularFunctionFieldC k N)) (1 : ℤ)) = s.card := by
    intro s
    rw [map_sum]
    simp only [Divisor.degree_single, hdegC, Nat.cast_one, mul_one, Finset.sum_const, nsmul_eq_mul]
  have hSnonneg : ∀ s : Finset ↥W, (0 : Divisor k ↥(modularFunctionFieldC k N)) ≤ ∑ j ∈ s, Finsupp.single ((j : ↥W) : Place k ↥(modularFunctionFieldC k N)) (1 : ℤ) :=
    fun s => Finset.sum_nonneg fun j _ => Finsupp.single_nonneg.mpr zero_le_one

  have hstep : ∀ i : ↥W,
      ∃ g ∈ riemannRochSpace (E₁ - ∑ j ∈ Finset.univ.erase i, Finsupp.single ((j : ↥W) : Place k ↥(modularFunctionFieldC k N)) 1),
        g ∉ riemannRochSpace (E₁ - ∑ j : ↥W, Finsupp.single ((j : ↥W) : Place k ↥(modularFunctionFieldC k N)) 1) := by
    intro i
    have hn1 : 1 ≤ n := by
      rw [← hcard]; exact Fintype.card_pos_iff.mpr ⟨i⟩
    have hda : Divisor.degree (E₁ - ∑ j ∈ Finset.univ.erase i, Finsupp.single ((j : ↥W) : Place k ↥(modularFunctionFieldC k N)) (1 : ℤ))
        = Divisor.degree E₁ - (n - 1 : ℕ) := by
      rw [map_sub, hdegsum, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, hcard]
    have hdb : Divisor.degree (E₁ - ∑ j : ↥W, Finsupp.single ((j : ↥W) : Place k ↥(modularFunctionFieldC k N)) (1 : ℤ)) = Divisor.degree E₁ - n := by
      rw [map_sub, hdegsum, Finset.card_univ, hcard]
    have hra := hRR _ (by rw [hda]; push_cast; omega)
    have hrb := hRR _ (by rw [hdb]; omega)
    haveI : FiniteDimensional k ↥(riemannRochSpace (E₁ - ∑ j : ↥W, Finsupp.single ((j : ↥W) : Place k ↥(modularFunctionFieldC k N)) (1 : ℤ))) :=
      hfin_of_le _ (sub_le_self _ (hSnonneg _))
    apply AlgebraicCurve.EvalCount.exists_mem_riemannRochSpace_not_mem_of_finrank_lt
    have : (Module.finrank k ↥(riemannRochSpace (E₁ - ∑ j : ↥W, Finsupp.single ((j : ↥W) : Place k ↥(modularFunctionFieldC k N)) (1 : ℤ))) : ℤ)
        < Module.finrank k ↥(riemannRochSpace (E₁ - ∑ j ∈ Finset.univ.erase i, Finsupp.single ((j : ↥W) : Place k ↥(modularFunctionFieldC k N)) (1 : ℤ))) := by
      rw [hra, hrb, hda, hdb]; push_cast; omega
    exact_mod_cast this

  have hsurj0 := AlgebraicCurve.exists_mem_riemannRochSpace_forall_hasValue_mul_of_exists_not_mem
    E₁ (fun w : ↥W => (w : Place k ↥(modularFunctionFieldC k N))) Subtype.val_injective (fun _ => (1 : ↥(modularFunctionFieldC k N))) ht₁ hstep
  obtain ⟨hfinT, hcount⟩ :=
    AlgebraicCurve.finrank_add_card_le_of_forall_exists_mem_riemannRochSpace_hasValue_mul
      E₁ E₂ (fun w : ↥W => (w : Place k ↥(modularFunctionFieldC k N))) (fun w : ↥W => arithFrobC q k N • (w : Place k ↥(modularFunctionFieldC k N)))
      (fun _ => (1 : ↥(modularFunctionFieldC k N))) (fun _ => (1 : ↥(modularFunctionFieldC k N))) ht₁ ht₂ (fun _ => (1 : k)) hsurj0 T
      (fun p => by
        rw [hT, mem_nodeCompatiblePairs_iff]
        simp only [one_mul])
  rw [hcard] at hcount

  have hfinD : FiniteDimensional (AlgebraicClosure ℚ) ↥(riemannRochSpace D) := Module.finite_of_finrank_pos (by omega)
  refine ⟨hfinT, ?_, hfinD⟩
  have hc : (Module.finrank k ↥T : ℤ) + n ≤ (Module.finrank k ↥(riemannRochSpace E₁) : ℤ) + Module.finrank k ↥(riemannRochSpace E₂) := by
    exact_mod_cast hcount
  have : (Module.finrank k ↥T : ℤ) ≤ Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace D) := by
    rw [hfr₁, hfr₂] at hc
    omega
  exact_mod_cast this

end FltWs21.RealN

namespace FltWs21
namespace RealN

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_mem_riemannRochSpace_residue_eq_of_isGoodDiv.AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

set_option maxHeartbeats 6400000 in
theorem main {P : PlaceSpecialization A q N data hKr k red hα hβ} (hqN : ¬ q ∣ N)
    {W : Finset (Place k ↥(modularFunctionFieldC k N))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hD : 0 ≤ D) (hgood : P.IsGoodDiv D)
    (hdeg₁ : 2 * (genusFF k ↥(modularFunctionFieldC k N) : ℤ) - 1 + W.card ≤
      Divisor.degree (Finsupp.mapDomain P.reduceFst (P.fstDiv D)))
    (hdeg₂ : 2 * (genusFF k ↥(modularFunctionFieldC k N) : ℤ) - 1 ≤
      Divisor.degree (Finsupp.mapDomain P.reduceSnd (P.sndDiv D)))
    (g₁ g₂ : ↥(modularFunctionFieldFullC (ResidueField A) N))
    (hg₁ : (R.ι g₁ : ↥(modularFunctionFieldC k N)) ∈
      riemannRochSpace (Finsupp.mapDomain P.reduceFst (P.fstDiv D)))
    (hg₂ : (R.ι g₂ : ↥(modularFunctionFieldC k N)) ∈
      riemannRochSpace (Finsupp.mapDomain P.reduceSnd (P.sndDiv D)))
    (hnode : ∀ s ∈ nodePairsOfPlaces (arithFrobC q k N) W, ∃ c : k,
      s.1.HasValue (R.ι g₁ : ↥(modularFunctionFieldC k N)) c ∧
      s.2.HasValue (R.ι g₂ : ↥(modularFunctionFieldC k N)) c) :
    ∃ (G : ↥(modularFunctionFieldBar (N * q))) (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers),
      G ∈ riemannRochSpace D ∧ R.R₁.residue ⟨G, h₁⟩ = g₁ ∧ R.R₂.residue ⟨G, h₂⟩ = g₂ := by
  classical

  obtain ⟨hfinT, hTn, hfd⟩ := count P hqN W hW D hD hgood hdeg₁ hdeg₂
  haveI := hfd

  obtain ⟨Gf, hG₁, hG₂, hGV, hGli⟩ := R.exists_linearIndependent_residuePair_of_riemannRochSpace hqN D

  set r := fun j => (R.R₁.residue ⟨Gf j, hG₁ j⟩, R.R₂.residue ⟨Gf j, hG₂ j⟩) with hr
  set φ : ↥(modularFunctionFieldFullC (ResidueField A) N) × ↥(modularFunctionFieldFullC (ResidueField A) N) →
      ↥(modularFunctionFieldC k N) × ↥(modularFunctionFieldC k N) := fun y => ((R.ι y.1 : ↥(modularFunctionFieldC k N)), (R.ι y.2 : ↥(modularFunctionFieldC k N))) with hφ
  have hGli' : LinearIndependent k (fun j => ((R.ι (r j).1 : ↥(modularFunctionFieldC k N)), (R.ι (r j).2 : ↥(modularFunctionFieldC k N)))) := hGli
  have hrli : LinearIndependent (ResidueField A) r :=
    linearIndependent_of_map_prod R.redBar _ _ R.ι R.ι_coe r hGli'

  set T : Submodule k (↥(modularFunctionFieldC k N) × ↥(modularFunctionFieldC k N)) :=
    nodeCompatiblePairs (Finsupp.mapDomain P.reduceFst (P.fstDiv D)) (Finsupp.mapDomain P.reduceSnd (P.sndDiv D))
      (fun w : ↥W => (w : Place k ↥(modularFunctionFieldC k N))) (fun w : ↥W => arithFrobC q k N • (w : Place k ↥(modularFunctionFieldC k N))) with hT
  have hpT : ∀ j, ((R.ι (r j).1 : ↥(modularFunctionFieldC k N)), (R.ι (r j).2 : ↥(modularFunctionFieldC k N))) ∈ T := fun j => by
    obtain ⟨h1, h2, h3⟩ :=
      ProlongationTuple.IsModel.residue_mem_riemannRochSpace_mapDomain_and_hasValue_of_isGoodDiv hqN hW R hR hRL hNV hO
        D hD hgood (Gf j) (hGV j) (hG₁ j) (hG₂ j)
    exact ⟨h1, h2, fun w => h3 w w.2⟩
  have hgT : φ (g₁, g₂) ∈ T := by
    refine ⟨hg₁, hg₂, fun w => ?_⟩
    exact hnode (smulNodePair (arithFrobC q k N) (w : Place k ↥(modularFunctionFieldC k N)))
      (smulNodePair_mem_nodePairsOfPlaces _ w.2)

  haveI := hfinT
  have hgspan : (g₁, g₂) ∈ Submodule.span (ResidueField A) (Set.range r) :=
    mem_span_of_map_mem R.redBar _ _ R.ι R.ι_coe r hrli T hpT hTn (g₁, g₂) hgT
  obtain ⟨μ, hμ⟩ := (Submodule.mem_span_range_iff_exists_fun (ResidueField A)).mp hgspan

  choose α hα using fun j => IsLocalRing.residue_surjective (μ j)
  have hcmem₁ : ∀ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (α j : AlgebraicClosure ℚ) ∈ R.R₁.integers :=
    fun j => (R.R₁.algebraMap_mem_iff _).mpr (α j).2
  have hcmem₂ : ∀ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (α j : AlgebraicClosure ℚ) ∈ R.R₂.integers :=
    fun j => (R.R₂.algebraMap_mem_iff _).mpr (α j).2
  set cs₁ : _ → R.R₁.integers := fun j => ⟨_, hcmem₁ j⟩ with hcs₁
  set Gs₁ : _ → R.R₁.integers := fun j => ⟨Gf j, hG₁ j⟩ with hGs₁
  set cs₂ : _ → R.R₂.integers := fun j => ⟨_, hcmem₂ j⟩ with hcs₂
  set Gs₂ : _ → R.R₂.integers := fun j => ⟨Gf j, hG₂ j⟩ with hGs₂
  set x₁ : R.R₁.integers := ∑ j, cs₁ j * Gs₁ j with hx₁
  set x₂ : R.R₂.integers := ∑ j, cs₂ j * Gs₂ j with hx₂
  set G : ↥(modularFunctionFieldBar (N * q)) :=
    ∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (α j : AlgebraicClosure ℚ) * Gf j with hGdef
  have hsum₁ : (x₁ : ↥(modularFunctionFieldBar (N * q))) = G := by
    have e : ((∑ j, cs₁ j * Gs₁ j : R.R₁.integers) : ↥(modularFunctionFieldBar (N * q)))
        = ∑ j, ((cs₁ j * Gs₁ j : R.R₁.integers) : ↥(modularFunctionFieldBar (N * q))) := by
      first
        | exact AddSubmonoidClass.coe_finsetSum _ _
        | exact AddSubmonoidClass.coe_finset_sum _ _
    rw [hx₁, e, hGdef]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MulMemClass.coe_mul]
  have hsum₂ : (x₂ : ↥(modularFunctionFieldBar (N * q))) = G := by
    have e : ((∑ j, cs₂ j * Gs₂ j : R.R₂.integers) : ↥(modularFunctionFieldBar (N * q)))
        = ∑ j, ((cs₂ j * Gs₂ j : R.R₂.integers) : ↥(modularFunctionFieldBar (N * q))) := by
      first
        | exact AddSubmonoidClass.coe_finsetSum _ _
        | exact AddSubmonoidClass.coe_finset_sum _ _
    rw [hx₂, e, hGdef]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MulMemClass.coe_mul]
  have hterm₁ : ∀ j, R.R₁.residue (cs₁ j * Gs₁ j) = μ j • (r j).1 := by
    intro j
    have hc : R.R₁.residue (cs₁ j) = algebraMap (ResidueField A) _ (μ j) := by
      rw [← hα j]
      exact R.R₁.residue_algebraMap (α j)
    rw [map_mul, Algebra.smul_def]
    exact congrArg (· * _) hc
  have hterm₂ : ∀ j, R.R₂.residue (cs₂ j * Gs₂ j) = μ j • (r j).2 := by
    intro j
    have hc : R.R₂.residue (cs₂ j) = algebraMap (ResidueField A) _ (μ j) := by
      rw [← hα j]
      exact R.R₂.residue_algebraMap (α j)
    rw [map_mul, Algebra.smul_def]
    exact congrArg (· * _) hc
  have h₁ : G ∈ R.R₁.integers := by
    rw [← hsum₁]
    exact x₁.2
  have h₂ : G ∈ R.R₂.integers := by
    rw [← hsum₂]
    exact x₂.2
  have hGx₁ : (⟨G, h₁⟩ : R.R₁.integers) = x₁ := Subtype.ext hsum₁.symm
  have hGx₂ : (⟨G, h₂⟩ : R.R₂.integers) = x₂ := Subtype.ext hsum₂.symm
  refine ⟨G, h₁, h₂, ?_, ?_, ?_⟩
  · rw [hGdef]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (hGV j)
  · rw [hGx₁, hx₁, map_sum, Finset.sum_congr rfl fun j _ => hterm₁ j]
    have h1 := congrArg Prod.fst hμ
    rw [Prod.fst_sum] at h1
    simpa only [Prod.smul_fst] using h1
  · rw [hGx₂, hx₂, map_sum, Finset.sum_congr rfl fun j _ => hterm₂ j]
    have h1 := congrArg Prod.snd hμ
    rw [Prod.snd_sum] at h1
    simpa only [Prod.smul_snd] using h1

end FltWs21.RealN

open _root_.AlgebraicCurve _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_mem_riemannRochSpace_residue_eq_of_isGoodDiv.AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (hqN : ¬ q ∣ N)
    {W : Finset (Place k ↥(modularFunctionFieldC k N))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hD : 0 ≤ D) (hgood : P.IsGoodDiv D)
    (hdeg₁ : 2 * (genusFF k ↥(modularFunctionFieldC k N) : ℤ) - 1 + W.card ≤
      (Finsupp.mapDomain P.reduceFst (P.fstDiv D)).degree)
    (hdeg₂ : 2 * (genusFF k ↥(modularFunctionFieldC k N) : ℤ) - 1 ≤
      (Finsupp.mapDomain P.reduceSnd (P.sndDiv D)).degree)
    (g₁ g₂ : ↥(modularFunctionFieldFullC (ResidueField A) N))
    (hg₁ : (R.ι g₁ : ↥(modularFunctionFieldC k N)) ∈
      riemannRochSpace (Finsupp.mapDomain P.reduceFst (P.fstDiv D)))
    (hg₂ : (R.ι g₂ : ↥(modularFunctionFieldC k N)) ∈
      riemannRochSpace (Finsupp.mapDomain P.reduceSnd (P.sndDiv D)))
    (hnode : ∀ s ∈ nodePairsOfPlaces (arithFrobC q k N) W, ∃ c : k,
      s.1.HasValue (R.ι g₁ : ↥(modularFunctionFieldC k N)) c ∧
      s.2.HasValue (R.ι g₂ : ↥(modularFunctionFieldC k N)) c) :
    ∃ (G : ↥(modularFunctionFieldBar (N * q))) (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers),
      G ∈ riemannRochSpace D ∧ R.R₁.residue ⟨G, h₁⟩ = g₁ ∧ R.R₂.residue ⟨G, h₂⟩ = g₂ := by
  haveI : IsCurveOver k ↥(modularFunctionFieldC k N) := isCurveOver_modularFunctionFieldC_of_perfectField k N
  have hdegC : ∀ v : Place k ↥(modularFunctionFieldC k N), v.deg = 1 := deg_eq_one_modularFunctionFieldC k N
  have hdeg₁' : 2 * (genusFF k ↥(modularFunctionFieldC k N) : ℤ) - 1 + W.card ≤
      Divisor.degree (Finsupp.mapDomain P.reduceFst (P.fstDiv D)) := by
    first
      | exact hdeg₁
      | (rw [← FltWs21.RealN.finsuppDegree_eq_divisorDegree hdegC]; exact hdeg₁)
  have hdeg₂' : 2 * (genusFF k ↥(modularFunctionFieldC k N) : ℤ) - 1 ≤
      Divisor.degree (Finsupp.mapDomain P.reduceSnd (P.sndDiv D)) := by
    first
      | exact hdeg₂
      | (rw [← FltWs21.RealN.finsuppDegree_eq_divisorDegree hdegC]; exact hdeg₂)
  exact FltWs21.RealN.main hqN hW R hR hRL hNV hO D hD hgood hdeg₁' hdeg₂' g₁ g₂ hg₁ hg₂ hnode

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_mem_riemannRochSpace_residue_eq_of_isGoodDiv
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_mem_riemannRochSpace_residue_eq_of_isGoodDiv (solution)
