-- Prove2me | solution 1 for ModularCurve.CharPModel.FibreModel.spPlace_eq_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/e1692a7f-7984-5a9a-a8fc-42ca1d90a2c6

import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_eq
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_d0_j
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_finChart_mem_nonunits_iff
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_eq_of_surjective
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine"
p2m_attr_erase "instance" "ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe"
p2m_attr_erase "simp" "AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero"
p2m_attr_erase "simp" "Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"
p2m_attr_erase "simp" "WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero"
p2m_attr_erase "simp" "TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

p2m_open "AlgebraicCurve ModularCurve~jBar~coeffMap_jqModC~coeffMap_jqNModC P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_eq_of_surjective.ModularCurve ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_eq_of_surjective.ModularCurve.CharPModel"

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqNModC modularFunctionFieldC jqModC_mem jqNModC_mem ModularPolynomialData modularFunctionFieldFull coeffMap coeffMap_single coeffMap_coeffMap coeffMap_id algebraMap_laurentSeries_eq_single laurentBaseChange CharPModel.FibreModel coeffSemilinearAut.coeffMap_jqModC coeffSemilinearAut.coeffMap_jqNModC coeffSemilinearAut CharPModel.FibreModel.spPlace_eq"
namespace CharPModel
p2m_export "ModularCurve.CharPModel" "jBar jNBar constantsHom FibreModel FibreModel.spPlace_eq FibreModel.spPlace_d0_j FibreModel.place_eq_of_forall_finChart_mem_nonunits_iff FibreModel.place_eq_of_forall_infChart_mem_nonunits_iff"
namespace SpPlaceBaseChange
p2m_open "ModularCurve.CharPModel ModularCurve~jBar~coeffMap_jqModC~coeffMap_jqNModC"

section FibreFieldCongr

variable {K S : Type*} [Field K] [Field S]

private theorem coeffMap_algebraMap' (f : K →+* S) (c : K) :
    coeffMap f (algebraMap K (LaurentSeries K) c)
      = algebraMap S (LaurentSeries S) (f c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

private theorem coeffMap_mem_mffC (f : K →+* S) (N : ℕ) [NeZero N] {x : LaurentSeries K}
    (hx : x ∈ modularFunctionFieldC K N) :
    coeffMap f x ∈ modularFunctionFieldC S N := by
  change x ∈ Subfield.closure (Set.range (algebraMap K (LaurentSeries K)) ∪
      {jqModC K, jqNModC K N}) at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | hy
      · rw [coeffMap_algebraMap']
        exact (modularFunctionFieldC S N).algebraMap_mem _
      · rcases hy with rfl | hy
        · rw [coeffSemilinearAut.coeffMap_jqModC]
          exact jqModC_mem S N
        · rw [Set.mem_singleton_iff] at hy
          subst hy
          rw [coeffSemilinearAut.coeffMap_jqNModC]
          exact jqNModC_mem S N
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

private def mffCCongr (e : K ≃+* S) (N : ℕ) [NeZero N] :
    modularFunctionFieldC K N ≃+* modularFunctionFieldC S N :=
  RingEquiv.ofRingHom
    (((coeffMap (e : K →+* S)).restrict _ _ (fun x hx => coeffMap_mem_mffC _ N hx) :
      modularFunctionFieldC K N →+* modularFunctionFieldC S N))
    (((coeffMap (e.symm : S →+* K)).restrict _ _ (fun x hx => coeffMap_mem_mffC _ N hx) :
      modularFunctionFieldC S N →+* modularFunctionFieldC K N))
    (RingHom.ext fun x => Subtype.ext (by
      show coeffMap (e : K →+* S) (coeffMap (e.symm : S →+* K) (x : LaurentSeries S))
        = (x : LaurentSeries S)
      rw [coeffMap_coeffMap,
        show (e : K →+* S).comp (e.symm : S →+* K) = RingHom.id S from
          RingHom.ext fun y => e.apply_symm_apply y]
      exact coeffMap_id _))
    (RingHom.ext fun x => Subtype.ext (by
      show coeffMap (e.symm : S →+* K) (coeffMap (e : K →+* S) (x : LaurentSeries K))
        = (x : LaurentSeries K)
      rw [coeffMap_coeffMap,
        show (e.symm : S →+* K).comp (e : K →+* S) = RingHom.id K from
          RingHom.ext fun y => e.symm_apply_apply y]
      exact coeffMap_id _))

private theorem coe_mffCCongr_apply (e : K ≃+* S) (N : ℕ) [NeZero N]
    (x : modularFunctionFieldC K N) :
    ((mffCCongr e N x : modularFunctionFieldC S N) : LaurentSeries S)
      = coeffMap (e : K →+* S) (x : LaurentSeries K) := rfl

private theorem mffCCongr_algebraMap (e : K ≃+* S) (N : ℕ) [NeZero N] (c : K) :
    mffCCongr e N (algebraMap K (modularFunctionFieldC K N) c)
      = algebraMap S (modularFunctionFieldC S N) (e c) :=
  Subtype.ext (coeffMap_algebraMap' (e : K →+* S) c)

private theorem mffCCongr_jLine (e : K ≃+* S) (N : ℕ) [NeZero N] :
    mffCCongr e N ⟨jqModC K, jqModC_mem K N⟩ = ⟨jqModC S, jqModC_mem S N⟩ :=
  Subtype.ext (by
    rw [coe_mffCCongr_apply]
    exact coeffSemilinearAut.coeffMap_jqModC (e : K →+* S))

private theorem mffCCongr_jNLine (e : K ≃+* S) (N : ℕ) [NeZero N] :
    mffCCongr e N ⟨jqNModC K N, jqNModC_mem K N⟩ = ⟨jqNModC S N, jqNModC_mem S N⟩ :=
  Subtype.ext (by
    rw [coe_mffCCongr_apply]
    exact coeffSemilinearAut.coeffMap_jqNModC (e : K →+* S) N)

end FibreFieldCongr

section OrdHelpers

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

private theorem mem_of_ord_pos' {f : F} (h : 0 < w.ord f) : f ∈ w.toValuationSubring := by
  have hf : f ≠ 0 := by rintro rfl; simp at h
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow hf hπ
  rw [hu, show w.ord f = (((w.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h.le).symm,
    zpow_natCast]
  exact mul_mem (u : w.toValuationSubring).2 (pow_mem (π : w.toValuationSubring).2 _)

private theorem mem_nonunits_iff_ord_pos' {f : F} (hf : f ≠ 0) :
    f ∈ w.toValuationSubring.nonunits ↔ 0 < w.ord f := by
  constructor
  · intro h
    have hmem : f ∈ w.toValuationSubring := w.toValuationSubring.nonunits_subset h
    have h' : ((⟨f, hmem⟩ : w.toValuationSubring) : F) ∈ w.toValuationSubring.nonunits := h
    rw [ValuationSubring.coe_mem_nonunits_iff] at h'
    exact (w.mem_maximalIdeal_iff_ord_pos hf hmem).mp h'
  · intro h
    have hmem : f ∈ w.toValuationSubring := mem_of_ord_pos' w h
    have h' := (w.mem_maximalIdeal_iff_ord_pos hf hmem).mpr h
    rw [← ValuationSubring.coe_mem_nonunits_iff] at h'
    exact h'

private theorem zero_mem_nonunits' : (0 : F) ∈ w.toValuationSubring.nonunits := by
  have h : ((0 : w.toValuationSubring) : F) ∈ w.toValuationSubring.nonunits := by
    rw [ValuationSubring.coe_mem_nonunits_iff]
    exact Ideal.zero_mem _
  exact h

private theorem mem_of_ord_sub_pos {x : F} {c : K}
    (h : 0 < w.ord (x - algebraMap K F c)) : x ∈ w.toValuationSubring := by
  have h1 : x - algebraMap K F c ∈ w.toValuationSubring := mem_of_ord_pos' w h
  have h2 : algebraMap K F c ∈ w.toValuationSubring := w.algebraMap_mem' c
  simpa using add_mem h1 h2

end OrdHelpers

section PlaceCongrHetero

variable {K S F F' : Type*} [Field K] [Field S] [Field F] [Field F']
  [Algebra K F] [Algebra S F']
variable (eK : K ≃+* S) (e : F ≃+* F')
variable (he : ∀ a : K, e (algebraMap K F a) = algebraMap S F' (eK a))

private def placeCongrHetero (v : Place K F) : Place S F' where
  toValuationSubring := v.toValuationSubring.comap (e.symm : F' →+* F)
  algebraMap_mem' a := by
    rw [ValuationSubring.mem_comap]
    show e.symm (algebraMap S F' a) ∈ v.toValuationSubring
    have hsq : e.symm (algebraMap S F' a) = algebraMap K F (eK.symm a) := by
      have h1 := he (eK.symm a)
      rw [eK.apply_symm_apply] at h1
      rw [← h1, e.symm_apply_apply]
    rw [hsq]
    exact v.algebraMap_mem' _
  ne_top' := fun h =>
    v.ne_top' (SetLike.ext fun x =>
      ⟨fun _ => ValuationSubring.mem_top x, fun _ => by
        have hx : e x ∈ v.toValuationSubring.comap (e.symm : F' →+* F) := by
          rw [h]
          exact ValuationSubring.mem_top _
        rw [ValuationSubring.mem_comap] at hx
        have hx2 : e.symm (e x) ∈ v.toValuationSubring := hx
        rwa [e.symm_apply_apply] at hx2⟩)
  isPrincipalIdealRing' :=
    IsPrincipalIdealRing.of_surjective
      (Place.comapSymmRingEquiv e v.toValuationSubring : _ ≃+* _)
      (Place.comapSymmRingEquiv e v.toValuationSubring).surjective

private theorem placeCongrHetero_toValuationSubring (v : Place K F) :
    (placeCongrHetero eK e he v).toValuationSubring
      = v.toValuationSubring.comap (e.symm : F' →+* F) := rfl

private theorem mem_placeCongrHetero_iff (v : Place K F) (x : F) :
    e x ∈ (placeCongrHetero eK e he v).toValuationSubring ↔ x ∈ v.toValuationSubring := by
  rw [placeCongrHetero_toValuationSubring, ValuationSubring.mem_comap]
  show e.symm (e x) ∈ v.toValuationSubring ↔ x ∈ v.toValuationSubring
  rw [e.symm_apply_apply]

private theorem ord_placeCongrHetero (v : Place K F) (f : F) :
    (placeCongrHetero eK e he v).ord (e f) = v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  have hπ' : Irreducible (Place.comapSymmRingEquiv e v.toValuationSubring π) :=
    (MulEquiv.irreducible_iff (Place.comapSymmRingEquiv e v.toValuationSubring)).mpr hπ
  have hu' : IsUnit (Place.comapSymmRingEquiv e v.toValuationSubring
      (u : v.toValuationSubring)) :=
    u.isUnit.map (Place.comapSymmRingEquiv e v.toValuationSubring)
  have key : e f
      = ((hu'.unit : (v.toValuationSubring.comap (e.symm : F' →+* F))) : F')
        * (((Place.comapSymmRingEquiv e v.toValuationSubring π :
            (v.toValuationSubring.comap (e.symm : F' →+* F))) : F') ^ (v.ord f)) := by
    rw [IsUnit.unit_spec, Place.coe_comapSymmRingEquiv_apply,
      Place.coe_comapSymmRingEquiv_apply, ← map_zpow₀, ← map_mul, ← hu]
  rw [key]
  exact (placeCongrHetero eK e he v).ord_unit_smul_zpow hu'.unit hπ' (v.ord f)

private theorem mem_nonunits_placeCongrHetero_iff (v : Place K F) (x : F) :
    e x ∈ (placeCongrHetero eK e he v).toValuationSubring.nonunits
      ↔ x ∈ v.toValuationSubring.nonunits := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero]
    exact ⟨fun _ => zero_mem_nonunits' v, fun _ => zero_mem_nonunits' _⟩
  rw [mem_nonunits_iff_ord_pos' (placeCongrHetero eK e he v) (by simpa using hx),
      mem_nonunits_iff_ord_pos' v hx, ord_placeCongrHetero eK e he v x]

include he in
private theorem placeCongrHetero_injective : Function.Injective (placeCongrHetero eK e he) := by
  intro v₁ v₂ h
  ext1
  refine SetLike.ext fun x => ?_
  have h1 := mem_placeCongrHetero_iff eK e he v₁ x
  have h2 := mem_placeCongrHetero_iff eK e he v₂ x
  rw [h] at h1
  exact h1.symm.trans h2

end PlaceCongrHetero

section ResidueToRed

variable {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] (red : A →+* k)

private theorem ker_red_eq (hred : Function.Surjective red) :
    RingHom.ker red = IsLocalRing.maximalIdeal A :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective red hred)

private def residueToRed (hred : Function.Surjective red) :
    IsLocalRing.ResidueField A ≃+* k :=
  (Ideal.quotEquivOfEq (ker_red_eq red hred).symm).trans
    (RingHom.quotientKerEquivOfSurjective hred)

private theorem residueToRed_residue (hred : Function.Surjective red) (x : A) :
    residueToRed red hred (IsLocalRing.residue A x) = red x := by
  show (RingHom.quotientKerEquivOfSurjective hred)
    ((Ideal.quotEquivOfEq (ker_red_eq red hred).symm) (Ideal.Quotient.mk _ x)) = red x
  rw [Ideal.quotEquivOfEq_mk]
  exact RingHom.kerLift_mk red x

end ResidueToRed

section SeparableCongr

variable {K S : Type*} [Field K] [Field S]

private theorem polyMap_nonZeroDivisors (e : K ≃+* S) :
    (nonZeroDivisors (Polynomial K)) ≤
      (nonZeroDivisors (Polynomial S)).comap (Polynomial.mapRingHom (e : K →+* S)) := by
  intro p hp
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
  rw [mem_nonZeroDivisors_iff_ne_zero] at hp
  exact (Polynomial.map_ne_zero_iff (e : K →+* S).injective).mpr hp

private def ratFuncMap (e : K ≃+* S) : RatFunc K →+* RatFunc S :=
  RatFunc.mapRingHom (Polynomial.mapRingHom (e : K →+* S)) (polyMap_nonZeroDivisors e)

private theorem ratFuncMap_algebraMap (e : K ≃+* S) (p : Polynomial K) :
    ratFuncMap e (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial S) (RatFunc S) (p.map (e : K →+* S)) := by
  show RatFunc.map (Polynomial.mapRingHom (e : K →+* S)) (polyMap_nonZeroDivisors e)
    (algebraMap (Polynomial K) (RatFunc K) p) = _
  rw [← div_one (algebraMap (Polynomial K) (RatFunc K) p),
    ← map_one (algebraMap (Polynomial K) (RatFunc K)), RatFunc.map_apply_div, map_one, map_one,
    div_one]
  rfl

private theorem intRoute_eq (e : K ≃+* S) :
    ((ratFuncMap e).comp (algebraMap (Polynomial K) (RatFunc K))).comp
        (Polynomial.mapRingHom (Int.castRingHom K))
      = (algebraMap (Polynomial S) (RatFunc S)).comp
          (Polynomial.mapRingHom (Int.castRingHom S)) := by
  apply Polynomial.ringHom_ext
  · intro n
    simp
  · simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X]
    rw [ratFuncMap_algebraMap, Polynomial.map_X]

private theorem separable_congr (e : K ≃+* S) (Φ : Polynomial (Polynomial ℤ))
    (h : ((Φ.map (Polynomial.mapRingHom (Int.castRingHom S))).map
      (algebraMap (Polynomial S) (RatFunc S))).Separable) :
    ((Φ.map (Polynomial.mapRingHom (Int.castRingHom K))).map
      (algebraMap (Polynomial K) (RatFunc K))).Separable := by
  rw [← Polynomial.separable_map (ratFuncMap e), Polynomial.map_map, Polynomial.map_map,
    intRoute_eq e]
  rw [Polynomial.map_map] at h
  exact h

end SeparableCongr

section ModelCongr

variable {N : ℕ} [NeZero N] {A : ValuationSubring (AlgebraicClosure ℚ)} {ℓ : ℕ} [Fact ℓ.Prime]
variable {k : Type*} [Field k] [CharP k ℓ] {red : A →+* k}
variable {k' : Type*} [Field k'] [CharP k' ℓ] {red' : A →+* k'}
variable (e : k ≃+* k') (he : ∀ a : A, e (red a) = red' a)

private abbrev fieldMap : modularFunctionFieldC k N ≃+* modularFunctionFieldC k' N :=
  mffCCongr e N

include he in
private theorem fieldMap_const (a : A) :
    fieldMap (N := N) e (algebraMap k (modularFunctionFieldC k N) (red a))
      = algebraMap k' (modularFunctionFieldC k' N) (red' a) := by
  rw [mffCCongr_algebraMap, he]

private theorem ker_comp_fieldMap {R : Type*} [CommRing R] (f : R →+* modularFunctionFieldC k N) :
    RingHom.ker ((fieldMap (N := N) e : modularFunctionFieldC k N →+* modularFunctionFieldC k' N).comp f)
      = RingHom.ker f := by
  ext z
  simp only [RingHom.mem_ker, RingHom.comp_apply, RingEquiv.coe_toRingHom]
  exact (fieldMap (N := N) e).map_eq_zero_iff

private theorem intClosed_comp_fieldMap {R : Type*} [CommRing R] (f : R →+* modularFunctionFieldC k N)
    (hf : ∀ x : modularFunctionFieldC k N,
      (∃ p : Polynomial f.range, p.Monic ∧ Polynomial.eval₂ f.range.subtype x p = 0) →
      x ∈ f.range)
    (x : modularFunctionFieldC k' N)
    (hx : ∃ p : Polynomial ((fieldMap (N := N) e : modularFunctionFieldC k N →+*
        modularFunctionFieldC k' N).comp f).range, p.Monic ∧
      Polynomial.eval₂ ((fieldMap (N := N) e : modularFunctionFieldC k N →+*
        modularFunctionFieldC k' N).comp f).range.subtype x p = 0) :
    x ∈ ((fieldMap (N := N) e : modularFunctionFieldC k N →+* modularFunctionFieldC k' N).comp f).range := by
  set g : modularFunctionFieldC k N →+* modularFunctionFieldC k' N :=
    (fieldMap (N := N) e : modularFunctionFieldC k N →+* modularFunctionFieldC k' N) with hg
  obtain ⟨p, hmonic, hroot⟩ := hx

  have hdown : ∀ z : (g.comp f).range, (fieldMap (N := N) e).symm (z : modularFunctionFieldC k' N) ∈ f.range := by
    rintro ⟨z, hz⟩
    obtain ⟨r, rfl⟩ := hz
    refine ⟨r, ?_⟩
    show f r = (fieldMap (N := N) e).symm (g (f r))
    rw [hg]
    exact ((fieldMap (N := N) e).symm_apply_apply (f r)).symm
  let down : (g.comp f).range →+* f.range :=
    (((fieldMap (N := N) e).symm : modularFunctionFieldC k' N →+* modularFunctionFieldC k N).comp
      (g.comp f).range.subtype).codRestrict f.range hdown
  have hmem : (fieldMap (N := N) e).symm x ∈ f.range := by
    refine hf _ ⟨p.map down, hmonic.map down, ?_⟩
    rw [Polynomial.eval₂_map]
    have h1 : f.range.subtype.comp down
        = (((fieldMap (N := N) e).symm : modularFunctionFieldC k' N →+* modularFunctionFieldC k N).comp
            (g.comp f).range.subtype) :=
      RingHom.ext fun z => rfl
    have h2 := Polynomial.hom_eval₂ p (g.comp f).range.subtype
      ((fieldMap (N := N) e).symm : modularFunctionFieldC k' N →+* modularFunctionFieldC k N) x
    rw [h1]
    refine h2.symm.trans ?_
    rw [hroot, map_zero]
  obtain ⟨r, hr⟩ := hmem
  refine ⟨r, ?_⟩
  show g (f r) = x
  rw [hr, hg]
  exact (fieldMap (N := N) e).apply_symm_apply x

private theorem frac_comp_fieldMap {R : Type*} [CommRing R] (f : R →+* modularFunctionFieldC k N)
    (hf : ∀ x : modularFunctionFieldC k N, ∃ b c : R, f c ≠ 0 ∧ x * f c = f b)
    (x : modularFunctionFieldC k' N) :
    ∃ b c : R,
      ((fieldMap (N := N) e : modularFunctionFieldC k N →+* modularFunctionFieldC k' N).comp f) c ≠ 0 ∧
      x * ((fieldMap (N := N) e : modularFunctionFieldC k N →+* modularFunctionFieldC k' N).comp f) c
        = ((fieldMap (N := N) e : modularFunctionFieldC k N →+* modularFunctionFieldC k' N).comp f) b := by
  obtain ⟨b, c, hc, h⟩ := hf ((fieldMap (N := N) e).symm x)
  refine ⟨b, c, ?_, ?_⟩
  · show fieldMap (N := N) e (f c) ≠ 0
    exact (map_ne_zero_iff _ (fieldMap (N := N) e).injective).mpr hc
  · show x * fieldMap (N := N) e (f c) = fieldMap (N := N) e (f b)
    rw [← h, map_mul, (fieldMap (N := N) e).apply_symm_apply]

include he in

private def modelCongr (fm : FibreModel N A ℓ k red) : FibreModel N A ℓ k' red' where
  BFin := fm.BFin
  BInf := fm.BInf
  constFin_mem := fm.constFin_mem
  constInf_mem := fm.constInf_mem
  jBar_mem := fm.jBar_mem
  jNBar_mem := fm.jNBar_mem
  jInvBar_mem := fm.jInvBar_mem
  integralFin := fm.integralFin
  integralInf := fm.integralInf
  piFin := (fieldMap (N := N) e : modularFunctionFieldC k N →+* modularFunctionFieldC k' N).comp fm.piFin
  piInf := (fieldMap (N := N) e : modularFunctionFieldC k N →+* modularFunctionFieldC k' N).comp fm.piInf
  piFin_const a := by
    show fieldMap (N := N) e (fm.piFin ⟨constantsHom N A a, fm.constFin_mem a⟩) = _
    rw [fm.piFin_const a, fieldMap_const e he a]
  piInf_const a := by
    show fieldMap (N := N) e (fm.piInf ⟨constantsHom N A a, fm.constInf_mem a⟩) = _
    rw [fm.piInf_const a, fieldMap_const e he a]
  piFin_j := by
    show fieldMap (N := N) e (fm.piFin ⟨jBar N, fm.jBar_mem⟩) = _
    rw [fm.piFin_j]
    exact mffCCongr_jLine e N
  piFin_jN := by
    show fieldMap (N := N) e (fm.piFin ⟨jNBar N, fm.jNBar_mem⟩) = _
    rw [fm.piFin_jN]
    exact mffCCongr_jNLine e N
  piInf_jInv := by
    show fieldMap (N := N) e (fm.piInf ⟨(jBar N)⁻¹, fm.jInvBar_mem⟩) = _
    rw [fm.piInf_jInv, map_inv₀, mffCCongr_jLine]
  ker_piFin := by
    rw [ker_comp_fieldMap]
    exact fm.ker_piFin
  ker_piInf := by
    rw [ker_comp_fieldMap]
    exact fm.ker_piInf
  intClosed_piFin := intClosed_comp_fieldMap e fm.piFin fm.intClosed_piFin
  intClosed_piInf := intClosed_comp_fieldMap e fm.piInf fm.intClosed_piInf
  frac_piFin := frac_comp_fieldMap e fm.piFin fm.frac_piFin
  frac_piInf := frac_comp_fieldMap e fm.piInf fm.frac_piInf

private theorem modelCongr_cuspChart (fm : FibreModel N A ℓ k red) (cc : fm.CuspChart) :
    (modelCongr e he fm).CuspChart where
  tBar_mem := cc.tBar_mem
  piInf_t := by
    show fieldMap (N := N) e (fm.piInf ⟨jNBar N * ((jBar N)⁻¹) ^ N, cc.tBar_mem⟩) = _
    rw [cc.piInf_t, map_mul, map_pow, map_inv₀, mffCCongr_jLine, mffCCongr_jNLine]

end ModelCongr

section Square

variable {N : ℕ} [NeZero N] {A : ValuationSubring (AlgebraicClosure ℚ)} {ℓ : ℕ} [Fact ℓ.Prime]
variable {k : Type*} [Field k] [CharP k ℓ] {red : A →+* k}
variable {k' : Type*} [Field k'] [CharP k' ℓ] {red' : A →+* k'}
variable (e : k ≃+* k') (he : ∀ a : A, e (red a) = red' a)

include he in

private theorem spPlace_modelCongr (fm : FibreModel N A ℓ k red)
    (hred : Function.Surjective red) (hred' : Function.Surjective red')
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hsep' : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k'))).map
      (algebraMap (Polynomial k') (RatFunc k'))).Separable)
    (w : Place (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))) :
    (modelCongr e he fm).spPlace hred' dataAll hsep' w
      = placeCongrHetero e (fieldMap (N := N) e) (mffCCongr_algebraMap e N) (fm.spPlace hred dataAll hsep w) := by
  by_cases hfin : ∃ a : A, 0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) (a : AlgebraicClosure ℚ))
  · obtain ⟨a₀, ha₀⟩ := hfin
    refine FibreModel.place_eq_of_forall_finChart_mem_nonunits_iff N ℓ A k' red' (modelCongr e he fm)
      hred' dataAll hsep' _ _ ?_ ?_ ?_
    · exact mem_of_ord_sub_pos _
        (FibreModel.spPlace_d0_j N A ℓ k' red' (modelCongr e he fm) hred' dataAll hsep' w a₀ ha₀)
    · have h := FibreModel.spPlace_d0_j N A ℓ k red fm hred dataAll hsep w a₀ ha₀
      have h' : 0 < (placeCongrHetero e (fieldMap (N := N) e) (mffCCongr_algebraMap e N)
          (fm.spPlace hred dataAll hsep w)).ord
          (fieldMap (N := N) e (⟨jqModC k, jqModC_mem k N⟩
            - algebraMap k (modularFunctionFieldC k N) (red a₀))) := by
        rw [ord_placeCongrHetero]
        exact h
      rw [map_sub, mffCCongr_jLine, mffCCongr_algebraMap, he] at h'
      exact mem_of_ord_sub_pos _ h'
    · intro b
      have h1 := (modelCongr e he fm).piFin_mem_spPlace_nonunits_iff hred' dataAll hsep' w a₀ ha₀ b
      have h2 := fm.piFin_mem_spPlace_nonunits_iff hred dataAll hsep w a₀ ha₀ b
      have h3 := mem_nonunits_placeCongrHetero_iff e (fieldMap (N := N) e) (mffCCongr_algebraMap e N)
        (fm.spPlace hred dataAll hsep w) (fm.piFin b)
      exact h1.trans (h2.symm.trans h3.symm)
  · have hpole : ∀ a : A, w.ord (jBar N - algebraMap (AlgebraicClosure ℚ)
        (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
          (a : AlgebraicClosure ℚ)) ≤ 0 :=
      fun a => not_lt.mp fun h => hfin ⟨a, h⟩
    refine FibreModel.place_eq_of_forall_infChart_mem_nonunits_iff N ℓ A k' red' (modelCongr e he fm)
      hred' dataAll hsep' _ _ ?_ ?_ ?_
    · exact (modelCongr e he fm).jLineInv_mem_spPlace hred' dataAll hsep' w hpole
    · have h := fm.jLineInv_mem_spPlace hred dataAll hsep w hpole
      have h' := (mem_placeCongrHetero_iff e (fieldMap (N := N) e) (mffCCongr_algebraMap e N)
        (fm.spPlace hred dataAll hsep w) _).mpr h
      rwa [map_inv₀, mffCCongr_jLine] at h'
    · intro b
      have h1 := (modelCongr e he fm).piInf_mem_spPlace_nonunits_iff hred' dataAll hsep' w hpole b
      have h2 := fm.piInf_mem_spPlace_nonunits_iff hred dataAll hsep w hpole b
      have h3 := mem_nonunits_placeCongrHetero_iff e (fieldMap (N := N) e) (mffCCongr_algebraMap e N)
        (fm.spPlace hred dataAll hsep w) (fm.piInf b)
      exact h1.trans (h2.symm.trans h3.symm)

private theorem spPlace_eq_of_modelCongr (fm₁ fm₂ : FibreModel N A ℓ k red)
    (hred : Function.Surjective red) (hred' : Function.Surjective red')
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hsep' : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k'))).map
      (algebraMap (Polynomial k') (RatFunc k'))).Separable)
    (h : (modelCongr e he fm₁).spPlace hred' dataAll hsep'
      = (modelCongr e he fm₂).spPlace hred' dataAll hsep') :
    fm₁.spPlace hred dataAll hsep = fm₂.spPlace hred dataAll hsep := by
  funext w
  apply placeCongrHetero_injective e (fieldMap (N := N) e) (mffCCongr_algebraMap e N)
  have h₁ := spPlace_modelCongr e he fm₁ hred hred' dataAll hsep hsep' w
  have h₂ := spPlace_modelCongr e he fm₂ hred hred' dataAll hsep hsep' w
  exact (h₁.symm.trans (congrFun h w)).trans h₂

end Square

end ModularCurve.CharPModel.SpPlaceBaseChange

end

open ModularCurve.CharPModel.SpPlaceBaseChange in
theorem solution
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k) (hred : Function.Surjective red)
    (fm₁ fm₂ : ModularCurve.CharPModel.FibreModel N A ℓ k red)
    (cc₁ : fm₁.CuspChart) (cc₂ : fm₂.CuspChart)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularCurve.ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable) :
    fm₁.spPlace hred dataAll hsep = fm₂.spPlace hred dataAll hsep := by

  let e : k ≃+* IsLocalRing.ResidueField A := (residueToRed red hred).symm
  have he : ∀ a : A, e (red a) = IsLocalRing.residue A a := fun a => by
    show (residueToRed red hred).symm (red a) = IsLocalRing.residue A a
    rw [RingEquiv.symm_apply_eq, residueToRed_residue]
  haveI : CharP (IsLocalRing.ResidueField A) ℓ :=
    charP_of_injective_ringHom (e : k →+* IsLocalRing.ResidueField A).injective ℓ
  have hsep' : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom (IsLocalRing.ResidueField A)))).map
      (algebraMap (Polynomial (IsLocalRing.ResidueField A))
        (RatFunc (IsLocalRing.ResidueField A)))).Separable :=
    separable_congr e.symm _ hsep

  exact spPlace_eq_of_modelCongr e he fm₁ fm₂ hred Ideal.Quotient.mk_surjective dataAll hsep hsep'
    (ModularCurve.CharPModel.FibreModel.spPlace_eq N ℓ hℓN A
      (modelCongr e he fm₁) (modelCongr e he fm₂)
      (modelCongr_cuspChart e he fm₁ cc₁) (modelCongr_cuspChart e he fm₂ cc₂) dataAll hsep')

end S_ModularCurve_CharPModel_FibreModel_spPlace_eq_of_surjective
end P2MW
export P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_eq_of_surjective (solution)
