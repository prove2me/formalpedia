-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_linearIndependent_residue_pair_riemannRochSpace_add_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/bb5e2254-befa-56d6-a9f2-92c5cae9991a

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_integers_linearIndependent_residue_pair_of_finiteDimensional
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_residue_mem_riemannRochSpace_mapDomain_and_hasValue_of_isGoodDiv
import Theorems.Thm_ModularCurve_degree_add_one_sub_genusFF_le_finrank_riemannRochSpace
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_ord_jFun_sub_pos_of_isAffineGeomPlace_reduceFst
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_atkinLehnerBar_smul
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_linearIndependent_residue_pair_riemannRochSpace_add_nsmul
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom"
p2m_attr_erase "simp" "ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl"
p2m_attr_erase "simp" "ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero"
p2m_attr_erase "simp" "TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization

namespace IntBasis

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

theorem not_isStrictFst_of_isStrictSnd (P : PlaceSpecialization A q N data hKr k red hα hβ)
    {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} (hS : P.IsStrictSnd W) : ¬ P.IsStrictFst W := by
  intro hF
  apply hF.2
  rw [hF.1]
  exact hS.1.symm

theorem isAffineGeomPlace_frob {v : Place k ↥(modularFunctionFieldC k N)} (hv : IsAffineGeomPlace k N v) :
    IsAffineGeomPlace k N (frobOnPlacesGeomLevel k N data hKr v) := by
  have hrat : v.IsRational :=
    (Place.isRational_iff_deg_eq_one v).mpr (place_deg_eq_one_of_isAlgClosed k N v)
  exact ((exists_isCentreOf_of_isRational hrat hv).frobOnPlacesGeomLevel data hKr).isAffineGeomPlace

theorem exists_coeffMap_eq_smul_of_forall_coeff_mem {f : ↥(modularFunctionFieldBar (N * q))} {c : AlgebraicClosure ℚ}
    (hA : ∀ n : ℤ, (c • (f : LaurentSeries (AlgebraicClosure ℚ))).coeff n ∈ A) :
    ∃ y : LaurentSeries A, coeffMap A.subtype y = c • (f : LaurentSeries (AlgebraicClosure ℚ)) := by
  refine ⟨⟨fun n => ⟨(c • (f : LaurentSeries (AlgebraicClosure ℚ))).coeff n, hA n⟩, ?_⟩, ?_⟩
  · have hs : Function.support (fun n => (⟨(c • (f : LaurentSeries (AlgebraicClosure ℚ))).coeff n, hA n⟩ : A))
        = Function.support (c • (f : LaurentSeries (AlgebraicClosure ℚ))).coeff := by
      ext n
      simp only [Function.mem_support, ne_eq]
      rw [← Subtype.coe_inj]
      rfl
    rw [hs]
    exact (c • (f : LaurentSeries (AlgebraicClosure ℚ))).isPWO_support
  · ext n
    rfl

theorem hint_of_mem_riemannRochSpace (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hsupp : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), D W ≠ 0 →
      IsAffineGeomPlace k N (P.reduceFst W) ∧
      IsAffineGeomPlace k N (P.reduceFst (ProlongationTuple.atkinLehnerBar N q • W)))
    {f : ↥(modularFunctionFieldBar (N * q))} (hf : f ∈ riemannRochSpace D) (hf0 : f ≠ 0) :
    (∃ (c : AlgebraicClosure ℚ) (y : LaurentSeries A), c ≠ 0 ∧ coeffMap A.subtype y = c • (f : LaurentSeries (AlgebraicClosure ℚ))) ∧
    (∃ (c : AlgebraicClosure ℚ) (y : LaurentSeries A), c ≠ 0 ∧
      coeffMap A.subtype y = c • ((ProlongationTuple.atkinLehnerBar N q f : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))) := by
  set σ := ProlongationTuple.atkinLehnerBar N q with hσ

  have hpoleD : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), W.ord f < 0 → D W ≠ 0 := by
    intro W hW hDW
    rcases (mem_riemannRochSpace_iff.mp hf) W with h0 | hb
    · exact hf0 h0
    · rw [hDW, neg_zero] at hb
      omega
  constructor
  · have hpole : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), W.ord f < 0 → ∃ a : A, 0 < W.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full (N * q) (jq_mem (N * q)))⟩
          - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) := by
      intro W hW
      obtain ⟨a, ha, -⟩ := P.exists_ord_jFun_sub_pos_of_isAffineGeomPlace_reduceFst W (hsupp W (hpoleD W hW)).1
      exact ⟨a, ha⟩
    obtain ⟨c, hc, hcA⟩ := exists_forall_coeff_smul_mem_of_forall_ord_neg A (N * q) f hf0 hpole
    obtain ⟨y, hy⟩ := exists_coeffMap_eq_smul_of_forall_coeff_mem hcA
    exact ⟨c, y, hc, hy⟩
  · have hσf0 : σ f ≠ 0 := by
      intro h0; exact hf0 (by simpa using congrArg σ.symm h0)
    have hpole : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), W.ord (σ f) < 0 → ∃ a : A, 0 < W.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full (N * q) (jq_mem (N * q)))⟩
          - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) := by
      intro W hW

      have hW' : (σ⁻¹ • W).ord f < 0 := by
        have h := Place.ord_smul σ (σ⁻¹ • W) f
        rw [smul_inv_smul] at h
        rw [← h]
        exact hW
      have haff := (hsupp (σ⁻¹ • W) (hpoleD _ hW')).2
      rw [smul_inv_smul] at haff
      obtain ⟨a, ha, -⟩ := P.exists_ord_jFun_sub_pos_of_isAffineGeomPlace_reduceFst W haff
      exact ⟨a, ha⟩
    obtain ⟨c, hc, hcA⟩ := exists_forall_coeff_smul_mem_of_forall_ord_neg A (N * q) (σ f) hσf0 hpole
    obtain ⟨y, hy⟩ := exists_coeffMap_eq_smul_of_forall_coeff_mem hcA
    exact ⟨c, y, hc, hy⟩

theorem sum_single_apply_of_injective {α ι : Type*} [Fintype ι] [DecidableEq α] (v : ι → α)
    (hv : Function.Injective v) (n : ℤ) (a : α) :
    (∑ i, Finsupp.single (v i) n) a = if ∃ i, v i = a then n else 0 := by
  classical
  rw [Finsupp.coe_finset_sum, Finset.sum_apply]
  simp only [Finsupp.single_apply]
  split_ifs with h
  · obtain ⟨i, hi⟩ := h
    rw [Finset.sum_eq_single i]
    · rw [if_pos hi]
    · intro j _ hj
      rw [if_neg]
      intro hji
      exact hj (hv (hji.trans hi.symm))
    · intro hh; exact absurd (Finset.mem_univ _) hh
  · push_neg at h
    exact Finset.sum_eq_zero fun i _ => if_neg (h i)

theorem sum_single_apply_nonneg {α ι : Type*} [Fintype ι] (v : ι → α) (a : α) :
    0 ≤ (∑ i, Finsupp.single (v i) (1 : ℤ)) a := by
  classical
  rw [Finsupp.coe_finset_sum, Finset.sum_apply]
  exact Finset.sum_nonneg fun i _ => by
    rw [Finsupp.single_apply]; split_ifs <;> omega

theorem exists_eq_of_sum_single_apply_ne_zero {α ι : Type*} [Fintype ι] (v : ι → α) (n : ℤ) (a : α)
    (h : (∑ i, Finsupp.single (v i) n) a ≠ 0) : ∃ i, v i = a := by
  classical
  by_contra hne
  push_neg at hne
  apply h
  rw [Finsupp.coe_finset_sum, Finset.sum_apply]
  exact Finset.sum_eq_zero fun i _ => by rw [Finsupp.single_apply, if_neg (hne i)]

section LinAlg

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem exists_index_avoid {M : ℕ} (pr : Fin M → V) (hpr : LinearIndependent K pr) (e : V) (he0 : e ≠ 0)
    (hM : 0 < M) : ∃ i₀ : Fin M, ∀ d : Fin M → K, d i₀ = 0 → ∑ i, d i • pr i ≠ e := by
  classical
  by_cases hspan : e ∈ Submodule.span K (Set.range pr)
  · obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hspan
    have hc0 : ∃ i₀, c i₀ ≠ 0 := by
      by_contra hall
      push_neg at hall
      apply he0
      rw [← hc]
      exact Finset.sum_eq_zero fun i _ => by rw [hall i, zero_smul]
    obtain ⟨i₀, hci₀⟩ := hc0
    refine ⟨i₀, fun d hd hsum => hci₀ ?_⟩
    have hdiff : ∑ i, (c i - d i) • pr i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, hc, hsum, sub_self]
    have := Fintype.linearIndependent_iff.mp hpr (fun i => c i - d i) hdiff i₀
    rw [hd, sub_zero] at this
    exact this
  · refine ⟨⟨0, hM⟩, fun d _ hsum => hspan ?_⟩
    rw [← hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem exists_embedding_avoid {M n : ℕ} (i₀ : Fin M) (h : n + 1 ≤ M) :
    ∃ emb : Fin n → Fin M, Function.Injective emb ∧ ∀ j, emb j ≠ i₀ := by
  refine ⟨fun j => if (j : ℕ) < (i₀ : ℕ) then ⟨j, by omega⟩ else ⟨(j : ℕ) + 1, by omega⟩, ?_, ?_⟩
  · intro j j' hjj
    have h' := congrArg Fin.val hjj
    simp only [apply_ite Fin.val, Fin.val_mk] at h'
    apply Fin.ext
    split_ifs at h' <;> omega
  · intro j hji
    have h' := congrArg Fin.val hji
    simp only [apply_ite Fin.val, Fin.val_mk] at h'
    split_ifs at h' <;> omega

theorem linearIndependent_cons_of_avoid {M n : ℕ} (pr : Fin M → V) (hpr : LinearIndependent K pr) (e : V)
    (i₀ : Fin M) (hi₀ : ∀ d : Fin M → K, d i₀ = 0 → ∑ i, d i • pr i ≠ e)
    (emb : Fin n → Fin M) (hinj : Function.Injective emb) (hne : ∀ j, emb j ≠ i₀) :
    LinearIndependent K (Fin.cons e (pr ∘ emb) : Fin (n + 1) → V) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  rw [Fin.sum_univ_succ, Fin.cons_zero] at hc
  simp only [Fin.cons_succ, Function.comp_apply] at hc
  have hc0 : c 0 = 0 := by
    by_contra hc0
    set a : Fin n → K := fun j => -((c 0)⁻¹ * c (Fin.succ j)) with ha
    have hea : ∑ j, a j • pr (emb j) = e := by
      have h2 : c 0 • e = -∑ j, c (Fin.succ j) • pr (emb j) := eq_neg_of_add_eq_zero_left hc
      have h3 : e = (c 0)⁻¹ • (c 0 • e) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [h3, h2, smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ha, neg_smul, smul_smul]
    set d : Fin M → K := fun i => ∑ j, if emb j = i then a j else 0 with hdd
    have hd0 : d i₀ = 0 := Finset.sum_eq_zero fun j _ => if_neg (hne j)
    apply hi₀ d hd0
    rw [← hea]
    have hstep : ∀ i, d i • pr i = ∑ j, if emb j = i then a j • pr i else 0 := fun i => by
      rw [hdd, Finset.sum_smul]
      exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
    simp only [hstep]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_ite_eq]
    simp
  intro l
  refine Fin.cases hc0 (fun j => ?_) l
  rw [hc0, zero_smul, zero_add] at hc
  exact Fintype.linearIndependent_iff.mp (hpr.comp emb hinj) (fun j => c (Fin.succ j)) hc j

end LinAlg

set_option maxHeartbeats 6400000 in
theorem intbasis (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    {W : Finset (Place k ↥(modularFunctionFieldC k N))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : P.ProlongationTuple) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    {d₁ d₂ : ℕ}
    (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j))
    (hinj₁ : Function.Injective fun i => P.reduceFst (Q₁ i))
    (hinj₂ : Function.Injective fun j => P.reduceSnd (Q₂ j))
    {T₁ T₂ : Finset (Place k ↥(modularFunctionFieldC k N))}
    (hT₁ : ∀ v, v ∈ T₁ ↔ ∃ i, P.reduceFst (Q₁ i) = v)
    (hT₂ : ∀ v, v ∈ T₂ ↔ ∃ j, P.reduceSnd (Q₂ j) = v)
    (hT₁aff : ∀ v ∈ T₁, IsAffineGeomPlace k N v) (hT₂aff : ∀ v ∈ T₂, IsAffineGeomPlace k N v)
    (hdeg : d₁ + d₂ = genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hQ₁' : ∀ i, P.IsStrictFst (Q₁' i)) (hQ₂' : ∀ j, P.IsStrictSnd (Q₂' j))
    (hred₁ : ∀ i, P.reduceFst (Q₁' i) = P.reduceFst (Q₁ i))
    (hred₂ : ∀ j, P.reduceSnd (Q₂' j) = P.reduceSnd (Q₂ j))
    (m : ℕ) (hm : (m : k) ≠ 0) :
    ∃ (h : Fin (m * (d₁ + d₂) - (d₁ + d₂) + 1) → ↥(modularFunctionFieldBar (N * q)))
      (h₁ : ∀ l, h l ∈ R.R₁.integers) (h₂ : ∀ l, h l ∈ R.R₂.integers),
      h 0 = 1 ∧
      (∀ l, h l ≠ 0) ∧
      (∀ l (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
        -(((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) :
                Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V)
            + ((m : ℤ) - 1) * ((∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) :
                Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V)) ≤ V.ord (h l)) ∧
      (∀ l,
        (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₁ → 0 ≤ v.ord (R.residue₁ ⟨h l, h₁ l⟩ : ↥(modularFunctionFieldC k N))) ∧
        (∀ v ∈ T₁, -(m : ℤ) ≤ v.ord (R.residue₁ ⟨h l, h₁ l⟩ : ↥(modularFunctionFieldC k N))) ∧
        (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₂ → 0 ≤ v.ord (R.residue₂ ⟨h l, h₂ l⟩ : ↥(modularFunctionFieldC k N))) ∧
        (∀ v ∈ T₂, -(m : ℤ) ≤ v.ord (R.residue₂ ⟨h l, h₂ l⟩ : ↥(modularFunctionFieldC k N))) ∧
        (∀ w ∈ W, ∃ c : k, w.HasValue (R.residue₁ ⟨h l, h₁ l⟩ : ↥(modularFunctionFieldC k N)) c ∧
          (arithFrobC q k N • w).HasValue (R.residue₂ ⟨h l, h₂ l⟩ : ↥(modularFunctionFieldC k N)) c)) ∧
      LinearIndependent k (fun l =>
        ((R.residue₁ ⟨h l, h₁ l⟩ : ↥(modularFunctionFieldC k N)), (R.residue₂ ⟨h l, h₂ l⟩ : ↥(modularFunctionFieldC k N)))) := by
  classical

  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · exact absurd (by simp) hm
    · exact h
  set g : ℕ := d₁ + d₂ with hg
  set K : ℕ := m * g - g with hKdef
  have hKg : (K : ℤ) = (m : ℤ) * g - g := by
    rw [hKdef]
    have : g ≤ m * g := Nat.le_mul_of_pos_left g hm1
    omega

  set E' : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) :=
    ∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) with hE'
  set E₀ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) :=
    ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) with hE₀
  set D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) := E' + ((m : ℤ) - 1) • E₀ with hD
  have hDapp : ∀ V, D V = E' V + ((m : ℤ) - 1) * E₀ V := fun V => by
    rw [hD, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  have hE'nn : ∀ V, 0 ≤ E' V := fun V => by
    rw [hE', Finsupp.add_apply]
    exact add_nonneg (sum_single_apply_nonneg _ _) (sum_single_apply_nonneg _ _)
  have hE₀nn : ∀ V, 0 ≤ E₀ V := fun V => by
    rw [hE₀, Finsupp.add_apply]
    exact add_nonneg (sum_single_apply_nonneg _ _) (sum_single_apply_nonneg _ _)
  have hm1' : (0 : ℤ) ≤ (m : ℤ) - 1 := by omega
  have hDnn : 0 ≤ D := fun V => by
    rw [Finsupp.coe_zero, Pi.zero_apply, hDapp]
    exact add_nonneg (hE'nn V) (mul_nonneg hm1' (hE₀nn V))

  have hsuppD : ∀ V, D V ≠ 0 →
      ((∃ i, Q₁' i = V) ∨ (∃ i, Q₁ i = V)) ∨ ((∃ j, Q₂' j = V) ∨ (∃ j, Q₂ j = V)) := by
    intro V hV
    by_contra hne
    push_neg at hne
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hne
    apply hV
    have z1 : (∑ i, Finsupp.single (Q₁' i) (1 : ℤ)) V = 0 := by
      by_contra hz; obtain ⟨i, hi⟩ := exists_eq_of_sum_single_apply_ne_zero _ _ _ hz; exact h1 i hi
    have z2 : (∑ i, Finsupp.single (Q₁ i) (1 : ℤ)) V = 0 := by
      by_contra hz; obtain ⟨i, hi⟩ := exists_eq_of_sum_single_apply_ne_zero _ _ _ hz; exact h2 i hi
    have z3 : (∑ j, Finsupp.single (Q₂' j) (1 : ℤ)) V = 0 := by
      by_contra hz; obtain ⟨j, hj⟩ := exists_eq_of_sum_single_apply_ne_zero _ _ _ hz; exact h3 j hj
    have z4 : (∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) V = 0 := by
      by_contra hz; obtain ⟨j, hj⟩ := exists_eq_of_sum_single_apply_ne_zero _ _ _ hz; exact h4 j hj
    rw [hDapp, hE', hE₀, Finsupp.add_apply, Finsupp.add_apply, z1, z2, z3, z4]
    ring
  have hstrict : ∀ V, D V ≠ 0 → P.IsStrictFst V ∨ P.IsStrictSnd V := by
    intro V hV
    rcases hsuppD V hV with (⟨i, rfl⟩ | ⟨i, rfl⟩) | (⟨j, rfl⟩ | ⟨j, rfl⟩)
    exacts [Or.inl (hQ₁' i), Or.inl (hQ₁ i), Or.inr (hQ₂' j), Or.inr (hQ₂ j)]
  have hgood : P.IsGoodDiv D := fun V hV => hstrict V (Finsupp.mem_support_iff.mp hV)

  have hfstaff : ∀ V, P.IsStrictFst V → D V ≠ 0 → IsAffineGeomPlace k N (P.reduceFst V) := by
    intro V hVs hV
    rcases hsuppD V hV with (⟨i, rfl⟩ | ⟨i, rfl⟩) | (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact hT₁aff _ ((hT₁ _).mpr ⟨i, (hred₁ i).symm⟩)
    · exact hT₁aff _ ((hT₁ _).mpr ⟨i, rfl⟩)
    · exact absurd hVs (not_isStrictFst_of_isStrictSnd P (hQ₂' j))
    · exact absurd hVs (not_isStrictFst_of_isStrictSnd P (hQ₂ j))
  have hsndaff : ∀ V, P.IsStrictSnd V → D V ≠ 0 → IsAffineGeomPlace k N (P.reduceSnd V) := by
    intro V hVs hV
    rcases hsuppD V hV with (⟨i, rfl⟩ | ⟨i, rfl⟩) | (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact absurd (hQ₁' i) (not_isStrictFst_of_isStrictSnd P hVs)
    · exact absurd (hQ₁ i) (not_isStrictFst_of_isStrictSnd P hVs)
    · exact hT₂aff _ ((hT₂ _).mpr ⟨j, (hred₂ j).symm⟩)
    · exact hT₂aff _ ((hT₂ _).mpr ⟨j, rfl⟩)
  have hsupp : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), D V ≠ 0 →
      IsAffineGeomPlace k N (P.reduceFst V) ∧
      IsAffineGeomPlace k N (P.reduceFst (ProlongationTuple.atkinLehnerBar N q • V)) := by
    intro V hV
    rw [P.reduceFst_atkinLehnerBar_smul hqN V]
    rcases hstrict V hV with hs | hs
    · refine ⟨hfstaff V hs hV, ?_⟩
      rw [← hs.1]
      exact isAffineGeomPlace_frob (hfstaff V hs hV)
    · refine ⟨?_, hsndaff V hs hV⟩
      rw [hs.1]
      exact isAffineGeomPlace_frob (hsndaff V hs hV)

  set V : Submodule (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) := riemannRochSpace D with hVdef
  have hdegD : D.degree = (m : ℤ) * g := by
    have hdeg1 : ∀ (w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))), (w.deg : ℤ) = 1 := fun w => by
      rw [deg_eq_one_modularFunctionFieldBar (N * q) w]; rfl
    have hsum : ∀ {ι : Type} [Fintype ι] (f : ι → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
        Divisor.degree (∑ i, Finsupp.single (f i) (1 : ℤ)) = Fintype.card ι := by
      intro ι _ f
      rw [map_sum]
      simp only [Divisor.degree_single, hdeg1, mul_one, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
    rw [hD, map_add, map_zsmul, hE', hE₀, map_add, map_add, hsum, hsum, hsum, hsum, Fintype.card_fin,
      Fintype.card_fin, hg]
    push_cast
    ring
  have hfin : (K : ℤ) + 1 ≤ Module.finrank (AlgebraicClosure ℚ) V := by
    have h := degree_add_one_sub_genusFF_le_finrank_riemannRochSpace (N * q) D
    rw [hdegD, ← hdeg] at h
    rw [hKg]
    push_cast at h ⊢
    linarith
  haveI : FiniteDimensional (AlgebraicClosure ℚ) V := Module.finite_of_finrank_pos (by omega)
  set M : ℕ := Module.finrank (AlgebraicClosure ℚ) V with hMdef
  have hKM : K + 1 ≤ M := by exact_mod_cast hfin

  obtain ⟨G, hG₁, hG₂, hGV, hGind⟩ :=
    R.exists_mem_integers_linearIndependent_residue_pair_of_finiteDimensional V (by
      let b := Module.finBasis (AlgebraicClosure ℚ) V
      refine ⟨fun i => (b i : ↥(modularFunctionFieldBar (N * q))), fun i => (b i).2, ?_, fun i => ?_⟩
      · exact b.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
      · have hb0 : ((b i : V) : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := fun h0 =>
          b.ne_zero i (Subtype.ext h0)
        exact hint_of_mem_riemannRochSpace P D hsupp (b i).2 hb0)

  have hGne : ∀ i, G i ≠ 0 := by
    intro i h0
    apply hGind.ne_zero i
    refine Prod.ext ?_ ?_
    · show (R.residue₁ ⟨G i, hG₁ i⟩ : ↥(modularFunctionFieldC k N)) = 0
      have : (⟨G i, hG₁ i⟩ : R.R₁.integers) = 0 := Subtype.ext h0
      rw [this, map_zero]
    · show (R.residue₂ ⟨G i, hG₂ i⟩ : ↥(modularFunctionFieldC k N)) = 0
      have : (⟨G i, hG₂ i⟩ : R.R₂.integers) = 0 := Subtype.ext h0
      rw [this, map_zero]

  set u₁ : Fin d₁ → Place k ↥(modularFunctionFieldC k N) := fun i => P.reduceFst (Q₁ i) with hu₁
  set u₂ : Fin d₂ → Place k ↥(modularFunctionFieldC k N) := fun j => P.reduceSnd (Q₂ j) with hu₂
  have hX₁ : Finsupp.mapDomain P.reduceFst (P.fstDiv D)
      = ∑ i, Finsupp.single (u₁ i) (1 : ℤ) + ((m : ℤ) - 1) • ∑ i, Finsupp.single (u₁ i) (1 : ℤ) := by
    have hf1 : (∑ i, Finsupp.single (Q₁' i) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))).filter P.IsStrictFst
        = ∑ i, Finsupp.single (Q₁' i) (1 : ℤ) := by
      rw [Finsupp.filter_eq_self_iff]
      intro x hx
      obtain ⟨i, rfl⟩ := exists_eq_of_sum_single_apply_ne_zero _ _ _ hx
      exact hQ₁' i
    have hf2 : (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))).filter P.IsStrictFst
        = ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) := by
      rw [Finsupp.filter_eq_self_iff]
      intro x hx
      obtain ⟨i, rfl⟩ := exists_eq_of_sum_single_apply_ne_zero _ _ _ hx
      exact hQ₁ i
    have hf3 : (∑ j, Finsupp.single (Q₂' j) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))).filter P.IsStrictFst = 0 := by
      rw [Finsupp.filter_eq_zero_iff]
      intro x hx
      by_contra hne
      obtain ⟨j, rfl⟩ := exists_eq_of_sum_single_apply_ne_zero _ _ _ hne
      exact not_isStrictFst_of_isStrictSnd P (hQ₂' j) hx
    have hf4 : (∑ j, Finsupp.single (Q₂ j) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))).filter P.IsStrictFst = 0 := by
      rw [Finsupp.filter_eq_zero_iff]
      intro x hx
      by_contra hne
      obtain ⟨j, rfl⟩ := exists_eq_of_sum_single_apply_ne_zero _ _ _ hne
      exact not_isStrictFst_of_isStrictSnd P (hQ₂ j) hx
    have hfst : P.fstDiv D = ∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ((m : ℤ) - 1) • ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) := by
      show D.filter P.IsStrictFst = _
      rw [hD, hE', hE₀, Finsupp.filter_add, Finsupp.filter_add, Finsupp.filter_smul, Finsupp.filter_add,
        hf1, hf2, hf3, hf4, add_zero, add_zero]
    rw [hfst, Finsupp.mapDomain_add, Finsupp.mapDomain_smul, Finsupp.mapDomain_finset_sum,
      Finsupp.mapDomain_finset_sum]
    simp only [Finsupp.mapDomain_single, hred₁]
    rfl
  have hX₂ : Finsupp.mapDomain P.reduceSnd (P.sndDiv D)
      = ∑ j, Finsupp.single (u₂ j) (1 : ℤ) + ((m : ℤ) - 1) • ∑ j, Finsupp.single (u₂ j) (1 : ℤ) := by
    have hf1 : (∑ j, Finsupp.single (Q₂' j) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))).filter P.IsStrictSnd
        = ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) := by
      rw [Finsupp.filter_eq_self_iff]
      intro x hx
      obtain ⟨j, rfl⟩ := exists_eq_of_sum_single_apply_ne_zero _ _ _ hx
      exact hQ₂' j
    have hf2 : (∑ j, Finsupp.single (Q₂ j) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))).filter P.IsStrictSnd
        = ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) := by
      rw [Finsupp.filter_eq_self_iff]
      intro x hx
      obtain ⟨j, rfl⟩ := exists_eq_of_sum_single_apply_ne_zero _ _ _ hx
      exact hQ₂ j
    have hf3 : (∑ i, Finsupp.single (Q₁' i) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))).filter P.IsStrictSnd = 0 := by
      rw [Finsupp.filter_eq_zero_iff]
      intro x hx
      by_contra hne
      obtain ⟨i, rfl⟩ := exists_eq_of_sum_single_apply_ne_zero _ _ _ hne
      exact not_isStrictFst_of_isStrictSnd P hx (hQ₁' i)
    have hf4 : (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))).filter P.IsStrictSnd = 0 := by
      rw [Finsupp.filter_eq_zero_iff]
      intro x hx
      by_contra hne
      obtain ⟨i, rfl⟩ := exists_eq_of_sum_single_apply_ne_zero _ _ _ hne
      exact not_isStrictFst_of_isStrictSnd P hx (hQ₁ i)
    have hsnd : P.sndDiv D = ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) + ((m : ℤ) - 1) • ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) := by
      show D.filter P.IsStrictSnd = _
      rw [hD, hE', hE₀, Finsupp.filter_add, Finsupp.filter_add, Finsupp.filter_smul, Finsupp.filter_add,
        hf3, hf1, hf4, hf2, zero_add, zero_add]
    rw [hsnd, Finsupp.mapDomain_add, Finsupp.mapDomain_smul, Finsupp.mapDomain_finset_sum,
      Finsupp.mapDomain_finset_sum]
    simp only [Finsupp.mapDomain_single, hred₂]
    rfl
  have hX₁app : ∀ a, (Finsupp.mapDomain P.reduceFst (P.fstDiv D)) a = if a ∈ T₁ then (m : ℤ) else 0 := by
    intro a
    rw [hX₁, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, sum_single_apply_of_injective u₁ hinj₁]
    by_cases ha : a ∈ T₁
    · rw [if_pos ((hT₁ a).mp ha), if_pos ha]; ring
    · rw [if_neg (fun h => ha ((hT₁ a).mpr h)), if_neg ha]; ring
  have hX₂app : ∀ a, (Finsupp.mapDomain P.reduceSnd (P.sndDiv D)) a = if a ∈ T₂ then (m : ℤ) else 0 := by
    intro a
    rw [hX₂, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, sum_single_apply_of_injective u₂ hinj₂]
    by_cases ha : a ∈ T₂
    · rw [if_pos ((hT₂ a).mp ha), if_pos ha]; ring
    · rw [if_neg (fun h => ha ((hT₂ a).mpr h)), if_neg ha]; ring
  have hGsec : ∀ i,
      (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₁ → 0 ≤ v.ord (R.residue₁ ⟨G i, hG₁ i⟩ : ↥(modularFunctionFieldC k N))) ∧
      (∀ v ∈ T₁, -(m : ℤ) ≤ v.ord (R.residue₁ ⟨G i, hG₁ i⟩ : ↥(modularFunctionFieldC k N))) ∧
      (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₂ → 0 ≤ v.ord (R.residue₂ ⟨G i, hG₂ i⟩ : ↥(modularFunctionFieldC k N))) ∧
      (∀ v ∈ T₂, -(m : ℤ) ≤ v.ord (R.residue₂ ⟨G i, hG₂ i⟩ : ↥(modularFunctionFieldC k N))) ∧
      (∀ w ∈ W, ∃ c : k, w.HasValue (R.residue₁ ⟨G i, hG₁ i⟩ : ↥(modularFunctionFieldC k N)) c ∧
        (arithFrobC q k N • w).HasValue (R.residue₂ ⟨G i, hG₂ i⟩ : ↥(modularFunctionFieldC k N)) c) := by
    intro i
    obtain ⟨hL1, hL2, hval⟩ :=
      hR.residue_mem_riemannRochSpace_mapDomain_and_hasValue_of_isGoodDiv hqN hW _ hRL hNV hO D hDnn hgood
        (G i) (hGV i) (hG₁ i) (hG₂ i)
    rw [mem_riemannRochSpace_iff] at hL1 hL2
    refine ⟨fun v hv => ?_, fun v hv => ?_, fun v hv => ?_, fun v hv => ?_, hval⟩
    · rcases hL1 v with h0 | hb
      · rw [h0, Place.ord_zero]
      · rw [hX₁app, if_neg hv, neg_zero] at hb; exact hb
    · rcases hL1 v with h0 | hb
      · rw [h0, Place.ord_zero]; omega
      · rw [hX₁app, if_pos hv] at hb; exact hb
    · rcases hL2 v with h0 | hb
      · rw [h0, Place.ord_zero]
      · rw [hX₂app, if_neg hv, neg_zero] at hb; exact hb
    · rcases hL2 v with h0 | hb
      · rw [h0, Place.ord_zero]; omega
      · rw [hX₂app, if_pos hv] at hb; exact hb

  let pr : Fin M → ↥(modularFunctionFieldC k N) × ↥(modularFunctionFieldC k N) := fun i =>
    ((R.residue₁ ⟨G i, hG₁ i⟩ : ↥(modularFunctionFieldC k N)), (R.residue₂ ⟨G i, hG₂ i⟩ : ↥(modularFunctionFieldC k N)))
  have hpr : LinearIndependent k pr := hGind
  have one₁ : (1 : ↥(modularFunctionFieldBar (N * q))) ∈ R.R₁.integers := one_mem _
  have one₂ : (1 : ↥(modularFunctionFieldBar (N * q))) ∈ R.R₂.integers := one_mem _
  have hres1₁ : ∀ h1 : (1 : ↥(modularFunctionFieldBar (N * q))) ∈ R.R₁.integers, (R.residue₁ ⟨1, h1⟩ : ↥(modularFunctionFieldC k N)) = 1 := fun h1 => by
    have : (⟨1, h1⟩ : R.R₁.integers) = 1 := Subtype.ext rfl
    rw [this, map_one]
  have hres1₂ : ∀ h2 : (1 : ↥(modularFunctionFieldBar (N * q))) ∈ R.R₂.integers, (R.residue₂ ⟨1, h2⟩ : ↥(modularFunctionFieldC k N)) = 1 := fun h2 => by
    have : (⟨1, h2⟩ : R.R₂.integers) = 1 := Subtype.ext rfl
    rw [this, map_one]
  set e : ↥(modularFunctionFieldC k N) × ↥(modularFunctionFieldC k N) := (1, 1) with he
  have he0 : e ≠ 0 := by
    intro h; have := congrArg Prod.fst h; exact one_ne_zero this

  have hM1 : 1 ≤ M := by omega
  obtain ⟨i₀, hi₀⟩ := exists_index_avoid pr hpr e he0 (by omega)
  obtain ⟨emb, hemb_inj, hemb_ne⟩ := exists_embedding_avoid (n := K) i₀ hKM
  have hind : LinearIndependent k (Fin.cons e (pr ∘ emb) : Fin (K + 1) → ↥(modularFunctionFieldC k N) × ↥(modularFunctionFieldC k N)) :=
    linearIndependent_cons_of_avoid pr hpr e i₀ hi₀ emb hemb_inj hemb_ne

  let hfun : Fin (K + 1) → ↥(modularFunctionFieldBar (N * q)) := Fin.cons 1 (fun j => G (emb j))
  have hh₁ : ∀ l, hfun l ∈ R.R₁.integers := fun l => Fin.cases one₁ (fun j => hG₁ (emb j)) l
  have hh₂ : ∀ l, hfun l ∈ R.R₂.integers := fun l => Fin.cases one₂ (fun j => hG₂ (emb j)) l
  refine ⟨hfun, hh₁, hh₂, rfl, ?_, ?_, ?_, ?_⟩
  ·
    intro l
    refine Fin.cases ?_ (fun j => ?_) l
    · exact one_ne_zero
    · exact hGne (emb j)
  ·
    intro l V'
    refine Fin.cases ?_ (fun j => ?_) l
    · show -(E' V' + ((m : ℤ) - 1) * E₀ V') ≤ V'.ord (1 : ↥(modularFunctionFieldBar (N * q)))
      rw [Place.ord_one]
      have := add_nonneg (hE'nn V') (mul_nonneg hm1' (hE₀nn V'))
      omega
    · show -(E' V' + ((m : ℤ) - 1) * E₀ V') ≤ V'.ord (G (emb j))
      rw [← hDapp]
      rcases (mem_riemannRochSpace_iff.mp (hGV (emb j))) V' with h0 | hb
      · exact absurd h0 (hGne _)
      · exact hb
  ·
    intro l
    refine Fin.cases ?_ (fun j => ?_) l
    · show (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₁ → 0 ≤ v.ord (R.residue₁ ⟨(1 : ↥(modularFunctionFieldBar (N * q))), one₁⟩ : ↥(modularFunctionFieldC k N))) ∧
        (∀ v ∈ T₁, -(m : ℤ) ≤ v.ord (R.residue₁ ⟨(1 : ↥(modularFunctionFieldBar (N * q))), one₁⟩ : ↥(modularFunctionFieldC k N))) ∧
        (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₂ → 0 ≤ v.ord (R.residue₂ ⟨(1 : ↥(modularFunctionFieldBar (N * q))), one₂⟩ : ↥(modularFunctionFieldC k N))) ∧
        (∀ v ∈ T₂, -(m : ℤ) ≤ v.ord (R.residue₂ ⟨(1 : ↥(modularFunctionFieldBar (N * q))), one₂⟩ : ↥(modularFunctionFieldC k N))) ∧
        (∀ w ∈ W, ∃ c : k, w.HasValue (R.residue₁ ⟨(1 : ↥(modularFunctionFieldBar (N * q))), one₁⟩ : ↥(modularFunctionFieldC k N)) c ∧
          (arithFrobC q k N • w).HasValue (R.residue₂ ⟨(1 : ↥(modularFunctionFieldBar (N * q))), one₂⟩ : ↥(modularFunctionFieldC k N)) c)
      rw [hres1₁, hres1₂]
      refine ⟨fun v _ => by rw [Place.ord_one], fun v _ => by rw [Place.ord_one]; omega,
        fun v _ => by rw [Place.ord_one], fun v _ => by rw [Place.ord_one]; omega,
        fun w _ => ⟨1, Place.hasValue_one w, Place.hasValue_one _⟩⟩
    · exact hGsec (emb j)
  ·
    have hfam : (fun l => ((R.residue₁ ⟨hfun l, hh₁ l⟩ : ↥(modularFunctionFieldC k N)), (R.residue₂ ⟨hfun l, hh₂ l⟩ : ↥(modularFunctionFieldC k N))))
        = Fin.cons e (pr ∘ emb) := by
      funext l
      refine Fin.cases ?_ (fun j => ?_) l
      · show ((R.residue₁ ⟨(1 : ↥(modularFunctionFieldBar (N * q))), one₁⟩ : ↥(modularFunctionFieldC k N)), (R.residue₂ ⟨(1 : ↥(modularFunctionFieldBar (N * q))), one₂⟩ : ↥(modularFunctionFieldC k N))) = _
        rw [Fin.cons_zero, hres1₁, hres1₂]
      · rw [Fin.cons_succ]
        rfl
    rw [hfam]
    exact hind

end IntBasis

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
    {d₁ d₂ : ℕ}
    (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j))
    (hinj₁ : Function.Injective fun i => P.reduceFst (Q₁ i))
    (hinj₂ : Function.Injective fun j => P.reduceSnd (Q₂ j))
    {T₁ T₂ : Finset (Place k ↥(modularFunctionFieldC k N))}
    (hT₁ : ∀ v, v ∈ T₁ ↔ ∃ i, P.reduceFst (Q₁ i) = v)
    (hT₂ : ∀ v, v ∈ T₂ ↔ ∃ j, P.reduceSnd (Q₂ j) = v)
    (hT₁W : Disjoint T₁ W)
    (hT₁aff : ∀ v ∈ T₁, IsAffineGeomPlace k N v) (hT₂aff : ∀ v ∈ T₂, IsAffineGeomPlace k N v)
    (hT₁sm : ∀ v ∈ T₁, ∃ c : k × k, IsCentreOf k N c v ∧
      (∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = v) ∧
      (v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.1) = 1 ∨
        v.ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.2) = 1))
    (hT₂sm : ∀ v ∈ T₂, ∃ c : k × k, IsCentreOf k N c v ∧
      (∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = v) ∧
      (v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.1) = 1 ∨
        v.ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.2) = 1))
    (hgp₁ : ∀ h : ↥(modularFunctionFieldC k N),
      (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) →
      (∀ w ∈ W, w.HasValue h 0) → h = 0)
    (hgp₂ : ∀ h : ↥(modularFunctionFieldC k N),
      (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) →
      ∃ c : k, h = algebraMap k ↥(modularFunctionFieldC k N) c)
    (hdeg : d₁ + d₂ = genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hQ₁' : ∀ i, P.IsStrictFst (Q₁' i)) (hQ₂' : ∀ j, P.IsStrictSnd (Q₂' j))
    (hred₁ : ∀ i, P.reduceFst (Q₁' i) = P.reduceFst (Q₁ i))
    (hred₂ : ∀ j, P.reduceSnd (Q₂' j) = P.reduceSnd (Q₂ j))
    (Qs : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hQs : P.IsStrictFst Qs)
    (hQs' : ∀ i, P.reduceFst Qs ≠ P.reduceFst (Q₁ i))
    (m : ℕ) (hm : (m : k) ≠ 0) :
    ∃ (h : Fin (m * (d₁ + d₂) - (d₁ + d₂) + 1) → ↥(modularFunctionFieldBar (N * q)))
      (h₁ : ∀ l, h l ∈ R.R₁.integers) (h₂ : ∀ l, h l ∈ R.R₂.integers),
      h 0 = 1 ∧
      (∀ l, h l ≠ 0) ∧
      (∀ l (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
        -(((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) :
                Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V)
            + ((m : ℤ) - 1) * ((∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) :
                Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V)) ≤ V.ord (h l)) ∧
      (∀ l,
        (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₁ → 0 ≤ v.ord (R.residue₁ ⟨h l, h₁ l⟩ : ↥(modularFunctionFieldC k N))) ∧
        (∀ v ∈ T₁, -(m : ℤ) ≤ v.ord (R.residue₁ ⟨h l, h₁ l⟩ : ↥(modularFunctionFieldC k N))) ∧
        (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₂ → 0 ≤ v.ord (R.residue₂ ⟨h l, h₂ l⟩ : ↥(modularFunctionFieldC k N))) ∧
        (∀ v ∈ T₂, -(m : ℤ) ≤ v.ord (R.residue₂ ⟨h l, h₂ l⟩ : ↥(modularFunctionFieldC k N))) ∧
        (∀ w ∈ W, ∃ c : k, w.HasValue (R.residue₁ ⟨h l, h₁ l⟩ : ↥(modularFunctionFieldC k N)) c ∧
          (arithFrobC q k N • w).HasValue (R.residue₂ ⟨h l, h₂ l⟩ : ↥(modularFunctionFieldC k N)) c)) ∧
      LinearIndependent k (fun l =>
        ((R.residue₁ ⟨h l, h₁ l⟩ : ↥(modularFunctionFieldC k N)), (R.residue₂ ⟨h l, h₂ l⟩ : ↥(modularFunctionFieldC k N)))) :=
  IntBasis.intbasis P hqN hW R hR hRL hNV hO Q₁ Q₂ hQ₁ hQ₂ hinj₁ hinj₂ hT₁ hT₂ hT₁aff hT₂aff hdeg Q₁' Q₂'
    hQ₁' hQ₂' hred₁ hred₂ m hm

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_linearIndependent_residue_pair_riemannRochSpace_add_nsmul
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_linearIndependent_residue_pair_riemannRochSpace_add_nsmul (solution)
