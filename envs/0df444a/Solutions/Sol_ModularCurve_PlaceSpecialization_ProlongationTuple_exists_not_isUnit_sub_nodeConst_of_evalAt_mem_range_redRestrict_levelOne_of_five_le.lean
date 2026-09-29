-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_not_isUnit_sub_nodeConst_of_evalAt_mem_range_redRestrict_levelOne_of_five_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/604f2494-0c6e-53c9-873a-f5af5d6f9c5f

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_and_hasValue_nodeResidueFst_of_hasValue
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_range_redRestrict_of_hasValue_nodeResidueFst_levelOne_of_five_le
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_not_isUnit_sub_nodeConst_of_evalAt_mem_range_redRestrict_levelOne_of_five_le
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆"
p2m_attr_erase "simp" "TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.NodeLocalized.coe_modularEvalAt AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.ProjectiveLine.map_mk AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul"
p2m_attr_erase "simp" "AdicCompletion.stabilizerToCompletionAut_of ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply"
p2m_attr_erase "simp" "ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace HresGlue

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

section Generic
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem hasValue_sub_algebraMap (W : Place K F) (f : F) (b c : K) (hb : W.HasValue f b) :
    W.HasValue (f - algebraMap K F c) (b - c) := by
  obtain ⟨hmem, hres⟩ := hb
  refine ⟨sub_mem hmem (W.algebraMap_mem' c), ?_⟩
  have : (⟨f - algebraMap K F c, sub_mem hmem (W.algebraMap_mem' c)⟩ : W.toValuationSubring)
      = ⟨f, hmem⟩ - algebraMap K W.toValuationSubring c := by
    apply Subtype.ext; simp [AlgebraicCurve.Place.coe_algebraMap]
  rw [this, map_sub, hres, AlgebraicCurve.Place.residue_algebraMap, map_sub]

theorem hasValue_add_algebraMap (W : Place K F) (f : F) (b c : K) (hb : W.HasValue f b) :
    W.HasValue (f + algebraMap K F c) (b + c) := by
  have h := hasValue_sub_algebraMap W f b (-c) hb
  rwa [map_neg, sub_neg_eq_add, sub_neg_eq_add] at h

theorem ord_pos_of_hasValue_zero (W : Place K F) {f : F} (h : W.HasValue f 0) (hf : f ≠ 0) : 0 < W.ord f := by
  obtain ⟨hm, hr⟩ := h
  have h0 : 0 ≤ W.ord f := W.ord_nonneg_of_mem hm
  rcases h0.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨hm', hu⟩ := W.exists_isUnit_of_ord_eq_zero hf heq.symm
    have hres : IsLocalRing.residue W.toValuationSubring ⟨f, hm'⟩ = 0 := by
      have e : (⟨f, hm'⟩ : W.toValuationSubring) = ⟨f, hm⟩ := rfl
      rw [e, hr, map_zero]
    exact ((IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu) hres

end Generic

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

theorem ι_algebraMap (R : ProlongationTuple P) (x : ResidueField A) :
    R.ι (algebraMap (ResidueField A) (↥(modularFunctionFieldFullC (ResidueField A) N)) x)
      = algebraMap k (↥(modularFunctionFieldC k N)) (R.redBar x) := by
  apply Subtype.ext
  rw [R.ι_coe]
  change coeffMap R.redBar (algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) x)
    = algebraMap k (LaurentSeries k) (R.redBar x)
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem residue₁_const (R : ProlongationTuple P) (a : A) (h : algebraMap (AlgebraicClosure ℚ) (↥(modularFunctionFieldBar (N * q))) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers) :
    (R.residue₁ ⟨algebraMap (AlgebraicClosure ℚ) (↥(modularFunctionFieldBar (N * q))) (a : AlgebraicClosure ℚ), h⟩ : ↥(modularFunctionFieldC k N)) = algebraMap k (↥(modularFunctionFieldC k N)) (red a) := by
  have e : (⟨algebraMap (AlgebraicClosure ℚ) (↥(modularFunctionFieldBar (N * q))) (a : AlgebraicClosure ℚ), h⟩ : R.R₁.integers)
      = ⟨algebraMap (AlgebraicClosure ℚ) (↥(modularFunctionFieldBar (N * q))) (a : AlgebraicClosure ℚ), (R.R₁.algebraMap_mem_iff _).mpr a.2⟩ := rfl
  rw [ProlongationTuple.residue₁_apply, e, R.R₁.residue_algebraMap a, ι_algebraMap, R.redBar_residue]

theorem residue₂_const (R : ProlongationTuple P) (a : A) (h : algebraMap (AlgebraicClosure ℚ) (↥(modularFunctionFieldBar (N * q))) (a : AlgebraicClosure ℚ) ∈ R.R₂.integers) :
    (R.residue₂ ⟨algebraMap (AlgebraicClosure ℚ) (↥(modularFunctionFieldBar (N * q))) (a : AlgebraicClosure ℚ), h⟩ : ↥(modularFunctionFieldC k N)) = algebraMap k (↥(modularFunctionFieldC k N)) (red a) := by
  have e : (⟨algebraMap (AlgebraicClosure ℚ) (↥(modularFunctionFieldBar (N * q))) (a : AlgebraicClosure ℚ), h⟩ : R.R₂.integers)
      = ⟨algebraMap (AlgebraicClosure ℚ) (↥(modularFunctionFieldBar (N * q))) (a : AlgebraicClosure ℚ), (R.R₂.algebraMap_mem_iff _).mpr a.2⟩ := rfl
  rw [ProlongationTuple.residue₂_apply, e, R.R₂.residue_algebraMap a, ι_algebraMap, R.redBar_residue]

end HresGlue

open HresGlue in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hq : 5 ≤ q)
    (hord : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k 1))) (hW : ∀ w ∈ W, w ∈ ssPlaces q 1 k)
    (hreg : R.RegularityLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hV : P.reduceFst V = w)
    (hKres : w.evalAt (jGeomGen k 1) ∈ Set.range (NodeLocalized.redRestrict red K))
    (g : ↥(R.nodeIntegersOver K w)) :
    ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o) := by
  classical
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) :=
    hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * q)
  have hqN : ¬ q ∣ 1 := fun h => (Fact.out : q.Prime).ne_one (Nat.dvd_one.mp h)
  have hssw : w ∈ ssPlaces q 1 k := hW w hw
  have hfix := frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed k 1 hqN data hKr w hssw
  have hrat : V.IsRational := (Place.isRational_iff_deg_eq_one V).mpr (deg_eq_one_modularFunctionFieldBar (1 * q) V)

  have hgN : (g : ↥(modularFunctionFieldBar (1 * q))) ∈ R.nodeIntegers w := R.nodeIntegersOver_le K w g.2
  have hgV : (g : ↥(modularFunctionFieldBar (1 * q))) ∈ V.toValuationSubring := R.mem_toValuationSubring_of_mem_nodeIntegers hgN hV
  have hgval : V.HasValue (g : ↥(modularFunctionFieldBar (1 * q))) (V.evalAt (g : ↥(modularFunctionFieldBar (1 * q)))) := ⟨hgV, (Place.algebraMap_evalAt V hrat hgV).symm⟩
  obtain ⟨hcA, hres⟩ := mem_and_hasValue_nodeResidueFst_of_hasValue R hord W hW hreg w hw hfix (g : ↥(modularFunctionFieldBar (1 * q))) hgN V hV _ hgval

  obtain ⟨o, ho⟩ := mem_range_redRestrict_of_hasValue_nodeResidueFst_levelOne_of_five_le R hq K w hssw hKres g _ hres
  refine ⟨o, ?_⟩

  rintro ⟨u, hu⟩
  have hvN : ((↑u⁻¹ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))) ∈ R.nodeIntegers w :=
    R.nodeIntegersOver_le K w (↑u⁻¹ : ↥(R.nodeIntegersOver K w)).2
  have hdN : ((g - R.nodeConst K w o : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))) ∈ R.nodeIntegers w :=
    R.nodeIntegersOver_le K w (g - R.nodeConst K w o).2
  have hprod : (g - R.nodeConst K w o) * (↑u⁻¹ : ↥(R.nodeIntegersOver K w)) = 1 := by
    rw [← hu, Units.mul_inv]

  have hres1 : (R.nodeResidue₁ w ⟨((g - R.nodeConst K w o : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))), hdN⟩ : ↥(modularFunctionFieldC k 1))
      * (R.nodeResidue₁ w ⟨((↑u⁻¹ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))), hvN⟩ : ↥(modularFunctionFieldC k 1)) = 1 := by
    rw [← map_mul]
    have e1 : (⟨((g - R.nodeConst K w o : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))), hdN⟩ : ↥(R.nodeIntegers w))
        * ⟨((↑u⁻¹ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))), hvN⟩ = 1 := by
      apply Subtype.ext
      have hc := congrArg (fun s : ↥(R.nodeIntegersOver K w) => (s : ↥(modularFunctionFieldBar (1 * q)))) hprod
      simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at hc ⊢
      exact hc
    rw [e1, map_one]

  have hval0 : w.HasValue (R.nodeResidue₁ w ⟨((g - R.nodeConst K w o : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))), hdN⟩ : ↥(modularFunctionFieldC k 1)) 0 := by
    have hoI : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) ((⟨(o : AlgebraicClosure ℚ), o.2.1⟩ : A) : AlgebraicClosure ℚ)
        ∈ R.R₁.integers := (R.R₁.algebraMap_mem_iff _).mpr o.2.1
    have e : (⟨((g - R.nodeConst K w o : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))), hdN⟩ : ↥(R.nodeIntegers w))
        = ⟨(g : ↥(modularFunctionFieldBar (1 * q))), hgN⟩ - ⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (o : AlgebraicClosure ℚ),
            R.algebraMap_mem_nodeIntegers w ⟨(o : AlgebraicClosure ℚ), o.2.1⟩⟩ := by
      apply Subtype.ext
      simp only [AddSubgroupClass.coe_sub]
      rfl
    rw [e, map_sub]
    have hc : (R.nodeResidue₁ w ⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (o : AlgebraicClosure ℚ),
        R.algebraMap_mem_nodeIntegers w ⟨(o : AlgebraicClosure ℚ), o.2.1⟩⟩ : ↥(modularFunctionFieldC k 1))
        = algebraMap k ↥(modularFunctionFieldC k 1) (red ⟨(o : AlgebraicClosure ℚ), o.2.1⟩) :=
      residue₁_const R ⟨(o : AlgebraicClosure ℚ), o.2.1⟩ hoI
    rw [hc]
    have h := hasValue_sub_algebraMap w _ _ (red ⟨(o : AlgebraicClosure ℚ), o.2.1⟩) hres
    have hro : red ⟨(o : AlgebraicClosure ℚ), o.2.1⟩ = NodeLocalized.redRestrict red K o := rfl
    have hz : red ⟨V.evalAt (g : ↥(modularFunctionFieldBar (1 * q))), hcA⟩ - red ⟨(o : AlgebraicClosure ℚ), o.2.1⟩ = 0 := by
      rw [hro, ho, sub_self]
    rw [hz] at h
    exact h

  have hvV : ((↑u⁻¹ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))) ∈ V.toValuationSubring :=
    R.mem_toValuationSubring_of_mem_nodeIntegers hvN hV
  have hvval : V.HasValue ((↑u⁻¹ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q)))
      (V.evalAt ((↑u⁻¹ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q)))) := ⟨hvV, (Place.algebraMap_evalAt V hrat hvV).symm⟩
  obtain ⟨hβA, hβ⟩ := mem_and_hasValue_nodeResidueFst_of_hasValue R hord W hW hreg w hw hfix _ hvN V hV _ hvval
  have hmul := hval0.mul hβ
  rw [hres1, zero_mul] at hmul
  exact zero_ne_one ((w.hasValue_one).unique hmul).symm

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_not_isUnit_sub_nodeConst_of_evalAt_mem_range_redRestrict_levelOne_of_five_le
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_not_isUnit_sub_nodeConst_of_evalAt_mem_range_redRestrict_levelOne_of_five_le (solution)
