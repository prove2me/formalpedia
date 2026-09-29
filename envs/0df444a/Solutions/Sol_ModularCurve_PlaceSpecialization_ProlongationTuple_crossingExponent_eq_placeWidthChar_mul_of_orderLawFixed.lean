-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.crossingExponent_eq_placeWidthChar_mul_of_orderLawFixed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/12335879-a3d8-515f-a691-b9e7cf73b3bb

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_PlaceWidthChar
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_crossingExponent_eq_placeWidth_mul_of_orderLawFixed
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_pair_nodeIntegersOver_ord_eq_placeRamificationJ_of_crossingPresentation
import Theorems.Thm_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_q_eq_two
import Theorems.Thm_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_q_eq_three
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_two
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_three
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidthChar_two_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidthChar_three_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_crossingExponent_eq_placeWidthChar_mul_of_orderLawFixed
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero"
p2m_attr_erase "simp" "ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.NodeLocalized.coe_modularEvalAt AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of"
p2m_attr_erase "simp" "AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of ModularCurve.crossingCoord_apply ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.cuspCount_one"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply"
set_option autoImplicit false
open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace SolXCd42

section Generic

variable {L F : Type*} [Field L] [Field F] [Algebra L F]

private theorem eq_two_or_eq_three {q : ℕ} (hp : q.Prime) (h : q < 5) : q = 2 ∨ q = 3 := by
  interval_cases q
  · exact absurd hp (by decide)
  · exact absurd hp (by decide)
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd hp (by decide)

private theorem autWeight_two_zero : autWeight 2 0 = 12 := by decide

private theorem autWeight_three_zero : autWeight 3 0 = 6 := by decide

private theorem eq_div_mul {r E n e : ℕ} (hdvd : r ∣ n) (hn : n ≠ 0) (h : r * E = n * e) : E = n / r * e := by
  obtain ⟨m, rfl⟩ := hdvd
  have hr : 0 < r := Nat.pos_of_ne_zero (fun h0 => hn (by rw [h0, zero_mul]))
  rw [Nat.mul_div_cancel_left m hr]
  rw [mul_assoc] at h
  exact Nat.eq_of_mul_eq_mul_left hr h

private theorem eq_of_pow_mul_eq {S : Type*} [CommRing S] [IsDomain S] {p : S} (hp0 : p ≠ 0) (hp : ¬ IsUnit p)
    {a b : ℕ} {e e' : S} (he : IsUnit e) (he' : IsUnit e') (h : p ^ a * e = p ^ b * e') : a = b := by
  suffices key : ∀ {a b : ℕ} {e e' : S}, IsUnit e → IsUnit e' → p ^ a * e = p ^ b * e' → a ≤ b → a = b by
    rcases le_total a b with hab | hab
    · exact key he he' h hab
    · exact (key he' he h.symm hab).symm
  intro a b e e' he he' h hab
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rfl
  · exfalso
    have h1 : p ^ a * e = p ^ a * (p ^ d * e') := by rw [h, pow_add, mul_assoc]
    have h2 : e = p ^ d * e' := mul_left_cancel₀ (pow_ne_zero a hp0) h1
    have hdvd : p ∣ e := ⟨p ^ (d - 1) * e', by
      rw [h2, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hd]⟩
    exact hp (isUnit_of_dvd_unit hdvd he)

private theorem val_eq_pow (O : ValuationSubring F) {x y p u : F} {E : ℕ}
    (h : x * y = p ^ E * u) (hy : O.valuation y = 1) (hu : O.valuation u = 1) :
    O.valuation x = O.valuation p ^ E := by
  have h1 := congrArg (fun z => O.valuation z) h
  simp only [map_mul, map_pow, hy, hu, mul_one] at h1
  exact h1

private theorem val_eq_one_of_mul_eq_one (O : ValuationSubring F) {u v : F} (hu : u ∈ O) (hv : v ∈ O)
    (h : u * v = 1) : O.valuation u = 1 := by
  have hu1 : O.valuation u ≤ 1 := (O.valuation_le_one_iff u).mpr hu
  have hv1 : O.valuation v ≤ 1 := (O.valuation_le_one_iff v).mpr hv
  have hprod : O.valuation u * O.valuation v = 1 := by rw [← map_mul, h, map_one]
  refine le_antisymm hu1 ?_
  calc (1 : _) = O.valuation u * O.valuation v := hprod.symm
    _ ≤ O.valuation u * 1 := mul_le_mul_right hv1 _
    _ = O.valuation u := mul_one _

private theorem div_mem_maximalIdeal (O : ValuationSubring F) {p x x' : F} {a b : ℕ}
    (hp0 : O.valuation p ≠ 0) (hp1 : O.valuation p < 1)
    (hx : O.valuation x = O.valuation p ^ a) (hx' : O.valuation x' = O.valuation p ^ b) (hlt : b < a) :
    ∃ h : x / x' ∈ O, (⟨x / x', h⟩ : O) ∈ IsLocalRing.maximalIdeal O := by
  have hval : O.valuation (x / x') = O.valuation p ^ (a - b) := by
    rw [map_div₀, hx, hx', pow_sub₀ _ hp0 hlt.le, div_eq_mul_inv]
  have hlt1 : O.valuation (x / x') < 1 := by
    rw [hval]
    exact pow_lt_one₀ zero_le' hp1 (Nat.sub_ne_zero_of_lt hlt)
  have hmem : x / x' ∈ O := (O.valuation_le_one_iff _).mp hlt1.le
  exact ⟨hmem, (O.valuation_lt_one_iff ⟨x / x', hmem⟩).mpr hlt1⟩

private theorem ord_eq_zero_of_mem_of_inv_mem (V : Place L F) {f : F}
    (hf : f ∈ V.toValuationSubring) (hfi : f⁻¹ ∈ V.toValuationSubring) : V.ord f = 0 := by
  have h1 := V.ord_nonneg_of_mem hf
  have h2 := V.ord_nonneg_of_mem hfi
  rw [V.ord_inv] at h2
  omega

private theorem ord_eq_zero_of_mul_eq (V : Place L F) {x y p u : F} {E : ℕ} (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hp0 : p ≠ 0) (hu0 : u ≠ 0) (h : x * y = p ^ E * u) (hp : V.ord p = 0) (hu : V.ord u = 0)
    (hx : 0 ≤ V.ord x) (hy : 0 ≤ V.ord y) : V.ord x = 0 := by
  have h1 := congrArg (fun z => V.ord z) h
  beta_reduce at h1
  rw [V.ord_mul hx0 hy0, V.ord_mul (pow_ne_zero E hp0) hu0, ← zpow_natCast, V.ord_zpow, hp, hu] at h1
  omega

private theorem ord_ne_zero_of_hasValue_zero (V : Place L F) {g : F} (hg : g ≠ 0) (h : V.HasValue g 0) :
    V.ord g ≠ 0 := by
  intro h0
  obtain ⟨hm, hu⟩ := V.exists_isUnit_of_ord_eq_zero hg h0
  obtain ⟨hm', hres⟩ := h
  rw [map_zero] at hres
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu hres

end Generic

section Frame

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

private theorem resFst_ne (R : ProlongationTuple P) (w : Place k (modularFunctionFieldC k N))
    {f : ↥(modularFunctionFieldBar (N * q))} (hf : f ∈ R.nodeIntegers w)
    (h : R.nodeResidue₁ w ⟨f, hf⟩ ≠ 0) : R.R₁.residue ⟨f, hf.1⟩ ≠ 0 := by
  intro h0
  apply h
  show R.ι (R.R₁.residue ⟨f, hf.1⟩) = 0
  rw [h0, map_zero]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

private theorem resSnd_ne (R : ProlongationTuple P) (w : Place k (modularFunctionFieldC k N))
    {f : ↥(modularFunctionFieldBar (N * q))} (hf : f ∈ R.nodeIntegers w)
    (h : R.nodeResidue₂ w ⟨f, hf⟩ ≠ 0) : R.R₂.residue ⟨f, hf.2.1⟩ ≠ 0 := by
  intro h0
  apply h
  show R.ι (R.R₂.residue ⟨f, hf.2.1⟩) = 0
  rw [h0, map_zero]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

private theorem unit_facts (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) {u : ↥(R.nodeIntegersOver K w)} (hu : IsUnit u) :
    R.R₁.integers.valuation (u : ↥(modularFunctionFieldBar (N * q))) = 1 ∧
      (u : ↥(modularFunctionFieldBar (N * q))) ≠ 0 ∧
      ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
        V.ord (u : ↥(modularFunctionFieldBar (N * q))) = 0 := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hF : (u : ↥(modularFunctionFieldBar (N * q))) * (v : ↥(modularFunctionFieldBar (N * q))) = 1 := by
    have h := congrArg Subtype.val hv
    rw [Subring.coe_mul, Subring.coe_one] at h
    exact h
  have hval := val_eq_one_of_mul_eq_one R.R₁.integers u.2.1.1 v.2.1.1 hF
  refine ⟨hval, fun h0 => ?_, fun V hV => ?_⟩
  · rw [h0, map_zero] at hval
    exact zero_ne_one hval
  · have hinv : (v : ↥(modularFunctionFieldBar (N * q))) = (u : ↥(modularFunctionFieldBar (N * q)))⁻¹ :=
      eq_inv_of_mul_eq_one_right hF
    exact ord_eq_zero_of_mem_of_inv_mem V (u.2.1.2.2 V hV) (hinv ▸ v.2.1.2.2 V hV)

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

private theorem gen_facts (R : ProlongationTuple P)
    (hker : ∀ c : ↥A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal ↥A)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d') :
    (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (ϖ : AlgebraicClosure ℚ) ∈
        R.R₁.integers,
      R.R₁.integers.valuation
          (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (ϖ : AlgebraicClosure ℚ)) ≠ 0 ∧
      R.R₁.integers.valuation
          (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (ϖ : AlgebraicClosure ℚ)) < 1 ∧
      (⟨_, h₁⟩ : R.R₁.integers) ∈ IsLocalRing.maximalIdeal R.R₁.integers) ∧
    ϖ ≠ 0 ∧ ¬ IsUnit ϖ ∧
    algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (ϖ : AlgebraicClosure ℚ) ≠ 0 ∧
    ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      V.ord (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (ϖ : AlgebraicClosure ℚ)) = 0 := by
  have hred0 : NodeLocalized.redRestrict red K ϖ = 0 := (hϖ ϖ).mpr ⟨1, (mul_one ϖ).symm⟩

  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    have hq0 : NodeLocalized.redRestrict red K (q : ↥(NodeLocalized.coeffSubring A K)) = 0 := by
      rw [map_natCast, CharP.cast_eq_zero]
    obtain ⟨d, hd⟩ := (hϖ _).mp hq0
    rw [h0, zero_mul] at hd
    have h1 := congrArg Subtype.val hd
    rw [Subring.coe_natCast, ZeroMemClass.coe_zero, Nat.cast_eq_zero] at h1
    exact (Fact.out : q.Prime).ne_zero h1
  have hϖnu : ¬ IsUnit ϖ := fun hu0 => by
    have h := hu0.map (NodeLocalized.redRestrict red K)
    rw [hred0] at h
    exact not_isUnit_zero h
  have hϖQ0 : (ϖ : AlgebraicClosure ℚ) ≠ 0 := fun h0 => hϖ0 (Subtype.ext (by rw [h0, ZeroMemClass.coe_zero]))
  have hF0 : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (ϖ : AlgebraicClosure ℚ) ≠ 0 :=
    fun h0 => hϖQ0 ((map_eq_zero_iff _ (algebraMap (AlgebraicClosure ℚ)
      ↥(modularFunctionFieldBar (N * q))).injective).mp h0)
  have h₁ : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (ϖ : AlgebraicClosure ℚ) ∈
      R.R₁.integers := (R.R₁.algebraMap_mem_iff (ϖ : AlgebraicClosure ℚ)).mpr ϖ.2.1

  have hredA : red ⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ = 0 := hred0
  have hresA : IsLocalRing.residue ↥A ⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr ((hker _).mp hredA)
  have hres : R.R₁.residue ⟨_, h₁⟩ = 0 := by
    have h := R.R₁.residue_algebraMap ⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩
    rw [hresA, map_zero] at h
    exact h
  have hmax : (⟨_, h₁⟩ : R.R₁.integers) ∈ IsLocalRing.maximalIdeal R.R₁.integers := by
    rw [← R.R₁.ker_residue]
    exact (RingHom.mem_ker).mpr hres
  refine ⟨⟨h₁, (Valuation.ne_zero_iff _).mpr hF0, (R.R₁.integers.valuation_lt_one_iff _).mp hmax, hmax⟩,
    hϖ0, hϖnu, hF0, fun V => ?_⟩
  exact (V.hasValue_algebraMap (ϖ : AlgebraicClosure ℚ)).ord_eq_zero hϖQ0

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

private theorem not_fst_zero_snd_unit (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k]
    (W : Finset (Place k (modularFunctionFieldC k N))) (hreg : R.RegularityLaw W)
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (f : ↥(modularFunctionFieldBar (N * q))) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (hres₁ : R.R₁.residue ⟨f, h₁⟩ = 0)
    (hne : R.residue₂ ⟨f, h₂⟩ ≠ 0) (hord : (arithFrobC q k N • w).ord (R.residue₂ ⟨f, h₂⟩) = 0)
    (hhor : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      P.reduceFst V = w → 0 ≤ V.ord f) : False := by
  obtain ⟨cv, hv₁, hv₂⟩ := hreg.2 f h₁ h₂ (smulNodePair (arithFrobC q k N) w)
    (smulNodePair_mem_nodePairsOfPlaces (arithFrobC q k N) hw) hhor
  have h0 : R.residue₁ ⟨f, h₁⟩ = 0 := by
    show R.ι (R.R₁.residue ⟨f, h₁⟩) = 0
    rw [hres₁, map_zero]
  have hz : w.HasValue (0 : ↥(modularFunctionFieldC k N)) 0 := by
    simpa using w.hasValue_algebraMap (0 : k)
  rw [h0] at hv₁
  have hcv : cv = 0 := hv₁.unique hz
  rw [hcv] at hv₂
  exact ord_ne_zero_of_hasValue_zero _ hne hv₂ hord

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

private theorem caseA (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k]
    (W : Finset (Place k (modularFunctionFieldC k N))) (hreg : R.RegularityLaw W)
    (hker : ∀ c : ↥A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal ↥A)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (c : R.NodeCoordinates K w) (E : ℕ) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u)
    (x' y' u' : ↥(R.nodeIntegersOver K w)) (r E₁ : ℕ) (hu' : IsUnit u')
    (hxy' : x' * y' = R.nodeConst K w ϖ ^ E₁ * u')
    (hx'2 : R.nodeResidue₂ w ⟨x', x'.2.1⟩ ≠ 0)
    (hx'r : (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨x', x'.2.1⟩) = r)
    (hy'1 : R.nodeResidue₁ w ⟨y', y'.2.1⟩ ≠ 0) :
    ¬ E₁ < r * E := by
  intro hlt
  obtain ⟨⟨hp₁, hv0, hv1, -⟩, -, -, hpF0, hordp⟩ := gen_facts R hker K ϖ hϖ
  obtain ⟨hvu, hu0, hordu⟩ := unit_facts R K w hu
  obtain ⟨hvu', hu'0, hordu'⟩ := unit_facts R K w hu'

  have hxyF : (c.x : ↥(modularFunctionFieldBar (N * q))) * (c.y : ↥(modularFunctionFieldBar (N * q))) =
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (ϖ : AlgebraicClosure ℚ) ^ E *
        (u : ↥(modularFunctionFieldBar (N * q))) := by
    have h := congrArg Subtype.val hxy
    rw [Subring.coe_mul, Subring.coe_mul, Subring.coe_pow, coe_nodeConst] at h
    exact h
  have hxyF' : (x' : ↥(modularFunctionFieldBar (N * q))) * (y' : ↥(modularFunctionFieldBar (N * q))) =
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (ϖ : AlgebraicClosure ℚ) ^ E₁ *
        (u' : ↥(modularFunctionFieldBar (N * q))) := by
    have h := congrArg Subtype.val hxy'
    rw [Subring.coe_mul, Subring.coe_mul, Subring.coe_pow, coe_nodeConst] at h
    exact h

  have hxres₂ : R.residue₂ ⟨(c.x : ↥(modularFunctionFieldBar (N * q))), c.x.2.1.2.1⟩ ≠ 0 :=
    c.nodeResidue₂_x_ne_zero
  have hx'res₂ : R.residue₂ ⟨(x' : ↥(modularFunctionFieldBar (N * q))), x'.2.1.2.1⟩ ≠ 0 := hx'2
  have hxs : (arithFrobC q k N • w).ord (R.residue₂ ⟨(c.x : ↥(modularFunctionFieldBar (N * q))), c.x.2.1.2.1⟩)
      = 1 := c.x_snd
  have hx's : (arithFrobC q k N • w).ord (R.residue₂ ⟨(x' : ↥(modularFunctionFieldBar (N * q))), x'.2.1.2.1⟩)
      = r := hx'r
  have hvy : R.R₁.integers.valuation (c.y : ↥(modularFunctionFieldBar (N * q))) = 1 :=
    (ValuationSubring.valuation_eq_one_iff _ ⟨_, c.y.2.1.1⟩).mp
      (R.R₁.isUnit_of_residue_ne_zero (resFst_ne R w c.y.2.1 c.nodeResidue₁_y_ne_zero))
  have hvy' : R.R₁.integers.valuation (y' : ↥(modularFunctionFieldBar (N * q))) = 1 :=
    (ValuationSubring.valuation_eq_one_iff _ ⟨_, y'.2.1.1⟩).mp
      (R.R₁.isUnit_of_residue_ne_zero (resFst_ne R w y'.2.1 hy'1))
  have hxu₂ : IsUnit (⟨(c.x : ↥(modularFunctionFieldBar (N * q))), c.x.2.1.2.1⟩ : R.R₂.integers) :=
    R.R₂.isUnit_of_residue_ne_zero (resSnd_ne R w c.x.2.1 c.nodeResidue₂_x_ne_zero)
  have hx'u₂ : IsUnit (⟨(x' : ↥(modularFunctionFieldBar (N * q))), x'.2.1.2.1⟩ : R.R₂.integers) :=
    R.R₂.isUnit_of_residue_ne_zero (resSnd_ne R w x'.2.1 hx'2)

  have hx0 : (c.x : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := fun h0 =>
    hxres₂ (by rw [show (⟨(c.x : ↥(modularFunctionFieldBar (N * q))), c.x.2.1.2.1⟩ : R.R₂.integers) = 0 from
      Subtype.ext h0, map_zero])
  have hx'0 : (x' : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := fun h0 =>
    hx'res₂ (by rw [show (⟨(x' : ↥(modularFunctionFieldBar (N * q))), x'.2.1.2.1⟩ : R.R₂.integers) = 0 from
      Subtype.ext h0, map_zero])
  have hy0 : (c.y : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hvy
    exact zero_ne_one hvy
  have hy'0 : (y' : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hvy'
    exact zero_ne_one hvy'

  have hvx := val_eq_pow R.R₁.integers hxyF hvy hvu
  have hvx' := val_eq_pow R.R₁.integers hxyF' hvy' hvu'

  have hordx : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
      V.ord (c.x : ↥(modularFunctionFieldBar (N * q))) = 0 := fun V hV =>
    ord_eq_zero_of_mul_eq V hx0 hy0 hpF0 hu0 hxyF (hordp V) (hordu V hV)
      (V.ord_nonneg_of_mem (c.x.2.1.2.2 V hV)) (V.ord_nonneg_of_mem (c.y.2.1.2.2 V hV))
  have hordx' : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
      V.ord (x' : ↥(modularFunctionFieldBar (N * q))) = 0 := fun V hV =>
    ord_eq_zero_of_mul_eq V hx'0 hy'0 hpF0 hu'0 hxyF' (hordp V) (hordu' V hV)
      (V.ord_nonneg_of_mem (x'.2.1.2.2 V hV)) (V.ord_nonneg_of_mem (y'.2.1.2.2 V hV))

  have hxinv : (((hxu₂.unit⁻¹ : (R.R₂.integers)ˣ) : R.R₂.integers) : ↥(modularFunctionFieldBar (N * q))) =
      (c.x : ↥(modularFunctionFieldBar (N * q)))⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    have h := congrArg Subtype.val hxu₂.unit.mul_inv
    rw [IsUnit.unit_spec, MulMemClass.coe_mul, OneMemClass.coe_one] at h
    exact h
  have hx'inv : (((hx'u₂.unit⁻¹ : (R.R₂.integers)ˣ) : R.R₂.integers) : ↥(modularFunctionFieldBar (N * q))) =
      (x' : ↥(modularFunctionFieldBar (N * q)))⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    have h := congrArg Subtype.val hx'u₂.unit.mul_inv
    rw [IsUnit.unit_spec, MulMemClass.coe_mul, OneMemClass.coe_one] at h
    exact h
  have hvxr : R.R₁.integers.valuation ((c.x : ↥(modularFunctionFieldBar (N * q))) ^ r) =
      R.R₁.integers.valuation
        (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (ϖ : AlgebraicClosure ℚ)) ^ (r * E) := by
    rw [map_pow, hvx, ← pow_mul, Nat.mul_comm E r]
  obtain ⟨hρ₁, hρm⟩ := div_mem_maximalIdeal R.R₁.integers hv0 hv1
    (x := (c.x : ↥(modularFunctionFieldBar (N * q))) ^ r) (x' := (x' : ↥(modularFunctionFieldBar (N * q))))
    hvxr hvx' hlt
  have hres₁ : R.R₁.residue ⟨_, hρ₁⟩ = 0 := by
    have hk : (⟨_, hρ₁⟩ : R.R₁.integers) ∈ RingHom.ker R.R₁.residue := by
      rw [R.R₁.ker_residue]
      exact hρm
    exact (RingHom.mem_ker).mp hk
  have hel₂ : (((⟨(c.x : ↥(modularFunctionFieldBar (N * q))), c.x.2.1.2.1⟩ : R.R₂.integers) ^ r *
      ((hx'u₂.unit⁻¹ : (R.R₂.integers)ˣ) : R.R₂.integers) : R.R₂.integers) : ↥(modularFunctionFieldBar (N * q)))
      = (c.x : ↥(modularFunctionFieldBar (N * q))) ^ r / (x' : ↥(modularFunctionFieldBar (N * q))) := by
    rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, hx'inv, div_eq_mul_inv]
  have hρ₂ : (c.x : ↥(modularFunctionFieldBar (N * q))) ^ r / (x' : ↥(modularFunctionFieldBar (N * q))) ∈
      R.R₂.integers := hel₂ ▸ SetLike.coe_mem _
  have hres₂ : R.R₂.residue ⟨_, hρ₂⟩ =
      R.R₂.residue ⟨(c.x : ↥(modularFunctionFieldBar (N * q))), c.x.2.1.2.1⟩ ^ r *
        (R.R₂.residue ⟨(x' : ↥(modularFunctionFieldBar (N * q))), x'.2.1.2.1⟩)⁻¹ := by
    have hel : (⟨_, hρ₂⟩ : R.R₂.integers) =
        (⟨(c.x : ↥(modularFunctionFieldBar (N * q))), c.x.2.1.2.1⟩ : R.R₂.integers) ^ r *
          ((hx'u₂.unit⁻¹ : (R.R₂.integers)ˣ) : R.R₂.integers) := Subtype.ext hel₂.symm
    rw [hel, map_mul, map_pow, map_units_inv, IsUnit.unit_spec]
  have hg : R.residue₂ ⟨_, hρ₂⟩ =
      R.residue₂ ⟨(c.x : ↥(modularFunctionFieldBar (N * q))), c.x.2.1.2.1⟩ ^ r *
        (R.residue₂ ⟨(x' : ↥(modularFunctionFieldBar (N * q))), x'.2.1.2.1⟩)⁻¹ := by
    show R.ι (R.R₂.residue ⟨_, hρ₂⟩) = R.ι (R.R₂.residue _) ^ r * (R.ι (R.R₂.residue _))⁻¹
    rw [hres₂, map_mul, map_pow, map_inv₀]
  have hne : R.residue₂ ⟨_, hρ₂⟩ ≠ 0 := by
    rw [hg]
    exact mul_ne_zero (pow_ne_zero _ hxres₂) (inv_ne_zero hx'res₂)
  have hord : (arithFrobC q k N • w).ord (R.residue₂ ⟨_, hρ₂⟩) = 0 := by
    rw [hg, Place.ord_mul _ (pow_ne_zero _ hxres₂) (inv_ne_zero hx'res₂), ← zpow_natCast, Place.ord_zpow,
      Place.ord_inv, hxs, hx's]
    ring
  have hhor : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
      0 ≤ V.ord ((c.x : ↥(modularFunctionFieldBar (N * q))) ^ r / (x' : ↥(modularFunctionFieldBar (N * q)))) := by
    intro V hV
    rw [div_eq_mul_inv, V.ord_mul (pow_ne_zero _ hx0) (inv_ne_zero hx'0), ← zpow_natCast, V.ord_zpow, V.ord_inv,
      hordx V hV, hordx' V hV]
    simp
  exact not_fst_zero_snd_unit R W hreg w hw _ hρ₁ hρ₂ hres₁ hne hord hhor

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

private theorem caseB (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k]
    (W : Finset (Place k (modularFunctionFieldC k N))) (hreg : R.RegularityLaw W)
    (hker : ∀ c : ↥A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal ↥A)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (c : R.NodeCoordinates K w) (E : ℕ) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u)
    (x' y' u' : ↥(R.nodeIntegersOver K w)) (r E₁ : ℕ) (hu' : IsUnit u')
    (hxy' : x' * y' = R.nodeConst K w ϖ ^ E₁ * u')
    (hx'2 : R.nodeResidue₂ w ⟨x', x'.2.1⟩ ≠ 0)
    (hx'r : (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨x', x'.2.1⟩) = r)
    (hy'1 : R.nodeResidue₁ w ⟨y', y'.2.1⟩ ≠ 0) :
    ¬ r * E < E₁ := by
  intro hgt
  obtain ⟨⟨hp₁, hv0, hv1, -⟩, -, -, hpF0, hordp⟩ := gen_facts R hker K ϖ hϖ
  obtain ⟨hvu, hu0, hordu⟩ := unit_facts R K w hu
  obtain ⟨hvu', hu'0, hordu'⟩ := unit_facts R K w hu'

  have hxyF : (c.x : ↥(modularFunctionFieldBar (N * q))) * (c.y : ↥(modularFunctionFieldBar (N * q))) =
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (ϖ : AlgebraicClosure ℚ) ^ E *
        (u : ↥(modularFunctionFieldBar (N * q))) := by
    have h := congrArg Subtype.val hxy
    rw [Subring.coe_mul, Subring.coe_mul, Subring.coe_pow, coe_nodeConst] at h
    exact h
  have hxyF' : (x' : ↥(modularFunctionFieldBar (N * q))) * (y' : ↥(modularFunctionFieldBar (N * q))) =
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (ϖ : AlgebraicClosure ℚ) ^ E₁ *
        (u' : ↥(modularFunctionFieldBar (N * q))) := by
    have h := congrArg Subtype.val hxy'
    rw [Subring.coe_mul, Subring.coe_mul, Subring.coe_pow, coe_nodeConst] at h
    exact h

  have hxres₂ : R.residue₂ ⟨(c.x : ↥(modularFunctionFieldBar (N * q))), c.x.2.1.2.1⟩ ≠ 0 :=
    c.nodeResidue₂_x_ne_zero
  have hx'res₂ : R.residue₂ ⟨(x' : ↥(modularFunctionFieldBar (N * q))), x'.2.1.2.1⟩ ≠ 0 := hx'2
  have hxs : (arithFrobC q k N • w).ord (R.residue₂ ⟨(c.x : ↥(modularFunctionFieldBar (N * q))), c.x.2.1.2.1⟩)
      = 1 := c.x_snd
  have hx's : (arithFrobC q k N • w).ord (R.residue₂ ⟨(x' : ↥(modularFunctionFieldBar (N * q))), x'.2.1.2.1⟩)
      = r := hx'r
  have hvy : R.R₁.integers.valuation (c.y : ↥(modularFunctionFieldBar (N * q))) = 1 :=
    (ValuationSubring.valuation_eq_one_iff _ ⟨_, c.y.2.1.1⟩).mp
      (R.R₁.isUnit_of_residue_ne_zero (resFst_ne R w c.y.2.1 c.nodeResidue₁_y_ne_zero))
  have hvy' : R.R₁.integers.valuation (y' : ↥(modularFunctionFieldBar (N * q))) = 1 :=
    (ValuationSubring.valuation_eq_one_iff _ ⟨_, y'.2.1.1⟩).mp
      (R.R₁.isUnit_of_residue_ne_zero (resFst_ne R w y'.2.1 hy'1))
  have hxu₂ : IsUnit (⟨(c.x : ↥(modularFunctionFieldBar (N * q))), c.x.2.1.2.1⟩ : R.R₂.integers) :=
    R.R₂.isUnit_of_residue_ne_zero (resSnd_ne R w c.x.2.1 c.nodeResidue₂_x_ne_zero)
  have hx'u₂ : IsUnit (⟨(x' : ↥(modularFunctionFieldBar (N * q))), x'.2.1.2.1⟩ : R.R₂.integers) :=
    R.R₂.isUnit_of_residue_ne_zero (resSnd_ne R w x'.2.1 hx'2)

  have hx0 : (c.x : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := fun h0 =>
    hxres₂ (by rw [show (⟨(c.x : ↥(modularFunctionFieldBar (N * q))), c.x.2.1.2.1⟩ : R.R₂.integers) = 0 from
      Subtype.ext h0, map_zero])
  have hx'0 : (x' : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := fun h0 =>
    hx'res₂ (by rw [show (⟨(x' : ↥(modularFunctionFieldBar (N * q))), x'.2.1.2.1⟩ : R.R₂.integers) = 0 from
      Subtype.ext h0, map_zero])
  have hy0 : (c.y : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hvy
    exact zero_ne_one hvy
  have hy'0 : (y' : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hvy'
    exact zero_ne_one hvy'

  have hvx := val_eq_pow R.R₁.integers hxyF hvy hvu
  have hvx' := val_eq_pow R.R₁.integers hxyF' hvy' hvu'

  have hordx : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
      V.ord (c.x : ↥(modularFunctionFieldBar (N * q))) = 0 := fun V hV =>
    ord_eq_zero_of_mul_eq V hx0 hy0 hpF0 hu0 hxyF (hordp V) (hordu V hV)
      (V.ord_nonneg_of_mem (c.x.2.1.2.2 V hV)) (V.ord_nonneg_of_mem (c.y.2.1.2.2 V hV))
  have hordx' : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
      V.ord (x' : ↥(modularFunctionFieldBar (N * q))) = 0 := fun V hV =>
    ord_eq_zero_of_mul_eq V hx'0 hy'0 hpF0 hu'0 hxyF' (hordp V) (hordu' V hV)
      (V.ord_nonneg_of_mem (x'.2.1.2.2 V hV)) (V.ord_nonneg_of_mem (y'.2.1.2.2 V hV))

  have hxinv : (((hxu₂.unit⁻¹ : (R.R₂.integers)ˣ) : R.R₂.integers) : ↥(modularFunctionFieldBar (N * q))) =
      (c.x : ↥(modularFunctionFieldBar (N * q)))⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    have h := congrArg Subtype.val hxu₂.unit.mul_inv
    rw [IsUnit.unit_spec, MulMemClass.coe_mul, OneMemClass.coe_one] at h
    exact h
  have hx'inv : (((hx'u₂.unit⁻¹ : (R.R₂.integers)ˣ) : R.R₂.integers) : ↥(modularFunctionFieldBar (N * q))) =
      (x' : ↥(modularFunctionFieldBar (N * q)))⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    have h := congrArg Subtype.val hx'u₂.unit.mul_inv
    rw [IsUnit.unit_spec, MulMemClass.coe_mul, OneMemClass.coe_one] at h
    exact h
  have hvxr : R.R₁.integers.valuation ((c.x : ↥(modularFunctionFieldBar (N * q))) ^ r) =
      R.R₁.integers.valuation
        (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (ϖ : AlgebraicClosure ℚ)) ^ (r * E) := by
    rw [map_pow, hvx, ← pow_mul, Nat.mul_comm E r]
  obtain ⟨hρ₁, hρm⟩ := div_mem_maximalIdeal R.R₁.integers hv0 hv1
    (x := (x' : ↥(modularFunctionFieldBar (N * q)))) (x' := (c.x : ↥(modularFunctionFieldBar (N * q))) ^ r)
    hvx' hvxr hgt
  have hres₁ : R.R₁.residue ⟨_, hρ₁⟩ = 0 := by
    have hk : (⟨_, hρ₁⟩ : R.R₁.integers) ∈ RingHom.ker R.R₁.residue := by
      rw [R.R₁.ker_residue]
      exact hρm
    exact (RingHom.mem_ker).mp hk
  have hxrinv : ((((hxu₂.unit ^ r)⁻¹ : (R.R₂.integers)ˣ) : R.R₂.integers) : ↥(modularFunctionFieldBar (N * q))) = ((c.x : ↥(modularFunctionFieldBar (N * q))) ^ r)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    have h := congrArg Subtype.val (hxu₂.unit ^ r).mul_inv
    rw [MulMemClass.coe_mul, OneMemClass.coe_one, Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow,
      IsUnit.unit_spec] at h
    exact h
  have hel₂ : (((⟨(x' : ↥(modularFunctionFieldBar (N * q))), x'.2.1.2.1⟩ : R.R₂.integers) *
      (((hxu₂.unit ^ r)⁻¹ : (R.R₂.integers)ˣ) : R.R₂.integers) : R.R₂.integers) : ↥(modularFunctionFieldBar (N * q)))
      = (x' : ↥(modularFunctionFieldBar (N * q))) / (c.x : ↥(modularFunctionFieldBar (N * q))) ^ r := by
    rw [MulMemClass.coe_mul, hxrinv, div_eq_mul_inv]
  have hρ₂ : (x' : ↥(modularFunctionFieldBar (N * q))) / (c.x : ↥(modularFunctionFieldBar (N * q))) ^ r ∈ R.R₂.integers := hel₂ ▸ SetLike.coe_mem _
  have hres₂ : R.R₂.residue ⟨_, hρ₂⟩ =
      R.R₂.residue ⟨(x' : ↥(modularFunctionFieldBar (N * q))), x'.2.1.2.1⟩ * (R.R₂.residue ⟨(c.x : ↥(modularFunctionFieldBar (N * q))), c.x.2.1.2.1⟩ ^ r)⁻¹ := by
    have hel : (⟨_, hρ₂⟩ : R.R₂.integers) =
        (⟨(x' : ↥(modularFunctionFieldBar (N * q))), x'.2.1.2.1⟩ : R.R₂.integers) * (((hxu₂.unit ^ r)⁻¹ : (R.R₂.integers)ˣ) : R.R₂.integers) :=
      Subtype.ext hel₂.symm
    rw [hel, map_mul, map_units_inv, Units.val_pow_eq_pow_val, map_pow, IsUnit.unit_spec]
  have hg : R.residue₂ ⟨_, hρ₂⟩ =
      R.residue₂ ⟨(x' : ↥(modularFunctionFieldBar (N * q))), x'.2.1.2.1⟩ * (R.residue₂ ⟨(c.x : ↥(modularFunctionFieldBar (N * q))), c.x.2.1.2.1⟩ ^ r)⁻¹ := by
    show R.ι (R.R₂.residue ⟨_, hρ₂⟩) = R.ι (R.R₂.residue _) * (R.ι (R.R₂.residue _) ^ r)⁻¹
    rw [hres₂, map_mul, map_inv₀, map_pow]
  have hne : R.residue₂ ⟨_, hρ₂⟩ ≠ 0 := by
    rw [hg]
    exact mul_ne_zero hx'res₂ (inv_ne_zero (pow_ne_zero _ hxres₂))
  have hord : (arithFrobC q k N • w).ord (R.residue₂ ⟨_, hρ₂⟩) = 0 := by
    rw [hg, Place.ord_mul _ hx'res₂ (inv_ne_zero (pow_ne_zero _ hxres₂)), Place.ord_inv, ← zpow_natCast,
      Place.ord_zpow, hxs, hx's]
    ring
  have hhor : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
      0 ≤ V.ord ((x' : ↥(modularFunctionFieldBar (N * q))) / (c.x : ↥(modularFunctionFieldBar (N * q))) ^ r) := by
    intro V hV
    rw [div_eq_mul_inv, V.ord_mul hx'0 (inv_ne_zero (pow_ne_zero _ hx0)), V.ord_inv, ← zpow_natCast, V.ord_zpow,
      hordx V hV, hordx' V hV]
    simp
  exact not_fst_zero_snd_unit R W hreg w hw _ hρ₁ hρ₂ hres₁ hne hord hhor

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

private theorem mul_eq (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k]
    (W : Finset (Place k (modularFunctionFieldC k N))) (hreg : R.RegularityLaw W)
    (hker : ∀ c : ↥A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal ↥A)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (c : R.NodeCoordinates K w) (E : ℕ) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u)
    (x' y' u' : ↥(R.nodeIntegersOver K w)) (r E₁ : ℕ) (hu' : IsUnit u')
    (hxy' : x' * y' = R.nodeConst K w ϖ ^ E₁ * u')
    (hx'2 : R.nodeResidue₂ w ⟨x', x'.2.1⟩ ≠ 0)
    (hx'r : (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨x', x'.2.1⟩) = r)
    (hy'1 : R.nodeResidue₁ w ⟨y', y'.2.1⟩ ≠ 0) :
    r * E = E₁ := by
  rcases Nat.lt_trichotomy E₁ (r * E) with hlt | heq | hgt
  · exact absurd hlt (caseA R W hreg hker K w hw ϖ hϖ c E u hu hxy x' y' u' r E₁ hu' hxy' hx'2 hx'r hy'1)
  · exact heq.symm
  · exact absurd hgt (caseB R W hreg hker K w hw ϖ hϖ c E u hu hxy x' y' u' r E₁ hu' hxy' hx'2 hx'r hy'1)

end Frame

end SolXCd42

open SolXCd42 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (hmodel : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W) (hord : R.OrderLawFixed)
    (hker : ∀ c : ↥A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal ↥A)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (xw : ↥(NodeLocalized.coeffSubring A K)) (hxw : NodeLocalized.redRestrict red K xw = w.evalAt (jGeomGen k N))
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (eK : ℕ) (ε : ↥(NodeLocalized.coeffSubring A K)) (hε : IsUnit ε)
    (hqe : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
    (c : R.NodeCoordinates K w) (E : ℕ) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u) :
    E = placeWidthChar q N w * eK := by
  by_cases hq5 : 5 ≤ q
  · rw [placeWidthChar_of_five_le hq5 N w]
    exact crossingExponent_eq_placeWidth_mul_of_orderLawFixed R hqN hq5 hmodel W hW hreg hval hord hker K w hw xw hxw ϖ hϖ
      eK ε hε hqe c E u hu hxy
  · have hq23 : q = 2 ∨ q = 3 := eq_two_or_eq_three Fact.out (Nat.lt_of_not_le hq5)
    have hss : w ∈ ssPlaces q N k := hW w hw
    have hamem : w.evalAt (jGeomGen k N) ∈ ssJSet q k :=
      ((isSupersingularPlace_iff q N k w).mp ((mem_ssPlaces_iff q N k).mp hss)).2.2
    have hapow : w.evalAt (jGeomGen k N) ^ (q ^ 2) = w.evalAt (jGeomGen k N) :=
      pow_q_sq_eq_self_of_mem_ssJSet q hamem
    obtain ⟨-, hϖ0, hϖnu, -, -⟩ := gen_facts R hker K ϖ hϖ
    rcases hq23 with rfl | rfl
    ·
      have ha0 : w.evalAt (jGeomGen k N) = 0 := eq_zero_of_mem_ssJSet_two _ hamem hapow
      obtain ⟨eKa, εa, -, hεa, hqa, G', H', w₁, hw₁, hGH, -, -, -, -, -, hGspan, hHspan⟩ :=
        exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_q_eq_two red rfl K ϖ hϖ
      obtain ⟨x', y', u', hu', hxy', -, -, hx'2, hx'r, hy'1, -⟩ :=
        exists_pair_nodeIntegersOver_ord_eq_placeRamificationJ_of_crossingPresentation R hqN W hW hreg K w hw 0
          ha0 ϖ hϖ G' H' (autWeight 2 0 * eKa) w₁ hw₁ hGH hGspan hHspan
      have hmain := mul_eq R W hreg hker K w hw ϖ hϖ c E u hu hxy x' y' u' (placeRamificationJ N w)
        (autWeight 2 0 * eKa) hu' hxy' hx'2 hx'r hy'1
      have heK : eK = eKa := eq_of_pow_mul_eq hϖ0 hϖnu hε hεa (hqe.symm.trans hqa)
      have h12 : autWeight 2 0 = 12 := autWeight_two_zero
      have hj : jWidthChar 2 (w.evalAt (jGeomGen k N)) = 12 := jWidthChar_two_of_eq_zero ha0
      have hdvd : placeRamificationJ N w ∣ 12 :=
        hj ▸ placeRamificationJ_dvd_jWidthChar_two_of_mem_ssPlaces hqN hss
      rw [placeWidthChar_eq_div, hj]
      rw [h12, ← heK] at hmain
      exact eq_div_mul hdvd (by decide) hmain
    ·
      have ha0 : w.evalAt (jGeomGen k N) = 0 := eq_zero_of_mem_ssJSet_three _ hamem hapow
      obtain ⟨eKa, εa, -, hεa, hqa, G', H', w₁, hw₁, hGH, -, -, -, -, -, hGspan, hHspan⟩ :=
        exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_q_eq_three red rfl K ϖ hϖ
      obtain ⟨x', y', u', hu', hxy', -, -, hx'2, hx'r, hy'1, -⟩ :=
        exists_pair_nodeIntegersOver_ord_eq_placeRamificationJ_of_crossingPresentation R hqN W hW hreg K w hw 0
          ha0 ϖ hϖ G' H' (autWeight 3 0 * eKa) w₁ hw₁ hGH hGspan hHspan
      have hmain := mul_eq R W hreg hker K w hw ϖ hϖ c E u hu hxy x' y' u' (placeRamificationJ N w)
        (autWeight 3 0 * eKa) hu' hxy' hx'2 hx'r hy'1
      have heK : eK = eKa := eq_of_pow_mul_eq hϖ0 hϖnu hε hεa (hqe.symm.trans hqa)
      have h6 : autWeight 3 0 = 6 := autWeight_three_zero
      have hj : jWidthChar 3 (w.evalAt (jGeomGen k N)) = 6 := jWidthChar_three_of_eq_zero ha0
      have hdvd : placeRamificationJ N w ∣ 6 :=
        hj ▸ placeRamificationJ_dvd_jWidthChar_three_of_mem_ssPlaces hqN hss
      rw [placeWidthChar_eq_div, hj]
      rw [h6, ← heK] at hmain
      exact eq_div_mul hdvd (by decide) hmain

#print axioms solution

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_crossingExponent_eq_placeWidthChar_mul_of_orderLawFixed
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_crossingExponent_eq_placeWidthChar_mul_of_orderLawFixed (solution)
