-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.splitDatum_of_forall_reduceFst_eq_ord_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/2ce97041-dc53-5146-a399-d072f5899176

import Definitions.Def_ModularCurve_ProlongationTuple
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isCuspidal_of_not_isAffineGeomPlace_reduceFst
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_not_isAffineGeomPlace_reduceFst_of_isCuspidal
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isInftySide_or_isZeroSide_of_isCuspidal
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isInftySide_atkinLehnerBar_smul_iff
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isZeroSide_atkinLehnerBar_smul_iff
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_atkinLehnerBar_smul
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_oneSided
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawZero_oneSided
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_le_ord_residue_and_exists_hasValue_of_mul
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace
import Theorems.Thm_ModularCurve_isAffineGeomPlace_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_splitDatum_of_forall_reduceFst_eq_ord_eq
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ValuationSubring.instIsAlgClosedResidueField AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero"
p2m_attr_erase "simp" "TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one"
p2m_attr_erase "simp" "compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply"
set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization~IsInftySide~IsCuspidal~IsZeroSide~IsCuspidal'"

noncomputable section

namespace W7SplitPort

section PlaceOrder

variable {k Fk : Type*} [Field k] [Field Fk] [Algebra k Fk]

private theorem ord_add_ge (w : Place k Fk) (x y : Fk) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (w.ord x) (w.ord y) ≤ w.ord (x + y) := by
  have h := w.adicValuation.map_add x y
  have hx' := w.adicValuation_ne_zero hx
  have hy' := w.adicValuation_ne_zero hy
  have hxy' := w.adicValuation_ne_zero hxy
  unfold Place.ord
  rcases le_max_iff.mp h with h1 | h1
  · have := WithZero.log_le_log hxy' hx' |>.mpr h1
    refine le_trans (min_le_left _ _) ?_
    omega
  · have := WithZero.log_le_log hxy' hy' |>.mpr h1
    refine le_trans (min_le_right _ _) ?_
    omega

private theorem ord_algebraMap_eq_zero (w : Place k Fk) {c : k} (hc : c ≠ 0) :
    w.ord (algebraMap k Fk c) = 0 := by
  have hu : IsUnit (⟨algebraMap k Fk c, w.algebraMap_mem' c⟩ : w.toValuationSubring) :=
    ⟨⟨⟨algebraMap k Fk c, w.algebraMap_mem' c⟩, ⟨algebraMap k Fk c⁻¹, w.algebraMap_mem' c⁻¹⟩,
      Subtype.ext (by
        show algebraMap k Fk c * algebraMap k Fk c⁻¹ = 1
        rw [← map_mul, mul_inv_cancel₀ hc, map_one]),
      Subtype.ext (by
        show algebraMap k Fk c⁻¹ * algebraMap k Fk c = 1
        rw [← map_mul, inv_mul_cancel₀ hc, map_one])⟩, rfl⟩
  obtain ⟨u, hu'⟩ := hu
  have := w.ord_coe_unit u
  rw [hu'] at this
  exact this

private theorem ord_add_algebraMap_of_ord_neg (w : Place k Fk) {g : Fk} (hg : w.ord g < 0) (c : k) :
    w.ord (g + algebraMap k Fk c) = w.ord g := by
  have hg0 : g ≠ 0 := by rintro rfl; rw [Place.ord_zero] at hg; exact lt_irrefl _ hg
  by_cases hc : c = 0
  · rw [hc, map_zero, add_zero]
  have hc0 : algebraMap k Fk c ≠ 0 := (map_ne_zero _).mpr hc
  have hordc := ord_algebraMap_eq_zero w hc
  have hsum0 : g + algebraMap k Fk c ≠ 0 := by
    intro h
    have : g = -algebraMap k Fk c := eq_neg_of_add_eq_zero_left h
    rw [this, show -algebraMap k Fk c = algebraMap k Fk (-c) by rw [map_neg],
      ord_algebraMap_eq_zero w (neg_ne_zero.mpr hc)] at hg
    exact lt_irrefl _ hg
  apply le_antisymm
  · by_contra hlt
    push Not at hlt
    have h2 := ord_add_ge w (g + algebraMap k Fk c) (algebraMap k Fk (-c)) hsum0
      ((map_ne_zero _).mpr (neg_ne_zero.mpr hc)) (by rw [map_neg, add_neg_cancel_right]; exact hg0)
    rw [map_neg, add_neg_cancel_right, ← map_neg,
      ord_algebraMap_eq_zero w (neg_ne_zero.mpr hc)] at h2
    have : min (w.ord (g + algebraMap k Fk c)) 0 ≤ w.ord g := h2
    rw [min_le_iff] at this
    rcases this with h | h <;> omega
  · have h1 := ord_add_ge w g (algebraMap k Fk c) hg0 hc0 hsum0
    rw [hordc, min_eq_left (le_of_lt hg)] at h1
    exact h1

private theorem ord_add_algebraMap_ge_of_ge (w : Place k Fk) {g : Fk} {n : ℤ} (hn : n ≤ 0)
    (hg : g = 0 ∨ n ≤ w.ord g) (c : k) :
    g + algebraMap k Fk c = 0 ∨ n ≤ w.ord (g + algebraMap k Fk c) := by
  by_cases h0 : g + algebraMap k Fk c = 0
  · exact Or.inl h0
  right
  by_cases hneg : w.ord (g + algebraMap k Fk c) < 0
  · have := ord_add_algebraMap_of_ord_neg w hneg (-c)
    rw [map_neg, add_neg_cancel_right] at this
    rcases hg with rfl | hg
    · rw [zero_add, ord_algebraMap_eq_zero w (by
        intro hc; apply h0; rw [hc, map_zero, add_zero])] at hneg
      exact absurd hneg (lt_irrefl 0)
    · rw [this] at hg; exact hg
  · push Not at hneg; exact hn.trans hneg

end PlaceOrder

section Upstairs

variable {L : Type*} [Field L] {A : ValuationSubring L}
  {F : Type*} [Field F] [Algebra L F]
  {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]

private theorem algebraMap_mem_riemannRochSpace {E : Divisor L F} (hE : ∀ W, 0 ≤ E W) (c : L) :
    algebraMap L F c ∈ riemannRochSpace E := by
  rw [mem_riemannRochSpace_iff]
  intro W
  by_cases hc : c = 0
  · left; rw [hc, map_zero]
  · right
    rw [ord_algebraMap_eq_zero W hc]
    have := hE W
    omega

private theorem algebraMap_mem_integers (R : RegularProlongation A F Fb) (a : A) :
    algebraMap L F (a : L) ∈ R.integers :=
  (R.algebraMap_mem_iff _).mpr a.2

private theorem residue_add_algebraMap (R : RegularProlongation A F Fb) {f : F} (hf : f ∈ R.integers)
    (a : A) :
    R.residue ⟨f + algebraMap L F (a : L), add_mem hf (algebraMap_mem_integers R a)⟩
      = R.residue ⟨f, hf⟩ + algebraMap (ResidueField A) Fb (IsLocalRing.residue A a) := by
  have : (⟨f + algebraMap L F (a : L), add_mem hf (algebraMap_mem_integers R a)⟩ : R.integers)
      = ⟨f, hf⟩ + ⟨_, algebraMap_mem_integers R a⟩ := rfl
  rw [this, map_add, R.residue_algebraMap a]

private theorem exists_add_algebraMap_residue_ne_zero [Infinite (ResidueField A)]
    (R₁ R₂ : RegularProlongation A F Fb) {f : F} (h₁ : f ∈ R₁.integers) (h₂ : f ∈ R₂.integers) :
    ∃ a : A, R₁.residue ⟨f + algebraMap L F (a : L), add_mem h₁ (algebraMap_mem_integers R₁ a)⟩ ≠ 0 ∧
             R₂.residue ⟨f + algebraMap L F (a : L), add_mem h₂ (algebraMap_mem_integers R₂ a)⟩ ≠ 0 := by
  classical
  set r₁ := R₁.residue ⟨f, h₁⟩
  set r₂ := R₂.residue ⟨f, h₂⟩
  obtain ⟨x, hx⟩ : ∃ x : ResidueField A,
      x ∉ ({y | algebraMap _ Fb y = -r₁} ∪ {y | algebraMap _ Fb y = -r₂}) := by
    have hfin : Set.Finite ({y : ResidueField A | algebraMap _ Fb y = -r₁} ∪ {y | algebraMap _ Fb y = -r₂}) := by
      refine Set.Finite.union ?_ ?_ <;>
      · refine Set.Subsingleton.finite ?_
        intro y hy y' hy'
        exact (algebraMap (ResidueField A) Fb).injective (hy.trans hy'.symm)
    exact hfin.infinite_compl.nonempty
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  refine ⟨a, ?_, ?_⟩
  · rw [residue_add_algebraMap R₁ h₁ a]
    intro h
    exact hx (Or.inl (eq_neg_of_add_eq_zero_right h))
  · rw [residue_add_algebraMap R₂ h₂ a]
    intro h
    exact hx (Or.inr (eq_neg_of_add_eq_zero_right h))

end Upstairs

section FinsuppTools

variable {α β : Type*}

private theorem mapDomain_neg (f : α → β) (E : α →₀ ℤ) :
    Finsupp.mapDomain f (-E) = -Finsupp.mapDomain f E :=
  map_neg (Finsupp.mapDomain.addMonoidHom f) E

private theorem neg_mapDomain_apply_le (f : α → β) {D E : α →₀ ℤ} (h : -E ≤ D) (v : β) :
    -(Finsupp.mapDomain f E v) ≤ Finsupp.mapDomain f D v := by
  have := Finsupp.le_def.mp (Finsupp.mapDomain_mono (f := f) h) v
  rwa [mapDomain_neg, Finsupp.coe_neg, Pi.neg_apply] at this

private theorem filter_le_filter (p : α → Prop) [DecidablePred p] {D E : α →₀ ℤ} (h : D ≤ E) :
    D.filter p ≤ E.filter p := by
  intro a
  rw [Finsupp.filter_apply, Finsupp.filter_apply]
  split_ifs
  · exact h a
  · exact le_rfl

private theorem filter_neg (p : α → Prop) [DecidablePred p] (E : α →₀ ℤ) :
    (-E).filter p = -E.filter p := by
  ext a
  simp only [Finsupp.filter_apply, Finsupp.coe_neg, Pi.neg_apply]
  split_ifs <;> simp

private theorem neg_mapDomain_filter_apply_le (f : α → β) (p : α → Prop) [DecidablePred p]
    {D E : α →₀ ℤ} (h : -E ≤ D) (v : β) :
    -(Finsupp.mapDomain f (E.filter p) v) ≤ Finsupp.mapDomain f (D.filter p) v := by
  apply neg_mapDomain_apply_le
  rw [← filter_neg]
  exact filter_le_filter p h

private theorem mapDomain_apply_eq_sum_filter [DecidableEq β] (f : α → β) (D : α →₀ ℤ) (v : β) :
    Finsupp.mapDomain f D v = ∑ W ∈ D.support.filter (fun W => f W = v), D W := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum, Finsupp.finsetSum_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [Finsupp.single_apply]

private theorem mapDomain_apply_eq_zero_of_forall [DecidableEq β] (f : α → β) (D : α →₀ ℤ) (v : β)
    (h : ∀ W ∈ D.support, f W ≠ v) : Finsupp.mapDomain f D v = 0 := by
  rw [mapDomain_apply_eq_sum_filter]
  refine Finset.sum_eq_zero fun W hW => ?_
  rw [Finset.mem_filter] at hW
  exact absurd hW.2 (h W hW.1)

private theorem mapDomain_nonneg_apply (f : α → β) {D : α →₀ ℤ} (hD : ∀ a, 0 ≤ D a) (v : β) :
    0 ≤ Finsupp.mapDomain f D v := by
  classical
  rw [mapDomain_apply_eq_sum_filter]
  exact Finset.sum_nonneg fun W _ => hD W

private theorem sum_mapDomain_id (f : α → β) (D : α →₀ ℤ) :
    (Finsupp.mapDomain f D).sum (fun _ n => n) = D.sum (fun _ n => n) :=
  Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

private theorem filter_eq_zero_of_nonneg (D : α →₀ ℤ) (hD : ∀ a, 0 ≤ D a) (p : α → Prop)
    [DecidablePred p]
    (hp : ∀ a, p a ↔ D a < 0) : D.filter p = 0 := by
  rw [Finsupp.filter_eq_zero_iff]
  intro a ha
  have := hD a
  have h2 := (hp a).mp ha
  omega

private theorem filter_eq_self_of_nonneg (D : α →₀ ℤ) (hD : ∀ a, 0 ≤ D a) (p : α → Prop)
    [DecidablePred p]
    (hp : ∀ a, p a ↔ 0 < D a) : D.filter p = D := by
  rw [Finsupp.filter_eq_self_iff]
  intro a ha
  rw [hp]
  have := hD a
  omega

end FinsuppTools

section RR

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem neg_le_of_mem_riemannRochSpace {E D : Divisor K F} {f : F} (hf : f ∈ riemannRochSpace E)
    (hf0 : f ≠ 0) (hD : ∀ W, D W = W.ord f) : -E ≤ D := by
  intro W
  rw [Finsupp.coe_neg, Pi.neg_apply, hD W]
  exact ((mem_riemannRochSpace_iff.mp hf) W).resolve_left hf0

private theorem neg_le_ord_of_mem {E : Divisor K F} (hE : ∀ W, 0 ≤ E W) {f : F} (hf : f ∈ riemannRochSpace E)
    (W : Place K F) : -E W ≤ W.ord f := by
  rcases (mem_riemannRochSpace_iff.mp hf) W with h0 | h
  · rw [h0, Place.ord_zero]; have := hE W; omega
  · exact h

private theorem degree_eq_sum_of_deg_eq_one (h : ∀ v : Place K F, v.deg = 1) (D : Divisor K F) :
    Divisor.degree D = D.sum (fun _ n => n) := by
  show Finsupp.liftAddHom (fun v => AddMonoidHom.mulRight ((v.deg : ℕ) : ℤ)) D = _
  rw [Finsupp.liftAddHom_apply]
  refine Finsupp.sum_congr fun v _ => ?_
  rw [AddMonoidHom.mulRight_apply, h v, Nat.cast_one, mul_one]

private theorem degree_eq_sum_support_of_deg_eq_one (h : ∀ v : Place K F, v.deg = 1) (D : Divisor K F) :
    Divisor.degree D = ∑ v ∈ D.support, D v := by
  rw [degree_eq_sum_of_deg_eq_one h]; rfl

private theorem degree_single_of_deg_eq_one (h : ∀ v : Place K F, v.deg = 1) (v : Place K F) (n : ℤ) :
    Divisor.degree (Finsupp.single v n) = n := by
  rw [Divisor.degree_single, h v, Nat.cast_one, mul_one]

private theorem degree_filter_eq_sum (h : ∀ v : Place K F, v.deg = 1) (D : Divisor K F) (p : Place K F → Prop)
    [DecidablePred p] : Divisor.degree (D.filter p) = ∑ v ∈ D.support.filter p, D v := by
  rw [degree_eq_sum_support_of_deg_eq_one h, Finsupp.support_filter]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [Finset.mem_filter] at hv
  rw [Finsupp.filter_apply, if_pos hv.2]

end RR

section Site

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
  {red : A →+* k} {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

local notation "Qb" => AlgebraicClosure ℚ
local notation "FNq" => modularFunctionFieldBar (N * q)
local notation "Ck" => modularFunctionFieldC k N
local notation "Plk" => Place k (modularFunctionFieldC k N)
local notation "PlF" => Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
local notation "φ" => frobOnPlacesGeomLevel k N data hKr

private local instance instAlgebraBarShortcut : Algebra Qb FNq := inferInstance

private local instance instAlgebraCShortcut : Algebra k Ck := inferInstance

omit [IsAlgClosed k] [DecidableEq k] in
private theorem frob_fixed_of_fixed {v : Plk} (hv : φ (φ v) = v) : φ (φ (φ v)) = φ v := by rw [hv]

omit [DecidableEq k] in

private theorem arithFrobC_smul_eq (data' : ModularPolynomialData q) (hKr' : KroneckerCongruence q data') (w : Plk) :
    arithFrobC q k N • w = frobOnPlacesGeomLevel k N data' hKr' w :=
  ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data' hKr' w

omit [IsAlgClosed k] [DecidableEq k] in
private theorem mapDomain_reduceFst_fstDiv_eq_zero (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (E : Divisor Qb FNq) (v : Plk) (hv : φ (φ v) = v) :
    Finsupp.mapDomain P.reduceFst (P.fstDiv E) v = 0 := by
  classical
  apply mapDomain_apply_eq_zero_of_forall
  intro W hW h
  have hW' : P.IsStrictFst W := by
    unfold PlaceSpecialization.fstDiv at hW
    rw [Finsupp.support_filter, Finset.mem_filter] at hW
    exact hW.2
  exact hW'.2 (h ▸ hv)

omit [IsAlgClosed k] [DecidableEq k] in
private theorem mapDomain_reduceSnd_sndDiv_eq_zero (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (E : Divisor Qb FNq) (v : Plk) (hv : φ (φ v) = v) :
    Finsupp.mapDomain P.reduceSnd (P.sndDiv E) v = 0 := by
  classical
  apply mapDomain_apply_eq_zero_of_forall
  intro W hW h
  have hW' : P.IsStrictSnd W := by
    unfold PlaceSpecialization.sndDiv at hW
    rw [Finsupp.support_filter, Finset.mem_filter] at hW
    exact hW.2
  exact hW'.2 (h ▸ hv)

variable (P : PlaceSpecialization A q N data hKr k red hα hβ)

private def D1 (E : Divisor Qb FNq) (w : Plk) (n₁ : ℕ) : Divisor k Ck :=
  Finsupp.mapDomain P.reduceFst (P.fstDiv E) + Finsupp.single w (n₁ : ℤ)

private def D2 (E : Divisor Qb FNq) (w : Plk) (n₂ : ℕ) : Divisor k Ck :=
  Finsupp.mapDomain P.reduceSnd (P.sndDiv E) + Finsupp.single (arithFrobC q k N • w) (n₂ : ℤ)

variable {P}

omit [IsAlgClosed k] [DecidableEq k] in
private theorem D1_of_not_fixed (E : Divisor Qb FNq) {w : Plk} (hw : φ (φ w) = w) (n₁ : ℕ) (v : Plk)
    (hv : φ (φ v) ≠ v) : D1 P E w n₁ v = Finsupp.mapDomain P.reduceFst (P.fstDiv E) v := by
  have hvw : v ≠ w := fun h => hv (by rw [h]; exact hw)
  rw [D1, Finsupp.add_apply, Finsupp.single_eq_of_ne hvw, add_zero]

omit [IsAlgClosed k] [DecidableEq k] in
private theorem D1_self (E : Divisor Qb FNq) {w : Plk} (hw : φ (φ w) = w) (n₁ : ℕ) :
    D1 P E w n₁ w = n₁ := by
  rw [D1, Finsupp.add_apply, mapDomain_reduceFst_fstDiv_eq_zero P E w hw, Finsupp.single_eq_same, zero_add]

omit [IsAlgClosed k] [DecidableEq k] in
private theorem D1_of_fixed_ne (E : Divisor Qb FNq) (w : Plk) (n₁ : ℕ) {v : Plk} (hv : φ (φ v) = v)
    (hvw : v ≠ w) : D1 P E w n₁ v = 0 := by
  rw [D1, Finsupp.add_apply, mapDomain_reduceFst_fstDiv_eq_zero P E v hv, Finsupp.single_eq_of_ne hvw, add_zero]

omit [DecidableEq k] in
private theorem D2_of_not_fixed (E : Divisor Qb FNq) {w : Plk} (hw : φ (φ w) = w) (n₂ : ℕ) (u : Plk)
    (hu : φ (φ u) ≠ u) : D2 P E w n₂ u = Finsupp.mapDomain P.reduceSnd (P.sndDiv E) u := by
  have huw : u ≠ φ w := fun h => hu (by rw [h]; exact frob_fixed_of_fixed hw)
  rw [D2, Finsupp.add_apply, arithFrobC_smul_eq data hKr, Finsupp.single_eq_of_ne huw, add_zero]

omit [DecidableEq k] in
private theorem D2_frob_self (E : Divisor Qb FNq) {w : Plk} (hw : φ (φ w) = w) (n₂ : ℕ) :
    D2 P E w n₂ (φ w) = n₂ := by
  rw [D2, Finsupp.add_apply, mapDomain_reduceSnd_sndDiv_eq_zero P E (φ w) (frob_fixed_of_fixed hw),
    arithFrobC_smul_eq data hKr, Finsupp.single_eq_same, zero_add]

omit [DecidableEq k] in
private theorem D2_smul_self (E : Divisor Qb FNq) {w : Plk} (hw : φ (φ w) = w) (n₂ : ℕ) :
    D2 P E w n₂ (arithFrobC q k N • w) = n₂ := by
  rw [arithFrobC_smul_eq data hKr]
  exact D2_frob_self E hw n₂

omit [DecidableEq k] in
private theorem D2_frob_of_fixed_ne (E : Divisor Qb FNq) (w : Plk) (n₂ : ℕ) {v : Plk} (hv : φ (φ v) = v)
    (hvw : v ≠ w) : D2 P E w n₂ (φ v) = 0 := by
  rw [D2, Finsupp.add_apply, mapDomain_reduceSnd_sndDiv_eq_zero P E (φ v) (frob_fixed_of_fixed hv),
    arithFrobC_smul_eq data hKr,
    Finsupp.single_eq_of_ne (fun h => hvw (frobOnPlacesGeomLevel_injective k N data hKr h)),
    add_zero]

omit [IsAlgClosed k] [DecidableEq k] in
private theorem not_isStrictSnd_of_isStrictFst {W : PlF} (h1 : P.IsStrictFst W) : ¬ P.IsStrictSnd W := by
  intro h2
  apply h1.2
  rw [h1.1]
  exact h2.1.symm

omit [IsAlgClosed k] [DecidableEq k] in

private theorem not_strict_of_reduceFst_eq {w : Plk} (hw : φ (φ w) = w) {V : PlF} (hV : P.reduceFst V = w) :
    ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V := by
  refine ⟨fun h1 => h1.2 (by rw [hV]; exact hw), fun h2 => h2.2 ?_⟩
  apply frobOnPlacesGeomLevel_injective k N data hKr
  have h : φ (φ (P.reduceFst V)) = P.reduceFst V := by rw [hV]; exact hw
  rw [h2.1] at h
  exact h

omit [IsAlgClosed k] [DecidableEq k] in

private theorem reduceFst_eq_of_fixed {w : Plk} {E : Divisor Qb FNq}
    (hEsupp : ∀ V ∈ E.support, P.IsStrictFst V ∨ P.IsStrictSnd V ∨
      (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V))
    {V : PlF} (hV : V ∈ E.support) (hfix : φ (φ (P.reduceFst V)) = P.reduceFst V) : P.reduceFst V = w := by
  rcases hEsupp V hV with h1 | h2 | hc
  · exact absurd hfix h1.2
  · exfalso
    apply h2.2
    apply frobOnPlacesGeomLevel_injective k N data hKr
    have h := hfix
    rw [h2.1] at h
    exact h
  · exact hc.1

omit [IsAlgClosed k] [DecidableEq k] in

private theorem isAffine_reduceFst_of_not_isCuspidal {V : PlF} (hV : ¬ ProlongationTuple.IsCuspidal P V) :
    IsAffineGeomPlace k N (P.reduceFst V) := by
  by_contra h
  exact hV (ProlongationTuple.isCuspidal_of_not_isAffineGeomPlace_reduceFst P V h)

omit [IsAlgClosed k] [DecidableEq k] in

private theorem isAffine_reduceSnd_of_not_isCuspidal (hqN : ¬ q ∣ N) {V : PlF}
    (hV : ¬ ProlongationTuple.IsCuspidal P V) (hV' : ¬ ProlongationTuple.IsCuspidal' P V) :
    IsAffineGeomPlace k N (P.reduceSnd V) := by
  by_contra h
  rw [← reduceFst_atkinLehnerBar_smul P hqN V] at h
  have hc := ProlongationTuple.isCuspidal_of_not_isAffineGeomPlace_reduceFst P _ h
  rcases ProlongationTuple.isInftySide_or_isZeroSide_of_isCuspidal P hqN _ hc with hi | hz
  · exact hV' ((ProlongationTuple.isInftySide_atkinLehnerBar_smul_iff P hqN V).mp hi).1
  · exact hV ((ProlongationTuple.isZeroSide_atkinLehnerBar_smul_iff P hqN V).mp hz).1

omit [IsAlgClosed k] [DecidableEq k] in

private theorem not_isAffine_reduceSnd_of_isZeroSide (hqN : ¬ q ∣ N) {c : PlF}
    (hc : ProlongationTuple.IsZeroSide P c) : ¬ IsAffineGeomPlace k N (P.reduceSnd c) := by
  rw [← reduceFst_atkinLehnerBar_smul P hqN c]
  exact ProlongationTuple.not_isAffineGeomPlace_reduceFst_of_isCuspidal P _
    ((ProlongationTuple.isInftySide_atkinLehnerBar_smul_iff P hqN c).mpr hc).1

variable (R : ProlongationTuple P)

omit [IsAlgClosed k] [DecidableEq k] in
private theorem ι_algebraMap (c : ResidueField A) :
    R.ι (algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N) c)
      = algebraMap k Ck (R.redBar c) := by
  apply Subtype.ext
  rw [R.ι_coe]
  change coeffMap R.redBar (algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) c)
    = algebraMap k (LaurentSeries k) (R.redBar c)
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

omit [IsAlgClosed k] [DecidableEq k] in
private theorem residue₁_coe_eq_zero {f : FNq} (h₁ : f ∈ R.R₁.integers)
    (h : R.R₁.residue ⟨f, h₁⟩ = 0) :
    (R.residue₁ ⟨f, h₁⟩ : Ck) = 0 := by
  rw [ProlongationTuple.residue₁_apply, h, map_zero]

omit [IsAlgClosed k] [DecidableEq k] in
private theorem residue₂_coe_eq_zero {f : FNq} (h₂ : f ∈ R.R₂.integers)
    (h : R.R₂.residue ⟨f, h₂⟩ = 0) :
    (R.residue₂ ⟨f, h₂⟩ : Ck) = 0 := by
  rw [ProlongationTuple.residue₂_apply, h, map_zero]

omit [IsAlgClosed k] [DecidableEq k] in
private theorem ne_zero_of_residue₁_ne_zero {f : FNq} (h₁ : f ∈ R.R₁.integers)
    (h : R.R₁.residue ⟨f, h₁⟩ ≠ 0) :
    f ≠ 0 := by
  intro h0
  apply h
  have : (⟨f, h₁⟩ : R.R₁.integers) = 0 := by
    apply Subtype.ext
    exact h0
  rw [this, map_zero]

omit [IsAlgClosed k] [DecidableEq k] in
private theorem ne_zero_of_residue₂_ne_zero {f : FNq} (h₂ : f ∈ R.R₂.integers)
    (h : R.R₂.residue ⟨f, h₂⟩ ≠ 0) :
    f ≠ 0 := by
  intro h0
  apply h
  have : (⟨f, h₂⟩ : R.R₂.integers) = 0 := by
    apply Subtype.ext
    exact h0
  rw [this, map_zero]

omit [IsAlgClosed k] [DecidableEq k] in
private theorem fstDiv_nonneg {E : Divisor Qb FNq} (hE : ∀ W, 0 ≤ E W) (W : PlF) : 0 ≤ P.fstDiv E W := by
  classical
  unfold PlaceSpecialization.fstDiv
  rw [Finsupp.filter_apply]
  split_ifs
  · exact hE W
  · exact le_rfl

omit [IsAlgClosed k] [DecidableEq k] in
private theorem sndDiv_nonneg {E : Divisor Qb FNq} (hE : ∀ W, 0 ≤ E W) (W : PlF) : 0 ≤ P.sndDiv E W := by
  classical
  unfold PlaceSpecialization.sndDiv
  rw [Finsupp.filter_apply]
  split_ifs
  · exact hE W
  · exact le_rfl

omit [IsAlgClosed k] [DecidableEq k] in
private theorem neg_fstDiv_le {E D : Divisor Qb FNq} (h : -E ≤ D) : -P.fstDiv E ≤ P.fstDiv D := by
  classical
  intro W
  unfold PlaceSpecialization.fstDiv
  rw [Finsupp.coe_neg, Pi.neg_apply, Finsupp.filter_apply, Finsupp.filter_apply]
  split_ifs
  · exact h W
  · simp

omit [IsAlgClosed k] [DecidableEq k] in
private theorem neg_sndDiv_le {E D : Divisor Qb FNq} (h : -E ≤ D) : -P.sndDiv E ≤ P.sndDiv D := by
  classical
  intro W
  unfold PlaceSpecialization.sndDiv
  rw [Finsupp.coe_neg, Pi.neg_apply, Finsupp.filter_apply, Finsupp.filter_apply]
  split_ifs
  · exact h W
  · simp

private theorem exists_principalDivisor (f : FNq) (hf : f ≠ 0) : ∃ D : Divisor Qb FNq, ∀ W, D W = W.ord f := by
  have hPD := ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (self := hPD) f hf
  exact ⟨D, hD⟩

omit [IsAlgClosed k] [DecidableEq k] in
private theorem image_fst_of_not_fixed (hDL : R.DivisorLawFst) {E : Divisor Qb FNq} (hE : ∀ W, 0 ≤ E W)
    {f : FNq} (hf : f ∈ riemannRochSpace E) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (v : Plk) (hv : φ (φ v) ≠ v) :
    (R.residue₁ ⟨f, h₁⟩ : Ck) = 0 ∨
      -(Finsupp.mapDomain P.reduceFst (P.fstDiv E) v) ≤ v.ord (R.residue₁ ⟨f, h₁⟩ : Ck) := by
  classical
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  haveI : Infinite (ResidueField A) := inferInstance
  obtain ⟨a, hne₁, hne₂⟩ := exists_add_algebraMap_residue_ne_zero R.R₁ R.R₂ h₁ h₂
  have h₁' : f + algebraMap Qb FNq (a : Qb) ∈ R.R₁.integers := add_mem h₁ (algebraMap_mem_integers R.R₁ a)
  have h₂' : f + algebraMap Qb FNq (a : Qb) ∈ R.R₂.integers := add_mem h₂ (algebraMap_mem_integers R.R₂ a)
  have hf'E : f + algebraMap Qb FNq (a : Qb) ∈ riemannRochSpace E :=
    add_mem hf (algebraMap_mem_riemannRochSpace hE _)
  have hf'0 : f + algebraMap Qb FNq (a : Qb) ≠ 0 := ne_zero_of_residue₁_ne_zero R h₁' hne₁
  obtain ⟨D, hD⟩ := exists_principalDivisor _ hf'0
  have hlaw := hDL _ h₁' h₂' hne₁ hne₂ D hD v hv
  have hlaw' : Finsupp.mapDomain P.reduceFst (P.fstDiv D) v = v.ord (R.residue₁ ⟨_, h₁'⟩ : Ck) := hlaw
  have hED : -E ≤ D := neg_le_of_mem_riemannRochSpace hf'E hf'0 hD
  have hb := neg_mapDomain_apply_le P.reduceFst (neg_fstDiv_le (P := P) hED) v
  rw [hlaw'] at hb
  have e1 := residue_add_algebraMap R.R₁ h₁ a
  have e2 : R.ι (R.R₁.residue ⟨_, h₁'⟩)
      = R.ι (R.R₁.residue ⟨f, h₁⟩) + algebraMap k Ck (R.redBar (IsLocalRing.residue A a)) := by
    rw [← ι_algebraMap, ← map_add]
    exact congrArg R.ι e1
  have hres : (R.residue₁ ⟨_, h₁'⟩ : Ck)
      = (R.residue₁ ⟨f, h₁⟩ : Ck) + algebraMap k Ck (R.redBar (IsLocalRing.residue A a)) := by
    rw [ProlongationTuple.residue₁_apply, ProlongationTuple.residue₁_apply]
    exact e2
  rw [hres] at hb
  have hn : -(Finsupp.mapDomain P.reduceFst (P.fstDiv E) v) ≤ 0 := by
    have := mapDomain_nonneg_apply P.reduceFst (fstDiv_nonneg (P := P) hE) v
    omega
  have key := ord_add_algebraMap_ge_of_ge v hn (Or.inr hb) (-(R.redBar (IsLocalRing.residue A a)))
  rwa [map_neg, add_neg_cancel_right] at key

omit [IsAlgClosed k] [DecidableEq k] in
private theorem image_snd_of_not_fixed (hDL : R.DivisorLawSnd) {E : Divisor Qb FNq} (hE : ∀ W, 0 ≤ E W)
    {f : FNq} (hf : f ∈ riemannRochSpace E) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (v : Plk) (hv : φ (φ v) ≠ v) :
    (R.residue₂ ⟨f, h₂⟩ : Ck) = 0 ∨
      -(Finsupp.mapDomain P.reduceSnd (P.sndDiv E) v) ≤ v.ord (R.residue₂ ⟨f, h₂⟩ : Ck) := by
  classical
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  haveI : Infinite (ResidueField A) := inferInstance
  obtain ⟨a, hne₁, hne₂⟩ := exists_add_algebraMap_residue_ne_zero R.R₁ R.R₂ h₁ h₂
  have h₁' : f + algebraMap Qb FNq (a : Qb) ∈ R.R₁.integers := add_mem h₁ (algebraMap_mem_integers R.R₁ a)
  have h₂' : f + algebraMap Qb FNq (a : Qb) ∈ R.R₂.integers := add_mem h₂ (algebraMap_mem_integers R.R₂ a)
  have hf'E : f + algebraMap Qb FNq (a : Qb) ∈ riemannRochSpace E :=
    add_mem hf (algebraMap_mem_riemannRochSpace hE _)
  have hf'0 : f + algebraMap Qb FNq (a : Qb) ≠ 0 := ne_zero_of_residue₁_ne_zero R h₁' hne₁
  obtain ⟨D, hD⟩ := exists_principalDivisor _ hf'0
  have hlaw := hDL _ h₁' h₂' hne₁ hne₂ D hD v hv
  have hlaw' : Finsupp.mapDomain P.reduceSnd (P.sndDiv D) v = v.ord (R.residue₂ ⟨_, h₂'⟩ : Ck) := hlaw
  have hED : -E ≤ D := neg_le_of_mem_riemannRochSpace hf'E hf'0 hD
  have hb := neg_mapDomain_apply_le P.reduceSnd (neg_sndDiv_le (P := P) hED) v
  rw [hlaw'] at hb
  have e1 := residue_add_algebraMap R.R₂ h₂ a
  have e2 : R.ι (R.R₂.residue ⟨_, h₂'⟩)
      = R.ι (R.R₂.residue ⟨f, h₂⟩) + algebraMap k Ck (R.redBar (IsLocalRing.residue A a)) := by
    rw [← ι_algebraMap, ← map_add]
    exact congrArg R.ι e1
  have hres : (R.residue₂ ⟨_, h₂'⟩ : Ck)
      = (R.residue₂ ⟨f, h₂⟩ : Ck) + algebraMap k Ck (R.redBar (IsLocalRing.residue A a)) := by
    rw [ProlongationTuple.residue₂_apply, ProlongationTuple.residue₂_apply]
    exact e2
  rw [hres] at hb
  have hn : -(Finsupp.mapDomain P.reduceSnd (P.sndDiv E) v) ≤ 0 := by
    have := mapDomain_nonneg_apply P.reduceSnd (sndDiv_nonneg (P := P) hE) v
    omega
  have key := ord_add_algebraMap_ge_of_ge v hn (Or.inr hb) (-(R.redBar (IsLocalRing.residue A a)))
  rwa [map_neg, add_neg_cancel_right] at key

open Classical in
omit [IsAlgClosed k] [DecidableEq k] in
private theorem image_fst_cusp (hqN : ¬ q ∣ N) (hR : R.IsModel) {E : Divisor Qb FNq}
    {f : FNq} (hf : f ∈ riemannRochSpace E) (h₁ : f ∈ R.R₁.integers)
    (c : PlF) (hc : ProlongationTuple.IsInftySide P c) :
    (R.residue₁ ⟨f, h₁⟩ : Ck) = 0 ∨
      -(Finsupp.mapDomain P.reduceFst (E.filter (ProlongationTuple.IsInftySide P)) (P.reduceFst c))
        ≤ (P.reduceFst c).ord (R.residue₁ ⟨f, h₁⟩ : Ck) := by
  by_cases hne : R.R₁.residue ⟨f, h₁⟩ = 0
  · exact Or.inl (residue₁_coe_eq_zero R h₁ hne)
  right
  have hf0 : f ≠ 0 := ne_zero_of_residue₁_ne_zero R h₁ hne
  obtain ⟨D, hD⟩ := exists_principalDivisor f hf0
  have hlaw := ProlongationTuple.cuspLawInfty_oneSided hqN P R hR f h₁ hne D hD c hc
  have hED : -E ≤ D := neg_le_of_mem_riemannRochSpace hf hf0 hD
  have hb := neg_mapDomain_filter_apply_le P.reduceFst (ProlongationTuple.IsInftySide P) hED (P.reduceFst c)
  rw [hlaw] at hb
  exact hb

open Classical in
omit [IsAlgClosed k] [DecidableEq k] in
private theorem image_snd_cusp (hqN : ¬ q ∣ N) (hR : R.IsModel) {E : Divisor Qb FNq}
    {f : FNq} (hf : f ∈ riemannRochSpace E) (h₂ : f ∈ R.R₂.integers)
    (c : PlF) (hc : ProlongationTuple.IsZeroSide P c) :
    (R.residue₂ ⟨f, h₂⟩ : Ck) = 0 ∨
      -(Finsupp.mapDomain P.reduceSnd (E.filter (ProlongationTuple.IsZeroSide P)) (P.reduceSnd c))
        ≤ (P.reduceSnd c).ord (R.residue₂ ⟨f, h₂⟩ : Ck) := by
  by_cases hne : R.R₂.residue ⟨f, h₂⟩ = 0
  · exact Or.inl (residue₂_coe_eq_zero R h₂ hne)
  right
  have hf0 : f ≠ 0 := ne_zero_of_residue₂_ne_zero R h₂ hne
  obtain ⟨D, hD⟩ := exists_principalDivisor f hf0
  have hlaw := ProlongationTuple.cuspLawZero_oneSided hqN P R hR f h₂ hne D hD c hc
  have hED : -E ≤ D := neg_le_of_mem_riemannRochSpace hf hf0 hD
  have hb := neg_mapDomain_filter_apply_le P.reduceSnd (ProlongationTuple.IsZeroSide P) hED (P.reduceSnd c)
  rw [hlaw] at hb
  exact hb

omit [DecidableEq k] in
private theorem deg_one_k (w : Plk) : w.deg = 1 := ModularCurve.place_deg_eq_one_of_isAlgClosed k N w

omit [IsAlgClosed k] [DecidableEq k] in
private theorem deg_one_Q (W : PlF) : W.deg = 1 := ModularCurve.deg_eq_one_modularFunctionFieldBar (N * q) W

open Classical in
omit [DecidableEq k] in
private theorem degree_fstDiv_push (E : Divisor Qb FNq) :
    Divisor.degree (Finsupp.mapDomain P.reduceFst (P.fstDiv E)) = ∑ W ∈ E.support.filter P.IsStrictFst, E W := by
  rw [degree_eq_sum_of_deg_eq_one deg_one_k, sum_mapDomain_id, ← degree_eq_sum_of_deg_eq_one deg_one_Q]
  unfold PlaceSpecialization.fstDiv
  rw [degree_filter_eq_sum deg_one_Q]

open Classical in
omit [DecidableEq k] in
private theorem degree_sndDiv_push (E : Divisor Qb FNq) :
    Divisor.degree (Finsupp.mapDomain P.reduceSnd (P.sndDiv E)) = ∑ W ∈ E.support.filter P.IsStrictSnd, E W := by
  rw [degree_eq_sum_of_deg_eq_one deg_one_k, sum_mapDomain_id, ← degree_eq_sum_of_deg_eq_one deg_one_Q]
  unfold PlaceSpecialization.sndDiv
  rw [degree_filter_eq_sum deg_one_Q]

open Classical in
omit [DecidableEq k] in

private theorem degree_identity (E : Divisor Qb FNq) {w : Plk} (hw : φ (φ w) = w)
    (hEsupp : ∀ V ∈ E.support, P.IsStrictFst V ∨ P.IsStrictSnd V ∨
      (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V))
    (n₁ n₂ : ℕ) (hn : ((n₁ : ℤ) + n₂) = Finsupp.mapDomain P.reduceFst E w) :
    Divisor.degree (D1 P E w n₁) + Divisor.degree (D2 P E w n₂) = Divisor.degree E := by
  have hmass : Finsupp.mapDomain P.reduceFst E w = ∑ W ∈ E.support.filter (fun W => P.reduceFst W = w), E W :=
    mapDomain_apply_eq_sum_filter _ _ _
  rw [D1, D2, map_add, map_add, degree_fstDiv_push, degree_sndDiv_push,
    degree_single_of_deg_eq_one deg_one_k, degree_single_of_deg_eq_one deg_one_k,
    degree_eq_sum_support_of_deg_eq_one deg_one_Q E,
    ← Finset.sum_filter_add_sum_filter_not E.support P.IsStrictFst,
    ← Finset.sum_filter_add_sum_filter_not (E.support.filter fun W => ¬ P.IsStrictFst W) P.IsStrictSnd,
    Finset.filter_filter, Finset.filter_filter]
  have hsnd : (E.support.filter fun W => ¬ P.IsStrictFst W ∧ P.IsStrictSnd W) = E.support.filter P.IsStrictSnd :=
    Finset.filter_congr fun W _ =>
      ⟨fun h => h.2, fun h2 => ⟨fun h1 => not_isStrictSnd_of_isStrictFst h1 h2, h2⟩⟩
  have hrest : (E.support.filter fun W => ¬ P.IsStrictFst W ∧ ¬ P.IsStrictSnd W)
      = E.support.filter (fun W => P.reduceFst W = w) := by
    refine Finset.filter_congr fun W hW => ⟨fun h => ?_, fun h => not_strict_of_reduceFst_eq hw h⟩
    rcases hEsupp W hW with h1 | h2 | hc
    · exact absurd h1 h.1
    · exact absurd h2 h.2
    · exact hc.1
  rw [hsnd, hrest, ← hmass, ← hn]
  ring

omit [IsAlgClosed k] [DecidableEq k] in
private theorem mem_support_of_mem_support_fstDiv {E : Divisor Qb FNq} {V : PlF} (hV : V ∈ (P.fstDiv E).support) :
    V ∈ E.support := by
  classical
  unfold PlaceSpecialization.fstDiv at hV
  rw [Finsupp.support_filter, Finset.mem_filter] at hV
  exact hV.1

omit [IsAlgClosed k] [DecidableEq k] in
private theorem mem_support_of_mem_support_sndDiv {E : Divisor Qb FNq} {V : PlF} (hV : V ∈ (P.sndDiv E).support) :
    V ∈ E.support := by
  classical
  unfold PlaceSpecialization.sndDiv at hV
  rw [Finsupp.support_filter, Finset.mem_filter] at hV
  exact hV.1

open Classical in
omit [IsAlgClosed k] [DecidableEq k] in
private theorem filter_isInftySide_eq_zero {E : Divisor Qb FNq}
    (hEc : ∀ V ∈ E.support, ¬ ProlongationTuple.IsCuspidal P V ∧ ¬ ProlongationTuple.IsCuspidal' P V) :
    E.filter (ProlongationTuple.IsInftySide P) = 0 := by
  rw [Finsupp.filter_eq_zero_iff]
  intro V hV
  by_contra hne
  exact (hEc V (Finsupp.mem_support_iff.mpr hne)).1 hV.1

open Classical in
omit [IsAlgClosed k] [DecidableEq k] in
private theorem filter_isZeroSide_eq_zero {E : Divisor Qb FNq}
    (hEc : ∀ V ∈ E.support, ¬ ProlongationTuple.IsCuspidal P V ∧ ¬ ProlongationTuple.IsCuspidal' P V) :
    E.filter (ProlongationTuple.IsZeroSide P) = 0 := by
  rw [Finsupp.filter_eq_zero_iff]
  intro V hV
  by_contra hne
  exact (hEc V (Finsupp.mem_support_iff.mpr hne)).2 hV.1

private theorem node_spec (W : Finset Plk) (hRL : R.RegularityLaw W) (w : Plk) (hw : w ∈ W)
    {E : Divisor Qb FNq} (hE0 : ∀ V, 0 ≤ E V) (t : FNq) (ht₁ : t ∈ R.R₁.integers)
    (ht₂ : t ∈ R.R₂.integers) (htord' : ∀ V : PlF, P.reduceFst V = w → V.ord t = E V)
    (n₁ n₂ : ℕ) (l₁ l₂ : k) (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0) (πw : Ck) (hπw : w.ord πw = 1)
    (htw₁ : w.HasValue (πw ^ (-(n₁ : ℤ)) * (R.residue₁ ⟨t, ht₁⟩ : Ck)) l₁)
    (htw₂ : (arithFrobC q k N • w).HasValue
      ((arithFrobC q k N • πw) ^ (-(n₂ : ℤ)) * (R.residue₂ ⟨t, ht₂⟩ : Ck)) l₂)
    {f : FNq} (hf : f ∈ riemannRochSpace E) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers) :
    (R.residue₁ ⟨f, h₁⟩ ≠ 0 → -(n₁ : ℤ) ≤ w.ord (R.residue₁ ⟨f, h₁⟩ : Ck)) ∧
      (R.residue₂ ⟨f, h₂⟩ ≠ 0 →
        -(n₂ : ℤ) ≤ (arithFrobC q k N • w).ord (R.residue₂ ⟨f, h₂⟩ : Ck)) ∧
      ∃ c : k, w.HasValue (πw ^ (n₁ : ℤ) * (R.residue₁ ⟨f, h₁⟩ : Ck)) (l₂ * c) ∧
        (arithFrobC q k N • w).HasValue
          ((arithFrobC q k N • πw) ^ (n₂ : ℤ) * (R.residue₂ ⟨f, h₂⟩ : Ck)) (l₁ * c) := by
  refine R.le_ord_residue_and_exists_hasValue_of_mul W hRL w hw f t h₁ h₂ ht₁ ht₂ ?_ (n₁ : ℤ) (n₂ : ℤ) l₁ l₂
    hl₁ hl₂ πw hπw htw₁ htw₂
  intro V hV
  by_cases hft : f * t = 0
  · rw [hft, Place.ord_zero]
  · have hf0 : f ≠ 0 := fun h => hft (by rw [h, zero_mul])
    have ht0 : t ≠ 0 := fun h => hft (by rw [h, mul_zero])
    rw [Place.ord_mul V hf0 ht0, htord' V hV]
    have := neg_le_ord_of_mem hE0 hf V
    omega

omit [DecidableEq k] in

private theorem residue₁_mem (hqN : ¬ q ∣ N) (hR : R.IsModel) (W : Finset Plk) (hRL : R.RegularityLaw W)
    {w : Plk} (hw2 : φ (φ w) = w) {E : Divisor Qb FNq} (hE0 : ∀ V, 0 ≤ E V)
    (hEc : ∀ V ∈ E.support, ¬ ProlongationTuple.IsCuspidal P V ∧ ¬ ProlongationTuple.IsCuspidal' P V)
    (n₁ : ℕ)
    {f : FNq} (hf : f ∈ riemannRochSpace E) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (hordfix : ∀ v : Plk, φ (φ v) = v → v ≠ w → ∀ V : PlF, P.reduceFst V = v → 0 ≤ V.ord f)
    (hnode : (R.residue₁ ⟨f, h₁⟩ : Ck) ≠ 0 → -(n₁ : ℤ) ≤ w.ord (R.residue₁ ⟨f, h₁⟩ : Ck)) :
    (R.residue₁ ⟨f, h₁⟩ : Ck) ∈ riemannRochSpace (D1 P E w n₁) := by
  rw [mem_riemannRochSpace_iff]
  intro v
  by_cases h0 : (R.residue₁ ⟨f, h₁⟩ : Ck) = 0
  · exact Or.inl h0
  right
  by_cases hv : φ (φ v) = v
  · by_cases hvw : v = w
    · rw [hvw, D1_self E hw2]
      exact hnode h0
    · rw [D1_of_fixed_ne E w n₁ hv hvw, neg_zero]
      by_cases hva : IsAffineGeomPlace k N v
      · exact (hRL.1 f h₁ h₂ v hv hva (hordfix v hv hvw)).1 h0
      · obtain ⟨⟨C, hC, hCv⟩, -⟩ :=
          exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace hqN P v hva
        have key := (image_fst_cusp R hqN hR hf h₁ C hC).resolve_left h0
        rw [filter_isInftySide_eq_zero hEc, Finsupp.mapDomain_zero, Finsupp.zero_apply, neg_zero, hCv] at key
        exact key
  · rw [D1_of_not_fixed E hw2 n₁ v hv]
    exact (image_fst_of_not_fixed R hR.1 hE0 hf h₁ h₂ v hv).resolve_left h0

omit [DecidableEq k] in

private theorem residue₂_mem (hqN : ¬ q ∣ N) (hR : R.IsModel) (W : Finset Plk) (hRL : R.RegularityLaw W)
    {w : Plk} (hw2 : φ (φ w) = w) {E : Divisor Qb FNq} (hE0 : ∀ V, 0 ≤ E V)
    (hEc : ∀ V ∈ E.support, ¬ ProlongationTuple.IsCuspidal P V ∧ ¬ ProlongationTuple.IsCuspidal' P V)
    (n₂ : ℕ)
    {f : FNq} (hf : f ∈ riemannRochSpace E) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (hordfix : ∀ v : Plk, φ (φ v) = v → v ≠ w → ∀ V : PlF, P.reduceFst V = v → 0 ≤ V.ord f)
    (hnode : (R.residue₂ ⟨f, h₂⟩ : Ck) ≠ 0 →
      -(n₂ : ℤ) ≤ (arithFrobC q k N • w).ord (R.residue₂ ⟨f, h₂⟩ : Ck)) :
    (R.residue₂ ⟨f, h₂⟩ : Ck) ∈ riemannRochSpace (D2 P E w n₂) := by
  rw [mem_riemannRochSpace_iff]
  intro u
  by_cases h0 : (R.residue₂ ⟨f, h₂⟩ : Ck) = 0
  · exact Or.inl h0
  right
  by_cases hu : φ (φ u) = u
  ·
    have hvfix : φ (φ (φ u)) = φ u := by rw [hu]
    by_cases hvw : φ u = w
    · have huw : u = φ w := by rw [← hvw, hu]
      rw [huw, D2_frob_self E hw2, ← arithFrobC_smul_eq data hKr]
      exact hnode h0
    · rw [show D2 P E w n₂ u = D2 P E w n₂ (φ (φ u)) by rw [hu], D2_frob_of_fixed_ne E w n₂ hvfix hvw,
        neg_zero]
      by_cases hua : IsAffineGeomPlace k N u
      · have hva : IsAffineGeomPlace k N (φ u) :=
          ModularCurve.isAffineGeomPlace_frobOnPlacesGeomLevel k N data hKr u hua
        have key := (hRL.1 f h₁ h₂ (φ u) hvfix hva (hordfix (φ u) hvfix hvw)).2 h0
        rw [hu] at key
        exact key
      · obtain ⟨-, ⟨C, hC, hCu⟩⟩ :=
          exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace hqN P u hua
        have key := (image_snd_cusp R hqN hR hf h₂ C hC).resolve_left h0
        rw [filter_isZeroSide_eq_zero hEc, Finsupp.mapDomain_zero, Finsupp.zero_apply, neg_zero, hCu] at key
        exact key
  · rw [D2_of_not_fixed E hw2 n₂ u hu]
    exact (image_snd_of_not_fixed R hR.2.1 hE0 hf h₁ h₂ u hu).resolve_left h0

omit [DecidableEq k] in
open Classical in

private theorem glue_pairs (W : Finset Plk) (hRL : R.RegularityLaw W) (π : Plk → Ck)
    {w : Plk} (hw2 : φ (φ w) = w) (hWfix : ∀ w' ∈ W, φ (φ w') = w')
    (E : Divisor Qb FNq) (n₁ n₂ : ℕ) (l₁ l₂ : k) (hl₁ : l₁ ≠ 0)
    {f : FNq} (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (hordfix : ∀ v : Plk, φ (φ v) = v → v ≠ w → ∀ V : PlF, P.reduceFst V = v → 0 ≤ V.ord f)
    (hnode : ∃ c : k, w.HasValue (π w ^ (n₁ : ℤ) * (R.residue₁ ⟨f, h₁⟩ : Ck)) (l₂ * c) ∧
      (arithFrobC q k N • w).HasValue
        ((arithFrobC q k N • π w) ^ (n₂ : ℤ) * (R.residue₂ ⟨f, h₂⟩ : Ck)) (l₁ * c)) :
    ∀ s ∈ nodePairsOfPlaces (arithFrobC q k N) W,
      ∃ c : k,
        s.1.HasValue (π s.1 ^ (D1 P E w n₁ s.1) * (R.residue₁ ⟨f, h₁⟩ : Ck))
          (Function.update (fun _ => (1 : k)) w (l₂ * l₁⁻¹) s.1 * c) ∧
        s.2.HasValue ((arithFrobC q k N • π s.1) ^ (D2 P E w n₂ s.2) * (R.residue₂ ⟨f, h₂⟩ : Ck)) c := by
  intro s hs
  obtain ⟨w', hw'W, rfl⟩ := (mem_nodePairsOfPlaces_iff (arithFrobC q k N) W s).mp hs
  simp only [smulNodePair_fst, smulNodePair_snd]
  by_cases hww : w' = w
  · rw [hww]
    obtain ⟨c, hc₁, hc₂⟩ := hnode
    refine ⟨l₁ * c, ?_, ?_⟩
    · rw [D1_self E hw2, Function.update_self]
      have : l₂ * l₁⁻¹ * (l₁ * c) = l₂ * c := by
        field_simp [hl₁]
      rw [this]
      exact hc₁
    · rw [D2_smul_self E hw2]
      exact hc₂
  ·
    have hfx : φ (φ w') = w' := hWfix w' hw'W
    have hD1 : D1 P E w n₁ w' = 0 := D1_of_fixed_ne E w n₁ hfx hww
    have hD2 : D2 P E w n₂ (arithFrobC q k N • w') = 0 := by
      rw [arithFrobC_smul_eq data hKr]
      exact D2_frob_of_fixed_ne E w n₂ hfx hww
    rw [hD1, hD2, Function.update_of_ne hww]
    obtain ⟨c, hc₁, hc₂⟩ := hRL.2 f h₁ h₂ _ hs (fun V hV => hordfix w' hfx hww V hV)
    refine ⟨c, ?_, ?_⟩
    · simpa only [zpow_zero, one_mul, smulNodePair_fst] using hc₁
    · simpa only [zpow_zero, one_mul, smulNodePair_snd] using hc₂

open Classical in

private theorem splitDatum_main (hqN : ¬ q ∣ N) (hR : R.IsModel)
    (W : Finset Plk) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k) (hRL : R.RegularityLaw W)
    (π : Plk → Ck) (hπ : ∀ w ∈ W, w.ord (π w) = 1)
    (w : Plk) (hw : w ∈ W) (hw2 : φ (φ w) = w)
    (E : Divisor Qb FNq) (hE0 : ∀ V, 0 ≤ E V)
    (hEsupp : ∀ V ∈ E.support, P.IsStrictFst V ∨ P.IsStrictSnd V ∨
      (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V))
    (hEc : ∀ V ∈ E.support, ¬ ProlongationTuple.IsCuspidal P V ∧ ¬ ProlongationTuple.IsCuspidal' P V)
    (t : FNq) (ht₁ : t ∈ R.R₁.integers) (ht₂ : t ∈ R.R₂.integers)
    (htord : ∀ V : PlF, (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V) → V.ord t = E V)
    (n₁ n₂ : ℕ) (l₁ l₂ : k) (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    (hn : ((n₁ : ℤ) + n₂) = Finsupp.mapDomain P.reduceFst E w)
    (htw₁ : w.HasValue (π w ^ (-(n₁ : ℤ)) * (R.residue₁ ⟨t, ht₁⟩ : Ck)) l₁)
    (htw₂ : (arithFrobC q k N • w).HasValue
      ((arithFrobC q k N • π w) ^ (-(n₂ : ℤ)) * (R.residue₂ ⟨t, ht₂⟩ : Ck)) l₂) :
    R.SplitDatum W π E (D1 P E w n₁) (D2 P E w n₂) (Function.update (fun _ => (1 : k)) w (l₂ * l₁⁻¹)) := by

  have hwss : IsSupersingularPlace q N k w := (hW w).mp hw
  have hwaff : IsAffineGeomPlace k N w := hwss.2.1
  have hWfix : ∀ w' ∈ W, φ (φ w') = w' := fun w' hw' =>
    ModularCurve.frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed k N hqN
      data hKr w' ((hW w').mp hw')

  have hsaff₁ : ∀ V ∈ E.support, IsAffineGeomPlace k N (P.reduceFst V) := fun V hV =>
    isAffine_reduceFst_of_not_isCuspidal (hEc V hV).1
  have hsaff₂ : ∀ V ∈ E.support, IsAffineGeomPlace k N (P.reduceSnd V) := fun V hV =>
    isAffine_reduceSnd_of_not_isCuspidal hqN (hEc V hV).1 (hEc V hV).2
  have hsuppfix : ∀ V ∈ E.support, φ (φ (P.reduceFst V)) = P.reduceFst V → P.reduceFst V = w :=
    fun V hV hfix => reduceFst_eq_of_fixed hEsupp hV hfix

  have hm0 : ∀ v : Plk, φ (φ v) = v → v ≠ w → Finsupp.mapDomain P.reduceFst E v = 0 := by
    intro v hv hvw
    apply mapDomain_apply_eq_zero_of_forall
    intro V hV h
    apply hvw
    rw [← h]
    exact hsuppfix V hV (by rw [h]; exact hv)
  have hmass_nonneg : ∀ v : Plk, 0 ≤ Finsupp.mapDomain P.reduceFst E v := fun v =>
    mapDomain_nonneg_apply P.reduceFst hE0 v

  have hordfix : ∀ {f : FNq}, f ∈ riemannRochSpace E → ∀ v : Plk, φ (φ v) = v → v ≠ w →
      ∀ V : PlF, P.reduceFst V = v → 0 ≤ V.ord f := by
    intro f hf v hv hvw V hVv
    have hEV : E V = 0 := by
      by_contra hne
      apply hvw
      rw [← hVv]
      exact hsuppfix V (Finsupp.mem_support_iff.mpr hne) (by rw [hVv]; exact hv)
    have := neg_le_ord_of_mem hE0 hf V
    rw [hEV, neg_zero] at this
    exact this

  have htord' : ∀ V : PlF, P.reduceFst V = w → V.ord t = E V := fun V hV =>
    htord V ⟨hV, not_strict_of_reduceFst_eq hw2 hV⟩
  refine ⟨hπ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro v hv _
    rw [filter_eq_zero_of_nonneg E hE0 _ (fun V => Iff.rfl), Finsupp.mapDomain_zero, Finsupp.zero_apply,
      filter_eq_self_of_nonneg E hE0 _ (fun V => Iff.rfl)]
    by_cases hvw : v = w
    · subst hvw
      rw [D1_self E hv, D2_frob_self E hv, ← hn]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
    · rw [D1_of_fixed_ne E w n₁ hv hvw, D2_frob_of_fixed_ne E w n₂ hv hvw]
      exact ⟨le_rfl, hmass_nonneg v, le_rfl, hmass_nonneg v⟩
  ·
    exact degree_identity E hw2 hEsupp n₁ n₂ hn
  ·
    intro w' _
    by_cases h : w' = w
    · rw [h, Function.update_self]
      exact mul_ne_zero hl₂ (inv_ne_zero hl₁)
    · rw [Function.update_of_ne h]
      exact one_ne_zero
  ·
    intro v hv
    exact ⟨D1_of_not_fixed E hw2 n₁ v hv, D2_of_not_fixed E hw2 n₂ v hv⟩
  ·
    intro v hv _
    by_cases hvw : v = w
    · subst hvw
      rw [D1_self E hv, D2_frob_self E hv]
      exact hn
    · rw [D1_of_fixed_ne E w n₁ hv hvw, D2_frob_of_fixed_ne E w n₂ hv hvw, hm0 v hv hvw, add_zero]
  ·
    intro c hc
    have hnc : ¬ IsAffineGeomPlace k N (P.reduceFst c) :=
      ProlongationTuple.not_isAffineGeomPlace_reduceFst_of_isCuspidal P c hc.1
    have h1 : Finsupp.mapDomain P.reduceFst (P.fstDiv E) (P.reduceFst c) = 0 := by
      apply mapDomain_apply_eq_zero_of_forall
      intro V hV h
      apply hnc
      rw [← h]
      exact hsaff₁ V (mem_support_of_mem_support_fstDiv hV)
    have h2 : P.reduceFst c ≠ w := by
      intro h
      apply hnc
      rw [h]
      exact hwaff
    rw [filter_isInftySide_eq_zero hEc, Finsupp.mapDomain_zero, Finsupp.zero_apply, D1, Finsupp.add_apply, h1,
      Finsupp.single_eq_of_ne h2, add_zero]
  ·
    intro c hc
    have hnc : ¬ IsAffineGeomPlace k N (P.reduceSnd c) := not_isAffine_reduceSnd_of_isZeroSide hqN hc
    have h1 : Finsupp.mapDomain P.reduceSnd (P.sndDiv E) (P.reduceSnd c) = 0 := by
      apply mapDomain_apply_eq_zero_of_forall
      intro V hV h
      apply hnc
      rw [← h]
      exact hsaff₂ V (mem_support_of_mem_support_sndDiv hV)
    have h2 : P.reduceSnd c ≠ φ w := by
      intro h
      apply hnc
      rw [h]
      exact ModularCurve.isAffineGeomPlace_frobOnPlacesGeomLevel k N data hKr w hwaff
    rw [filter_isZeroSide_eq_zero hEc, Finsupp.mapDomain_zero, Finsupp.zero_apply, D2, Finsupp.add_apply, h1,
      arithFrobC_smul_eq data hKr, Finsupp.single_eq_of_ne h2, add_zero]
  ·
    intro f hf h₁ h₂
    have hsp :=
      node_spec R W hRL w hw hE0 t ht₁ ht₂ htord' n₁ n₂ l₁ l₂ hl₁ hl₂ (π w) (hπ w hw) htw₁ htw₂ hf h₁ h₂
    exact ⟨residue₁_mem R hqN hR W hRL hw2 hE0 hEc n₁ hf h₁ h₂ (hordfix hf) hsp.1,
      residue₂_mem R hqN hR W hRL hw2 hE0 hEc n₂ hf h₁ h₂ (hordfix hf) hsp.2.1,
      glue_pairs R W hRL π hw2 hWfix E n₁ n₂ l₁ l₂ hl₁ h₁ h₂ (hordfix hf) hsp.2.2⟩

end Site

end W7SplitPort

end

p2m_open "ModularCurve.PlaceSpecialization~IsInftySide~IsCuspidal~IsZeroSide~IsCuspidal'" in open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization.ProlongationTuple in

open Classical in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (hqN : ¬ q ∣ N) (R : ProlongationTuple P) (hR : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (hRL : R.RegularityLaw W) (hO : R.OrderLawFixed)
    (π : Place k (modularFunctionFieldC k N) → modularFunctionFieldC k N) (hπ : ∀ w ∈ W, w.ord (π w) = 1)
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (hw2 : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w)
    (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hE0 : ∀ V, 0 ≤ E V)
    (hEsupp : ∀ V ∈ E.support, P.IsStrictFst V ∨ P.IsStrictSnd V ∨
      (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V))
    (hEc : ∀ V ∈ E.support, ¬ IsCuspidal P V ∧ ¬ IsCuspidal' P V)
    (t : ↥(modularFunctionFieldBar (N * q))) (ht₁ : t ∈ R.R₁.integers) (ht₂ : t ∈ R.R₂.integers)
    (htord : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V) → V.ord t = E V)
    (n₁ n₂ : ℕ) (l₁ l₂ : k) (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    (hn : ((n₁ : ℤ) + n₂) = Finsupp.mapDomain P.reduceFst E w)
    (htw₁ : w.HasValue (π w ^ (-(n₁ : ℤ)) * (R.residue₁ ⟨t, ht₁⟩ : ↥(modularFunctionFieldC k N))) l₁)
    (htw₂ : (arithFrobC q k N • w).HasValue
      ((arithFrobC q k N • π w) ^ (-(n₂ : ℤ)) * (R.residue₂ ⟨t, ht₂⟩ : ↥(modularFunctionFieldC k N))) l₂) :
    R.SplitDatum W π E
      (Finsupp.mapDomain P.reduceFst (P.fstDiv E) + Finsupp.single w (n₁ : ℤ))
      (Finsupp.mapDomain P.reduceSnd (P.sndDiv E) + Finsupp.single (arithFrobC q k N • w) (n₂ : ℤ))
      (Function.update (fun _ => (1 : k)) w (l₂ * l₁⁻¹)) := by
  have _ := hO
  exact W7SplitPort.splitDatum_main R hqN hR W hW hRL π hπ w hw hw2 E hE0 hEsupp hEc t ht₁ ht₂ htord n₁ n₂ l₁ l₂
    hl₁ hl₂ hn htw₁ htw₂

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_splitDatum_of_forall_reduceFst_eq_ord_eq
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_splitDatum_of_forall_reduceFst_eq_ord_eq (solution)
