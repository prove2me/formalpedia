-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.depth_pos_of_depthValueLaw_of_nodeEquation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/2acf24ab-2bcc-5050-a94c-0eb817e967c3

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_NodeCoordinates_exists_hasDepth_or_depthBetween_y_of_nodeEquation_of_orderLawFixed
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_NodeCoordinates_hasValuation_y_iff_yDepth_eq
import Theorems.Thm_ModularCurve_isRational_place_modularFunctionFieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_NodeCoordinates_depth_pos_of_depthValueLaw_of_nodeEquation
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

section ValueGroupFurniture

variable {A : ValuationSubring (AlgebraicClosure ℚ)}

private theorem dbd_valuation_natCast_lt_one {q : ℕ} (hA : A.LiesOverPrime q) :
    A.valuation ((q : ℕ) : AlgebraicClosure ℚ) < 1 :=
  (ValuationSubring.mem_nonunits_iff A).mp hA

private theorem dbd_valuation_natCast_pos {q : ℕ} (hq : q ≠ 0) : 0 < A.valuation ((q : ℕ) : AlgebraicClosure ℚ) :=
  zero_lt_iff.mpr (A.valuation.ne_zero_iff.mpr (Nat.cast_ne_zero.mpr hq))

private theorem dbd_lt_of_pow_lt_pow {γ : A.ValueGroup} (h0 : 0 < γ) (h1 : γ < 1) {E d : ℕ} (h : γ ^ E < γ ^ d) :
    d < E :=
  (pow_lt_pow_iff_right_of_lt_one₀ h0 h1).mp h

private theorem dbd_pow_succ_lt {γ : A.ValueGroup} (h0 : 0 < γ) (h1 : γ < 1) (n : ℕ) : γ ^ (n + 1) < γ ^ n :=
  pow_lt_pow_right_of_lt_one₀ h0 h1 (Nat.lt_succ_self n)

private theorem dbd_pow_le_pow_of_le {γ : A.ValueGroup} (h1 : γ ≤ 1) {m n : ℕ} (h : m ≤ n) : γ ^ n ≤ γ ^ m :=
  pow_le_pow_right_of_le_one' h1 h

variable {K : IntermediateField ℚ (AlgebraicClosure ℚ)}

private theorem dbd_valuation_coe_le_one (z : ↥(NodeLocalized.coeffSubring A K)) :
    A.valuation (z : AlgebraicClosure ℚ) ≤ 1 :=
  A.valuation_le_one ⟨_, (Subring.mem_inf.mp z.2).1⟩

private theorem dbd_valuation_coe_eq_one_of_isUnit {ε : ↥(NodeLocalized.coeffSubring A K)} (hε : IsUnit ε) :
    A.valuation (ε : AlgebraicClosure ℚ) = 1 := by
  obtain ⟨v, rfl⟩ := hε
  have h1 := congrArg (fun z : ↥(NodeLocalized.coeffSubring A K) => A.valuation (z : AlgebraicClosure ℚ)) v.mul_inv
  simp only [MulMemClass.coe_mul, OneMemClass.coe_one, map_mul, map_one] at h1
  refine le_antisymm (dbd_valuation_coe_le_one _) ?_
  calc (1 : A.ValueGroup) = _ * _ := h1.symm
    _ ≤ _ := mul_le_of_le_one_right' (dbd_valuation_coe_le_one _)

private theorem dbd_valuation_natCast_eq_pow {q eK : ℕ} {ϖ ε : ↥(NodeLocalized.coeffSubring A K)} (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε) :
    A.valuation ((q : ℕ) : AlgebraicClosure ℚ) = A.valuation (ϖ : AlgebraicClosure ℚ) ^ eK := by
  have h := congrArg (fun z : ↥(NodeLocalized.coeffSubring A K) => A.valuation (z : AlgebraicClosure ℚ)) hqϖ
  simpa only [SubringClass.coe_natCast, MulMemClass.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow,
    dbd_valuation_coe_eq_one_of_isUnit hε, mul_one] using h

private theorem dbd_valuation_coe_lt_one {q eK : ℕ} {ϖ ε : ↥(NodeLocalized.coeffSubring A K)} (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
    (hq1 : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) < 1) : A.valuation (ϖ : AlgebraicClosure ℚ) < 1 := by
  refine lt_of_le_of_ne (dbd_valuation_coe_le_one ϖ) fun h1 => ?_
  rw [dbd_valuation_natCast_eq_pow hε hqϖ, h1, one_pow] at hq1
  exact lt_irrefl _ hq1

private theorem dbd_valuation_coe_pos {q eK : ℕ} {ϖ ε : ↥(NodeLocalized.coeffSubring A K)} (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
    (hq0 : 0 < A.valuation ((q : ℕ) : AlgebraicClosure ℚ)) (hq1 : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) < 1) :
    0 < A.valuation (ϖ : AlgebraicClosure ℚ) := by
  refine zero_lt_iff.mpr fun h0 => ?_
  have hqv := dbd_valuation_natCast_eq_pow hε hqϖ
  rw [h0] at hqv
  cases eK with
  | zero =>
    rw [pow_zero] at hqv
    rw [hqv] at hq1
    exact lt_irrefl _ hq1
  | succ m =>
    rw [zero_pow (Nat.succ_ne_zero m)] at hqv
    rw [hqv] at hq0
    exact lt_irrefl _ hq0

end ValueGroupFurniture

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime q) {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (hmodel : R.IsModel) (hord : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W) (hvalA : R.ValueIntegralityLaw w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K)) (eK : ℕ) (ε : ↥(NodeLocalized.coeffSubring A K)) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
    (c : R.NodeCoordinates K w) (E : ℕ) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ (E * eK) * u)
    (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → ℕ) (hdepth : c.DepthValueLaw depth)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = w)
    (hfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) :
    0 < depth V := by
  have hrat : V.IsRational := isRational_place_modularFunctionFieldBar (N * q) V
  have hq0 : 0 < A.valuation ((q : ℕ) : AlgebraicClosure ℚ) := dbd_valuation_natCast_pos (Fact.out : q.Prime).ne_zero
  have hq1 : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) < 1 := dbd_valuation_natCast_lt_one hA
  have hϖpos : 0 < A.valuation (ϖ : AlgebraicClosure ℚ) := dbd_valuation_coe_pos hε hqϖ hq0 hq1
  have hϖ1 : A.valuation (ϖ : AlgebraicClosure ℚ) < 1 := dbd_valuation_coe_lt_one hε hqϖ hq1
  have hϖ0 : (ϖ : AlgebraicClosure ℚ) ≠ 0 := A.valuation.ne_zero_iff.mp hϖpos.ne'
  have hlaw : c.yDepth V = A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ depth V := hdepth V hV hfix

  have hpart := NodeCoordinates.exists_hasDepth_or_depthBetween_y_of_nodeEquation_of_orderLawFixed R hqN hmodel hord W
    hW hreg hval K w hw hvalA ϖ c (E * eK) u hu hxy V hV hrat hϖ0
  have hup : c.yDepth V < 1 := by
    rcases hpart with ⟨n, h1n, -, hdep⟩ | ⟨n, -, hbet⟩
    · rw [(NodeCoordinates.hasValuation_y_iff_yDepth_eq R c V hV hrat _).mp hdep.hasValuation]
      calc A.valuation (ϖ : AlgebraicClosure ℚ) ^ n ≤ A.valuation (ϖ : AlgebraicClosure ℚ) ^ 1 :=
            dbd_pow_le_pow_of_le hϖ1.le h1n
        _ < 1 := by rw [pow_one]; exact hϖ1
    · obtain ⟨a, ha, -, hlt⟩ := (Place.depthBetween_iff A V _ _ _ _).mp hbet
      rw [(NodeCoordinates.hasValuation_y_iff_yDepth_eq R c V hV hrat (A.valuation a)).mp
        ((Place.hasValuation_iff A V _ _).mpr ⟨a, ha, rfl⟩)]
      exact lt_of_lt_of_le hlt (pow_le_one₀ zero_le' hϖ1.le)

  rw [hlaw] at hup
  refine Nat.pos_of_ne_zero fun h0 => ?_
  rw [h0, pow_zero] at hup
  exact lt_irrefl _ hup

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_NodeCoordinates_depth_pos_of_depthValueLaw_of_nodeEquation
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_NodeCoordinates_depth_pos_of_depthValueLaw_of_nodeEquation (solution)
