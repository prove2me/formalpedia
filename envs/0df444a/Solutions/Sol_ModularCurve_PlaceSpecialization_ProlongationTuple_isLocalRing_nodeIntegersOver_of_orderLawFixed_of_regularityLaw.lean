-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.isLocalRing_nodeIntegersOver_of_orderLawFixed_of_regularityLaw
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/575026c0-b6db-5b91-9e1e-75d943a26fd8

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_and_hasValue_nodeResidueFst_of_hasValue
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
import Theorems.Thm_ModularCurve_isRational_place_modularFunctionFieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_isLocalRing_nodeIntegersOver_of_orderLawFixed_of_regularityLaw
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.NodeLocalized
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace LocPrime

private theorem _root_.AlgebraicCurve.Place.HasValue.add' {K F : Type*} [Field K] [Field F] [Algebra K F] {v : Place K F}
    {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_isLocalRing_nodeIntegersOver_of_orderLawFixed_of_regularityLaw.AlgebraicCurve.Place.HasValue.add'" "AlgebraicCurve.Place.HasValue.add'"

theorem inv_mem_of_isUnit {F : Type*} [Field F] (V : ValuationSubring F) {x : F} (hx : x ∈ V)
    (hu : IsUnit (⟨x, hx⟩ : ↥V)) : x⁻¹ ∈ V := by
  obtain ⟨u, hu⟩ := hu
  have hcoe : ((u : ↥V) : F) = x := by rw [hu]
  have hinv : (((u⁻¹ : (↥V)ˣ) : ↥V) : F) = x⁻¹ := by
    have h1 : x * (((u⁻¹ : (↥V)ˣ) : ↥V) : F) = 1 := by
      rw [← hcoe, ← MulMemClass.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, OneMemClass.coe_one]
    exact (inv_eq_of_mul_eq_one_right h1).symm
  rw [← hinv]
  exact SetLike.coe_mem _

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

variable (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
  (hO : R.OrderLawFixed)
  (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
  (hreg : R.RegularityLaw W)
  (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
  (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)

include hreg hw in

theorem exists_value (f : ↥(modularFunctionFieldBar (N * q))) (hf : f ∈ R.nodeIntegers w) :
    ∃ c : k, w.HasValue (R.residue₁ ⟨f, hf.1⟩ : ↥(modularFunctionFieldC k N)) c ∧
      (arithFrobC q k N • w).HasValue (R.residue₂ ⟨f, hf.2.1⟩ : ↥(modularFunctionFieldC k N)) c :=
  hreg.2 f hf.1 hf.2.1 (smulNodePair (arithFrobC q k N) w) (smulNodePair_mem_nodePairsOfPlaces _ hw)
    (fun V hV => R.ord_nonneg_of_mem_nodeIntegers hf hV)

include hqN hO hW hreg hw in

theorem inv_mem_of_hasValue {f : ↥(modularFunctionFieldBar (N * q))} (hf : f ∈ R.nodeIntegersOver K w)
    {c : k} (hc : w.HasValue (R.residue₁ ⟨f, hf.1.1⟩ : ↥(modularFunctionFieldC k N)) c) (hc0 : c ≠ 0) :
    f⁻¹ ∈ R.nodeIntegersOver K w := by
  haveI := ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)
  have hfix := ModularCurve.frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
    k N hqN data hKr w (hW w hw)
  obtain ⟨c₂, hc₂, hc₂'⟩ := exists_value R W hreg w hw f hf.1
  have hcc : c₂ = c := hc₂.unique hc
  have hc₂0 : c₂ ≠ 0 := by rw [hcc]; exact hc0

  have h₁ : f⁻¹ ∈ R.R₁.integers := by
    apply inv_mem_of_isUnit _ hf.1.1
    apply R.R₁.isUnit_of_residue_ne_zero
    intro h0
    apply hc.ne_zero hc0
    rw [residue₁_apply, h0, map_zero]

  have h₂ : f⁻¹ ∈ R.R₂.integers := by
    apply inv_mem_of_isUnit _ hf.1.2.1
    apply R.R₂.isUnit_of_residue_ne_zero
    intro h0
    apply hc₂'.ne_zero hc₂0
    rw [residue₂_apply, h0, map_zero]

  have h₃ : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
      f⁻¹ ∈ V.toValuationSubring := by
    intro V hV
    have hfV : f ∈ V.toValuationSubring := hf.1.2.2 V hV
    obtain ⟨c', hc', -⟩ := V.exists_hasValue_of_surjective (ModularCurve.isRational_place_modularFunctionFieldBar _ V) hfV
    obtain ⟨hcA, hred⟩ := R.mem_and_hasValue_nodeResidueFst_of_hasValue hO W hW hreg w hw hfix f hf.1 V hV c' hc'
    have hc'0 : c' ≠ 0 := by
      intro h0
      apply hc0
      have : red ⟨c', hcA⟩ = c := hred.unique hc
      rw [← this]
      have hz : (⟨c', hcA⟩ : ↥A) = 0 := Subtype.ext h0
      rw [hz, map_zero]
    exact (hc'.inv hc'0).mem
  refine ⟨⟨h₁, h₂, h₃⟩, ?_⟩
  change ((f : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))⁻¹ ∈ fieldOver (N * q) K
  exact inv_mem hf.2

end LocPrime

open LocPrime

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W) :
    IsLocalRing ↥(R.nodeIntegersOver K w) := by
  classical

  let ρ : ↥(R.nodeIntegersOver K w) →+* ↥(modularFunctionFieldC k N) :=
    (R.nodeResidue₁ w).comp (Subring.inclusion (R.nodeIntegersOver_le K w))
  have hρ : ∀ g : ↥(R.nodeIntegersOver K w), ρ g = R.residue₁ ⟨(g : ↥(modularFunctionFieldBar (N * q))), g.2.1.1⟩ :=
    fun g => rfl

  have hval : ∀ g : ↥(R.nodeIntegersOver K w), ∃ c : k, w.HasValue (ρ g) c := fun g => by
    obtain ⟨c, hc, -⟩ := exists_value R W hreg w hw (g : ↥(modularFunctionFieldBar (N * q))) g.2.1
    exact ⟨c, hc⟩
  have hunit : ∀ g : ↥(R.nodeIntegersOver K w), ∀ c : k, w.HasValue (ρ g) c → c ≠ 0 → IsUnit g := by
    intro g c hc hc0
    have hinv := inv_mem_of_hasValue R hqN hO W hW hreg K w hw g.2 hc hc0
    have hg0 : (g : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := by
      intro h0
      apply hc.ne_zero hc0
      rw [hρ]
      have : (⟨(g : ↥(modularFunctionFieldBar (N * q))), g.2.1.1⟩ : ↥R.R₁.integers) = 0 := Subtype.ext h0
      rw [this, map_zero]
    refine ⟨⟨g, ⟨(g : ↥(modularFunctionFieldBar (N * q)))⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hg0),
      Subtype.ext (inv_mul_cancel₀ hg0)⟩, rfl⟩
  have hzero : ∀ g : ↥(R.nodeIntegersOver K w), g ∈ nonunits ↥(R.nodeIntegersOver K w) → w.HasValue (ρ g) 0 := by
    intro g hg
    obtain ⟨c, hc⟩ := hval g
    by_cases hc0 : c = 0
    · rw [hc0] at hc; exact hc
    · exact absurd (hunit g c hc hc0) hg
  apply IsLocalRing.of_nonunits_add
  intro a b ha hb hab
  obtain ⟨u, hu⟩ := hab.exists_right_inv
  obtain ⟨cu, hcu⟩ := hval u
  have h1 : w.HasValue (ρ ((a + b) * u)) ((0 + 0) * cu) := by
    rw [map_mul, map_add]
    exact ((hzero a ha).add' (hzero b hb)).mul hcu
  rw [hu, map_one, add_zero, zero_mul] at h1
  exact zero_ne_one (h1.unique w.hasValue_one)

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_isLocalRing_nodeIntegersOver_of_orderLawFixed_of_regularityLaw
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_isLocalRing_nodeIntegersOver_of_orderLawFixed_of_regularityLaw (solution)
