-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.isUnit_of_not_hasValue_nodeResidue_zero_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/0a436c95-282b-5e5f-b2a4-955fe56f68cf

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_nodeResidue_nonneg_of_regularityLaw
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_range_redRestrict_of_hasValue_nodeResidueFst
import Theorems.Thm_ModularCurve_NodeLocalized_exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_isUnit_of_not_hasValue_nodeResidue_zero_of_isLocalRing
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

noncomputable section

namespace SatL4

theorem ord_nonneg_of_mem {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem mem_of_ord_nonneg' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {f : F} (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  have h1 : v.adicValuation f ≤ 1 := v.adicValuation_le_one_iff.mpr (Or.inr h)
  obtain ⟨a, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one h1
  exact a.2

theorem hasValue_unique {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {f : F} {a b : K} (ha : v.HasValue f a) (hb : v.HasValue f b) : a = b := by
  obtain ⟨h1, h1'⟩ := ha
  obtain ⟨h2, h2'⟩ := hb
  have : algebraMap K v.ResidueField a = algebraMap K v.ResidueField b := by rw [← h1', ← h2']
  exact (algebraMap K v.ResidueField).injective this

theorem isAlgebraic_redRestrict {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (K₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K₀]
    [Algebra (ZMod q) k] (x : ↥(NodeLocalized.coeffSubring A K₀)) :
    IsAlgebraic (ZMod q) (NodeLocalized.redRestrict red K₀ x) := by
  have hxK : (x : AlgebraicClosure ℚ) ∈ K₀ := x.2.2
  have halgQ : IsAlgebraic ℚ (x : AlgebraicClosure ℚ) := by
    have : IsAlgebraic ℚ (⟨(x : AlgebraicClosure ℚ), hxK⟩ : ↥K₀) :=
      Algebra.IsAlgebraic.isAlgebraic _
    exact isAlgebraic_algebraMap_iff (algebraMap ↥K₀ (AlgebraicClosure ℚ)).injective |>.mpr this
  have halgZ : IsAlgebraic ℤ (x : AlgebraicClosure ℚ) := (IsFractionRing.isAlgebraic_iff ℤ ℚ _).mpr halgQ
  obtain ⟨p, hp0, hpx⟩ := halgZ
  set p' := p.primPart with hp'
  have hp'x : Polynomial.aeval (x : AlgebraicClosure ℚ) p' = 0 := by
    have hdec := Polynomial.eq_C_content_mul_primPart p
    have hc : (algebraMap ℤ (AlgebraicClosure ℚ)) p.content ≠ 0 := by
      rw [map_ne_zero_iff _ (algebraMap ℤ (AlgebraicClosure ℚ)).injective_int]
      exact (Polynomial.content_eq_zero_iff).not.mpr hp0
    rw [hdec, map_mul, Polynomial.aeval_C, mul_eq_zero] at hpx
    exact hpx.resolve_left hc
  have hprim : p'.IsPrimitive := Polynomial.isPrimitive_primPart p
  have hmap : p'.map (Int.castRingHom k) ≠ 0 := by
    intro h0
    have hdvd : Polynomial.C (q : ℤ) ∣ p' := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro n
      have hc : ((p'.coeff n : ℤ) : k) = 0 := by
        have := congrArg (fun r => Polynomial.coeff r n) h0
        simpa [Polynomial.coeff_map] using this
      exact (CharP.intCast_eq_zero_iff k q _).mp hc
    have hu : IsUnit (q : ℤ) := hprim _ hdvd
    have : (q : ℤ).natAbs = 1 := Int.isUnit_iff_natAbs_eq.mp hu
    simp at this
    exact (Fact.out : q.Prime).one_lt.ne' this
  have hxA : Polynomial.aeval ((⟨(x : AlgebraicClosure ℚ), x.2.1⟩ : ↥A)) p' = 0 := by
    have hinj : Function.Injective (algebraMap ↥A (AlgebraicClosure ℚ)) := Subtype.val_injective
    apply hinj
    rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂,
      RingHom.ext_int ((algebraMap ↥A (AlgebraicClosure ℚ)).comp (algebraMap ℤ ↥A)) (algebraMap ℤ (AlgebraicClosure ℚ))]
    rw [Polynomial.aeval_def] at hp'x
    exact hp'x
  have hred : Polynomial.eval₂ (Int.castRingHom k) (NodeLocalized.redRestrict red K₀ x) p' = 0 := by
    have h1 : NodeLocalized.redRestrict red K₀ x = red ⟨(x : AlgebraicClosure ℚ), x.2.1⟩ := rfl
    rw [h1, RingHom.ext_int (Int.castRingHom k) (red.comp (algebraMap ℤ ↥A)), ← Polynomial.hom_eval₂,
      ← Polynomial.aeval_def, hxA, map_zero]
  refine ⟨(p'.map (Int.castRingHom (ZMod q))), ?_, ?_⟩
  · intro h0; apply hmap
    have : p'.map (Int.castRingHom k) = (p'.map (Int.castRingHom (ZMod q))).map (algebraMap (ZMod q) k) := by
      rw [Polynomial.map_map]; congr 1; exact RingHom.ext_int _ _
    rw [this, h0, Polynomial.map_zero]
  · rw [Polynomial.aeval_def, Polynomial.eval₂_map, RingHom.ext_int ((algebraMap (ZMod q) k).comp (Int.castRingHom (ZMod q))) (Int.castRingHom k)]
    exact hred

end SatL4

open SatL4 in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    [IsLocalRing ↥(R.nodeIntegersOver K w)]
    (s : ↥(R.nodeIntegersOver K w))
    (hs : ¬ w.HasValue (R.nodeResidue₁ w ⟨s, s.2.1⟩ : ↥(modularFunctionFieldC k N)) (0 : k) ∨
      ¬ (arithFrobC q k N • w).HasValue (R.nodeResidue₂ w ⟨s, s.2.1⟩ : ↥(modularFunctionFieldC k N)) (0 : k)) :
    IsUnit s := by
  classical
  have hwss : w ∈ ssPlaces q N k := hW w hw
  have hregR := ModularCurve.PlaceSpecialization.ProlongationTuple.ord_nodeResidue_nonneg_of_regularityLaw R W hreg K w hw

  have hmem : ∀ t : ↥(R.nodeIntegersOver K w),
      (R.nodeResidue₁ w ⟨t, t.2.1⟩ : ↥(modularFunctionFieldC k N)) ∈ w.toValuationSubring := by
    intro t
    by_cases h0 : (R.nodeResidue₁ w ⟨t, t.2.1⟩ : ↥(modularFunctionFieldC k N)) = 0
    · rw [h0]; exact zero_mem _
    · exact mem_of_ord_nonneg' w (hregR t).1

  have hone : (⟨((1 : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))), (1 : ↥(R.nodeIntegersOver K w)).2.1⟩
      : ↥(R.nodeIntegers w)) = 1 := rfl
  have hzero : (⟨((0 : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))), (0 : ↥(R.nodeIntegersOver K w)).2.1⟩
      : ↥(R.nodeIntegers w)) = 0 := rfl
  have hmul : ∀ a b : ↥(R.nodeIntegersOver K w),
      (⟨((a * b : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))), (a * b).2.1⟩ : ↥(R.nodeIntegers w))
        = ⟨a, a.2.1⟩ * ⟨b, b.2.1⟩ := fun _ _ => rfl
  have hadd : ∀ a b : ↥(R.nodeIntegersOver K w),
      (⟨((a + b : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))), (a + b).2.1⟩ : ↥(R.nodeIntegers w))
        = ⟨a, a.2.1⟩ + ⟨b, b.2.1⟩ := fun _ _ => rfl
  let φ : ↥(R.nodeIntegersOver K w) →+* ↥w.toValuationSubring :=
    { toFun := fun t => ⟨_, hmem t⟩
      map_one' := Subtype.ext (by simp only [hone, map_one]; rfl)
      map_mul' := fun a b => Subtype.ext (by simp only [hmul, map_mul]; rfl)
      map_zero' := Subtype.ext (by simp only [hzero, map_zero]; rfl)
      map_add' := fun a b => Subtype.ext (by simp only [hadd, map_add]; rfl) }
  let ψ : ↥(R.nodeIntegersOver K w) →+* w.ResidueField := (residue ↥w.toValuationSubring).comp φ
  have hψ : ∀ t, ψ t = residue ↥w.toValuationSubring ⟨_, hmem t⟩ := fun t => rfl

  haveI : PerfectField k := IsAlgClosed.perfectField k
  haveI : IsCurveOver k ↥(modularFunctionFieldC k N) := ModularCurve.isCurveOver_modularFunctionFieldC_of_perfectField k N
  haveI : Module.Finite k w.ResidueField := IsCurveOver.finite_residueField w
  haveI : Algebra.IsIntegral k w.ResidueField := Algebra.IsIntegral.of_finite k w.ResidueField
  have hsurj : Function.Surjective (algebraMap k w.ResidueField) := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := w.ResidueField)).2

  letI : Algebra (ZMod q) k := ZMod.algebra k q
  haveI : CharP w.ResidueField q := charP_of_injective_algebraMap (algebraMap k w.ResidueField).injective q
  letI : Algebra (ZMod q) w.ResidueField := ZMod.algebra w.ResidueField q
  haveI : IsScalarTower (ZMod q) k w.ResidueField :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

  have hq2 : (Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial k) ≠ 0 := by
    exact FiniteField.X_pow_card_pow_sub_X_ne_zero k two_ne_zero (Fact.out : q.Prime).one_lt
  obtain ⟨K₁, hK₁fd, -, hK₁⟩ :=
    ModularCurve.NodeLocalized.exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict q A k red
      ((Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial k).roots.toFinset) (by
        intro a ha
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hq2, Polynomial.IsRoot.def] at ha
        simpa [sub_eq_zero] using ha)
  haveI := hK₁fd
  haveI : FiniteDimensional ℚ ↥(K ⊔ K₁) := IntermediateField.finiteDimensional_sup K K₁
  have hk₀ : ∀ a : k, a ^ (q ^ 2) = a → a ∈ Set.range (NodeLocalized.redRestrict red (K ⊔ K₁)) := by
    intro a ha
    have hmemS : a ∈ ((Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial k).roots.toFinset) := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hq2, Polynomial.IsRoot.def]
      simp [ha]
    obtain ⟨x, hx⟩ := hK₁ a hmemS
    exact ⟨⟨(x : AlgebraicClosure ℚ), x.2.1, (le_sup_right : K₁ ≤ K ⊔ K₁) x.2.2⟩, hx⟩
  have hKK'' : K ≤ K ⊔ K₁ := le_sup_left

  have hSS : ∀ t : ↥(R.nodeIntegersOver K w), (t : ↥(modularFunctionFieldBar (N * q))) ∈ R.nodeIntegersOver (K ⊔ K₁) w := by
    intro t
    refine ⟨t.2.1, ?_⟩
    have hmono : NodeLocalized.fieldOver (N * q) K ≤ NodeLocalized.fieldOver (N * q) (K ⊔ K₁) := by
      unfold NodeLocalized.fieldOver
      refine Subfield.closure_mono (Set.union_subset_union_left _ ?_)
      rintro _ ⟨c, rfl⟩
      exact ⟨⟨(c : AlgebraicClosure ℚ), hKK'' c.2⟩, rfl⟩
    exact hmono t.2.2

  have halg : ∀ t : ↥(R.nodeIntegersOver K w), IsAlgebraic (ZMod q) (ψ t) := by
    intro t
    obtain ⟨a, ha⟩ := hsurj (ψ t)
    have hval : w.HasValue (R.nodeResidue₁ w ⟨t, t.2.1⟩ : ↥(modularFunctionFieldC k N)) a := ⟨hmem t, by rw [← hψ, ha]⟩
    obtain ⟨x, hx⟩ := ModularCurve.PlaceSpecialization.ProlongationTuple.mem_range_redRestrict_of_hasValue_nodeResidueFst
      R hqN (K ⊔ K₁) w hwss hk₀ ⟨_, hSS t⟩ a hval
    rw [← ha, ← hx]
    exact (isAlgebraic_redRestrict red (K ⊔ K₁) x).algebraMap

  have hinv : ∀ s₀ : ↥(R.nodeIntegersOver K w), ψ s₀ ≠ 0 → ∃ t, ψ s₀ * ψ t = 1 := by
    intro s₀ hs₀
    let Ψ : Subalgebra (ZMod q) w.ResidueField :=
      { ψ.range with
        algebraMap_mem' := fun r => by
          obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective r
          rw [map_natCast]; exact natCast_mem ψ.range n }
    have hmemΨ : ψ s₀ ∈ Ψ := ⟨s₀, rfl⟩
    have : (ψ s₀)⁻¹ ∈ Ψ := Ψ.inv_mem_of_algebraic (x := ⟨ψ s₀, hmemΨ⟩) (halg s₀)
    obtain ⟨t, ht⟩ := this
    exact ⟨t, by rw [ht, mul_inv_cancel₀ hs₀]⟩

  have hs1 : ¬ w.HasValue (R.nodeResidue₁ w ⟨s, s.2.1⟩ : ↥(modularFunctionFieldC k N)) (0 : k) := by
    rcases hs with h | h
    · exact h
    · intro h0
      apply h
      have hpair : smulNodePair (arithFrobC q k N) w ∈ nodePairsOfPlaces (arithFrobC q k N) W :=
        smulNodePair_mem_nodePairsOfPlaces _ hw
      obtain ⟨c, hc1, hc2⟩ := hreg.2 (s : ↥(modularFunctionFieldBar (N * q))) s.2.1.1 s.2.1.2.1 _ hpair (by
        intro V hV
        exact ord_nonneg_of_mem V (s.2.1.2.2 V hV))
      have hc0 : c = 0 := hasValue_unique w hc1 h0
      subst hc0
      exact hc2
  have hψs : ψ s ≠ 0 := by
    intro h0; apply hs1
    exact ⟨hmem s, by rw [← hψ, h0, map_zero]⟩
  obtain ⟨t, ht⟩ := hinv s hψs
  have hker : s * t - 1 ∈ RingHom.ker ψ := by
    rw [RingHom.mem_ker, map_sub, map_mul, map_one, ht, sub_self]
  have hkerle : RingHom.ker ψ ≤ maximalIdeal ↥(R.nodeIntegersOver K w) :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top ψ)
  have hunit : IsUnit (s * t) := by
    have hm : s * t - 1 ∈ maximalIdeal ↥(R.nodeIntegersOver K w) := hkerle hker
    have hm' : 1 - s * t ∈ maximalIdeal ↥(R.nodeIntegersOver K w) := by
      rw [← neg_sub]; exact Submodule.neg_mem _ hm
    have hnu : ¬ IsUnit (1 - s * t) := (IsLocalRing.mem_maximalIdeal _).mp hm'
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (1 - s * t) with h | h
    · exact (hnu h).elim
    · simpa using h
  exact isUnit_of_mul_isUnit_left hunit

end

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_isUnit_of_not_hasValue_nodeResidue_zero_of_isLocalRing
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_isUnit_of_not_hasValue_nodeResidue_zero_of_isLocalRing (solution)
