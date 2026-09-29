-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.spData_mem_admissible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/a740c957-84d9-51ad-832f-e8d7c7fcc81d

import Mathlib
import Definitions.Def_ModularCurve_AnnulusSpecializationLevel
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_arithFrobC_smul_mem_ssPlaces_univ
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_spData_mem_admissible
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply"
p2m_attr_erase "simp" "WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [PerfectField k] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} {R : P.ProlongationTuple} (hqN : ¬ q ∣ N)
    {W : Finset (Place k (modularFunctionFieldC k N))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (dat : R.AnnulusDatumLevel W)
    (hcorrFst : ∀ w ∈ W, (∀ v ∈ W, dat.corrFst w v = 0) ∧ Divisor.degree (dat.corrFst w) = -1)
    (hcorrSnd : ∀ w ∈ W, (∀ v ∈ W, dat.corrSnd w v = 0) ∧ Divisor.degree (dat.corrSnd w) = -1)
    (a : ProlongationTuple.TwistVectorLevel (k := k) (N := N) W)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (ha₁ : Divisor.degree (P.fstDiv D) = -∑ w ∈ W, dat.endOrderFst a D w)
    (ha₂ : Divisor.degree (P.sndDiv D) = -∑ w ∈ W, dat.endOrderSnd a D w) :
    dat.spData a D ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k N) W) := by
  classical
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

  have hdegMap : ∀ (f : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → Place k (modularFunctionFieldC k N))
      (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      Divisor.degree (Finsupp.mapDomain f E) = Divisor.degree E := by
    intro f E
    induction E using Finsupp.induction_linear with
    | zero => simp
    | add E₁ E₂ h₁ h₂ => rw [Finsupp.mapDomain_add, map_add, map_add, h₁, h₂]
    | single V n =>
      rw [Finsupp.mapDomain_single, Divisor.degree_single, Divisor.degree_single,
        ModularCurve.place_deg_eq_one_of_isAlgClosed k N (f V), ModularCurve.deg_eq_one_modularFunctionFieldBar (N * q) V]
  have hdegCorrF : Divisor.degree (∑ w ∈ W, dat.endOrderFst a D w • dat.corrFst w) = -∑ w ∈ W, dat.endOrderFst a D w := by
    rw [map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [map_zsmul, (hcorrFst w hw).2, smul_eq_mul, mul_neg, mul_one]
  have hdegCorrS : Divisor.degree (∑ w ∈ W, dat.endOrderSnd a D w • dat.corrSnd w) = -∑ w ∈ W, dat.endOrderSnd a D w := by
    rw [map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [map_zsmul, (hcorrSnd w hw).2, smul_eq_mul, mul_neg, mul_one]

  have hFix : ∀ w ∈ W, frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w :=
    fun w hw => ModularCurve.frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
      k N hqN data hKr w ((hW w).mp hw)
  have hφW : ∀ w ∈ W, arithFrobC q k N • w ∈ W := fun w hw =>
    (hW _).mpr (ModularCurve.arithFrobC_smul_mem_ssPlaces_univ q N k w ((hW w).mp hw))
  have hFixφ : ∀ w ∈ W, frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (arithFrobC q k N • w))
      = arithFrobC q k N • w := fun w hw => hFix _ (hφW w hw)

  have hmapFst : ∀ w ∈ W, Finsupp.mapDomain P.reduceFst (P.fstDiv D) w = 0 := by
    intro w hw
    rw [Finsupp.mapDomain, Finsupp.sum_apply]
    refine Finset.sum_eq_zero fun V hV => ?_
    dsimp only
    rw [Finsupp.single_apply, if_neg]
    intro hVw
    have hV' : P.IsStrictFst V := by
      by_contra hns
      rw [Finsupp.mem_support_iff, PlaceSpecialization.fstDiv, Finsupp.filter_apply_neg _ _ hns] at hV
      exact hV rfl
    exact hV'.2 (hVw ▸ hFix w hw)
  have hmapSnd : ∀ w ∈ W, Finsupp.mapDomain P.reduceSnd (P.sndDiv D) (arithFrobC q k N • w) = 0 := by
    intro w hw
    rw [Finsupp.mapDomain, Finsupp.sum_apply]
    refine Finset.sum_eq_zero fun V hV => ?_
    dsimp only
    rw [Finsupp.single_apply, if_neg]
    intro hVw
    have hV' : P.IsStrictSnd V := by
      by_contra hns
      rw [Finsupp.mem_support_iff, PlaceSpecialization.sndDiv, Finsupp.filter_apply_neg _ _ hns] at hV
      exact hV rfl
    exact hV'.2 (hVw ▸ hFixφ w hw)

  have hcorrF0 : ∀ v ∈ W, (∑ w ∈ W, dat.endOrderFst a D w • dat.corrFst w) v = 0 := by
    intro v hv
    rw [Finsupp.finsetSum_apply]
    exact Finset.sum_eq_zero fun w hw => by rw [Finsupp.smul_apply, (hcorrFst w hw).1 v hv, smul_zero]
  have hcorrS0 : ∀ v ∈ W, (∑ w ∈ W, dat.endOrderSnd a D w • dat.corrSnd w) (arithFrobC q k N • v) = 0 := by
    intro v hv
    rw [Finsupp.finsetSum_apply]
    exact Finset.sum_eq_zero fun w hw => by rw [Finsupp.smul_apply, (hcorrSnd w hw).1 _ (hφW v hv), smul_zero]
  rw [GluingData.mem_admissible]
  dsimp only [ProlongationTuple.AnnulusDatumLevel.spData]
  refine ⟨?_, ?_, ?_⟩
  · rw [Divisor.mem_degZero, map_sub, hdegMap, hdegCorrF, ha₁, sub_self]
  · rw [Divisor.mem_degZero, map_sub, hdegMap, hdegCorrS, ha₂, sub_self]
  · intro s hs
    obtain ⟨w, hw, rfl⟩ := (mem_nodePairsOfPlaces_iff _ W s).mp hs
    dsimp only [smulNodePair]
    refine ⟨?_, ?_⟩
    · rw [Finsupp.sub_apply, hmapFst w hw, hcorrF0 w hw, sub_zero]
    · rw [Finsupp.sub_apply, hmapSnd w hw, hcorrS0 w hw, sub_zero]

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_spData_mem_admissible
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_spData_mem_admissible (solution)
