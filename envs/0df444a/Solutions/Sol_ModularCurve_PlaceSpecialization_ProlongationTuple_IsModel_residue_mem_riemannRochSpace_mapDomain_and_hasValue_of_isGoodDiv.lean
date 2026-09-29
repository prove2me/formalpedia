-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.residue_mem_riemannRochSpace_mapDomain_and_hasValue_of_isGoodDiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/c4f8b430-05a1-5a3d-be8a-f4493fcecdb1

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_residue_mem_riemannRochSpace_mapDomain_and_hasValue_of_isGoodDiv
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom"
p2m_attr_erase "simp" "ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl"
p2m_attr_erase "simp" "ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero"
p2m_attr_erase "simp" "TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_residue_mem_riemannRochSpace_mapDomain_and_hasValue_of_isGoodDiv.ModularCurve ModularCurve.PlaceSpecialization"
open ModularCurve.PlaceSpecialization.ProlongationTuple

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple PlaceSpecialization.fstDiv PlaceSpecialization.sndDiv modularFunctionFieldBar ModularPolynomialData coeffMap coeffMap_single algebraMap_laurentSeries_eq_single modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff frobOnPlacesGeomLevel_injective KroneckerCongruence smulNodePair smulNodePair_fst smulNodePair_snd nodePairsOfPlaces smulNodePair_mem_nodePairsOfPlaces ssPlaces jGeomGen jNGeomGen frobeniusGeomLevel_jGeomGen_sub_pow frobeniusGeomLevel_jNGeomGen_sub_pow IsAffineGeomPlace arithFrobC modularFunctionFieldFullC hasPrincipalDivisors_modularFunctionFieldBar_unconditional frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed"
namespace RespairN
p2m_open "ModularCurve"

section Finsupp

theorem neg_mapDomain_filter_le {α β : Type*} (r : α → β) (Q : α → Prop) {hQ : DecidablePred Q}
    (X Y : α →₀ ℤ) (hXY : ∀ a, -Y a ≤ X a) (b : β) :
    -(Finsupp.mapDomain r (Y.filter Q) b) ≤ Finsupp.mapDomain r (X.filter Q) b := by
  have h1 : -(Y.filter Q) ≤ X.filter Q := by
    intro a
    simp only [Finsupp.coe_neg, Pi.neg_apply, Finsupp.filter_apply]
    split_ifs
    · exact hXY a
    · simp
  have h2 := Finsupp.le_def.mp (Finsupp.mapDomain_mono (f := r) h1) b
  have h3 : Finsupp.mapDomain r (-(Y.filter Q)) = -Finsupp.mapDomain r (Y.filter Q) :=
    map_neg (Finsupp.mapDomain.addMonoidHom r) _
  rw [h3] at h2
  exact h2

theorem mapDomain_nonneg {α β : Type*} (r : α → β) (X : α →₀ ℤ) (hX : ∀ a, 0 ≤ X a) (b : β) :
    0 ≤ Finsupp.mapDomain r X b := by
  have h : (0 : α →₀ ℤ) ≤ X := fun a => by simpa using hX a
  have h2 := Finsupp.le_def.mp (Finsupp.mapDomain_mono (f := r) h) b
  simpa using h2

theorem filter_nonneg {α : Type*} (Q : α → Prop) {hQ : DecidablePred Q} (X : α →₀ ℤ) (hX : ∀ a, 0 ≤ X a)
    (a : α) : 0 ≤ X.filter Q a := by
  rw [Finsupp.filter_apply]
  split_ifs
  · exact hX a
  · exact le_rfl

theorem mapDomain_filter_nonneg_at {α β : Type*} (r : α → β) (Q : α → Prop) {hQ : DecidablePred Q}
    (X : α →₀ ℤ) (b : β) (hX : ∀ a, Q a → r a = b → 0 ≤ X a) :
    0 ≤ Finsupp.mapDomain r (X.filter Q) b := by
  classical
  unfold Finsupp.mapDomain
  rw [Finsupp.sum_apply, Finsupp.sum]
  apply Finset.sum_nonneg
  intro a _
  simp only [Finsupp.single_apply]
  split_ifs with h
  · rw [Finsupp.filter_apply]
    split_ifs with hq
    · exact hX a hq h
    · exact le_rfl
  · exact le_rfl

end Finsupp

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
  {red : A →+* k} {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

local notation "𝕂" => AlgebraicClosure ℚ

theorem frob_frob_reduceSnd_ne_of_isStrictFst (P : PlaceSpecialization A q N data hKr k red hα hβ)
    {W : Place 𝕂 ↥(modularFunctionFieldBar (N * q))} (h : P.IsStrictFst W) : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceSnd W)) ≠ P.reduceSnd W := by
  intro hfix
  apply h.2
  rw [← h.1] at hfix
  exact frobOnPlacesGeomLevel_injective k N data hKr hfix

theorem frob_frob_reduceFst_ne_of_isStrictSnd (P : PlaceSpecialization A q N data hKr k red hα hβ)
    {W : Place 𝕂 ↥(modularFunctionFieldBar (N * q))} (h : P.IsStrictSnd W) : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst W)) ≠ P.reduceFst W := by
  intro hfix
  apply h.2
  rw [h.1] at hfix
  exact frobOnPlacesGeomLevel_injective k N data hKr hfix

theorem apply_eq_zero_of_reduceFst_fixed (P : PlaceSpecialization A q N data hKr k red hα hβ)
    {D : Divisor 𝕂 ↥(modularFunctionFieldBar (N * q))} (hgood : P.IsGoodDiv D) {v : Place k ↥(modularFunctionFieldC k N)}
    (hv : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v) (W : Place 𝕂 ↥(modularFunctionFieldBar (N * q))) (hW : P.reduceFst W = v) : D W = 0 := by
  by_contra h
  rcases hgood W (Finsupp.mem_support_iff.mpr h) with hs | hs
  · exact hs.2 (by rw [hW]; exact hv)
  · exact frob_frob_reduceFst_ne_of_isStrictSnd P hs (by rw [hW]; exact hv)

theorem apply_eq_zero_of_reduceSnd_fixed (P : PlaceSpecialization A q N data hKr k red hα hβ)
    {D : Divisor 𝕂 ↥(modularFunctionFieldBar (N * q))} (hgood : P.IsGoodDiv D) {v : Place k ↥(modularFunctionFieldC k N)}
    (hv : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v) (W : Place 𝕂 ↥(modularFunctionFieldBar (N * q))) (hW : P.reduceSnd W = v) : D W = 0 := by
  by_contra h
  rcases hgood W (Finsupp.mem_support_iff.mpr h) with hs | hs
  · exact frob_frob_reduceSnd_ne_of_isStrictFst P hs (by rw [hW]; exact hv)
  · exact hs.2 (by rw [hW]; exact hv)

theorem isAffineGeomPlace_frob {v : Place k ↥(modularFunctionFieldC k N)} (hv : IsAffineGeomPlace k N v) :
    IsAffineGeomPlace k N (frobOnPlacesGeomLevel k N data hKr v) := by
  have hq1 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have e₁ : frobeniusGeomLevel k N data hKr (jGeomGen k N) = jGeomGen k N ^ q := by
    have h := frobeniusGeomLevel_jGeomGen_sub_pow k N data hKr (0 : k)
    simp only [zero_pow hq1, map_zero, sub_zero] at h
    exact h
  have e₂ : frobeniusGeomLevel k N data hKr (jNGeomGen k N) = jNGeomGen k N ^ q := by
    have h := frobeniusGeomLevel_jNGeomGen_sub_pow k N data hKr (0 : k)
    simp only [zero_pow hq1, map_zero, sub_zero] at h
    exact h
  refine ⟨?_, ?_⟩
  · rw [mem_frobOnPlacesGeomLevel_iff, e₁]
    exact pow_mem hv.1 q
  · rw [mem_frobOnPlacesGeomLevel_iff, e₂]
    exact pow_mem hv.2 q

section Constants

variable {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

theorem algebraMap_mem_integers₁ (c : A) : algebraMap 𝕂 ↥(modularFunctionFieldBar (N * q)) (c : 𝕂) ∈ R.R₁.integers :=
  (R.R₁.algebraMap_mem_iff _).mpr c.2

theorem algebraMap_mem_integers₂ (c : A) : algebraMap 𝕂 ↥(modularFunctionFieldBar (N * q)) (c : 𝕂) ∈ R.R₂.integers :=
  (R.R₂.algebraMap_mem_iff _).mpr c.2

theorem ι_algebraMap (x : ResidueField A) :
    R.ι (algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) N) x)
      = algebraMap k ↥(modularFunctionFieldC k N) (R.redBar x) := by
  apply Subtype.ext
  rw [R.ι_coe]
  change coeffMap R.redBar (algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) x)
    = algebraMap k (LaurentSeries k) (R.redBar x)
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem algebraMap_mem_riemannRochSpace {K L : Type*} [Field K] [Field L] [Algebra K L]
    {E : Divisor K L} (hE : ∀ v, 0 ≤ E v) (c : K) : algebraMap K L c ∈ riemannRochSpace E := by
  intro v
  refine (Place.adicValuation_algebraMap_le_one v c).trans ?_
  rw [← WithZero.exp_zero, WithZero.exp_le_exp]
  exact hE v

theorem exists_residue_add_ne_zero (G : ↥(modularFunctionFieldBar (N * q))) (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers) :
    ∃ c : A,
      R.R₁.residue ⟨G + algebraMap 𝕂 ↥(modularFunctionFieldBar (N * q)) (c : 𝕂), add_mem h₁ (algebraMap_mem_integers₁ R c)⟩ ≠ 0 ∧
      R.R₂.residue ⟨G + algebraMap 𝕂 ↥(modularFunctionFieldBar (N * q)) (c : 𝕂), add_mem h₂ (algebraMap_mem_integers₂ R c)⟩ ≠ 0 := by
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  haveI : Infinite (ResidueField A) := inferInstance
  let r₁ := R.R₁.residue ⟨G, h₁⟩
  let r₂ := R.R₂.residue ⟨G, h₂⟩
  obtain ⟨xbar, hx⟩ : ∃ xbar : ResidueField A,
      algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) N) xbar ≠ -r₁ ∧
      algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) N) xbar ≠ -r₂ := by
    by_contra hall
    push_neg at hall
    have hsub : (Set.univ : Set (ResidueField A)) ⊆
        ((algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) N)) ⁻¹' {-r₁, -r₂}) := by
      intro x _
      rcases eq_or_ne (algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) N) x) (-r₁) with h | h
      · exact Or.inl h
      · exact Or.inr (hall x h)
    have hfin : (Set.univ : Set (ResidueField A)).Finite :=
      ((Set.toFinite {-r₁, -r₂}).preimage
        ((algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) N)).injective.injOn)).subset hsub
    exact Set.infinite_univ hfin
  obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective xbar
  refine ⟨c, ?_, ?_⟩
  · have : (⟨G + algebraMap 𝕂 ↥(modularFunctionFieldBar (N * q)) (c : 𝕂), add_mem h₁ (algebraMap_mem_integers₁ R c)⟩ : R.R₁.integers)
        = ⟨G, h₁⟩ + ⟨_, algebraMap_mem_integers₁ R c⟩ := rfl
    rw [this, map_add, R.R₁.residue_algebraMap]
    intro h0
    exact hx.1 (eq_neg_of_add_eq_zero_right h0)
  · have : (⟨G + algebraMap 𝕂 ↥(modularFunctionFieldBar (N * q)) (c : 𝕂), add_mem h₂ (algebraMap_mem_integers₂ R c)⟩ : R.R₂.integers)
        = ⟨G, h₂⟩ + ⟨_, algebraMap_mem_integers₂ R c⟩ := rfl
    rw [this, map_add, R.R₂.residue_algebraMap]
    intro h0
    exact hx.2 (eq_neg_of_add_eq_zero_right h0)

end Constants

section Bounds

variable {P : PlaceSpecialization A q N data hKr k red hα hβ} (hqN : ¬ q ∣ N) (R : ProlongationTuple P)
  (hR : R.IsModel) {W : Finset (Place k ↥(modularFunctionFieldC k N))} (hRL : R.RegularityLaw W)
  {D : Divisor 𝕂 ↥(modularFunctionFieldBar (N * q))} (hD : ∀ V, 0 ≤ D V) (hgood : P.IsGoodDiv D)
  {f : ↥(modularFunctionFieldBar (N * q))} (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
  (hne₁ : R.R₁.residue ⟨f, h₁⟩ ≠ 0) (hne₂ : R.R₂.residue ⟨f, h₂⟩ ≠ 0)
  (hfD : ∀ V : Place 𝕂 ↥(modularFunctionFieldBar (N * q)), -D V ≤ V.ord f)

include hqN hR hRL hD hgood hne₁ hne₂ hfD

theorem bound₁ (v : Place k ↥(modularFunctionFieldC k N)) :
    -(Finsupp.mapDomain P.reduceFst (P.fstDiv D) v) ≤ v.ord (R.residue₁ ⟨f, h₁⟩ : ↥(modularFunctionFieldC k N)) := by
  classical
  have hf0 : f ≠ 0 := by
    rintro rfl
    apply hne₁
    have : (⟨(0 : ↥(modularFunctionFieldBar (N * q))), h₁⟩ : R.R₁.integers) = 0 := rfl
    rw [this, map_zero]
  obtain ⟨D', hD', -⟩ :=
    (hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)).exists_divisor f hf0
  have hXY : ∀ V, -D V ≤ D' V := fun V => by rw [hD' V]; exact hfD V
  have h0 : 0 ≤ Finsupp.mapDomain P.reduceFst (P.fstDiv D) v := by
    unfold PlaceSpecialization.fstDiv
    exact mapDomain_nonneg _ _ (filter_nonneg _ D hD) _
  have hres : (R.residue₁ ⟨f, h₁⟩ : ↥(modularFunctionFieldC k N)) ≠ 0 := by
    rw [residue₁_apply]
    exact (map_ne_zero_iff R.ι R.ι.injective).mpr hne₁
  by_cases hv : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v
  · have hnopole : ∀ V : Place 𝕂 ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = v → 0 ≤ V.ord f := fun V hV => by
      have h := hfD V
      rw [apply_eq_zero_of_reduceFst_fixed P hgood hv V hV] at h
      simpa using h
    by_cases haff : IsAffineGeomPlace k N v
    · have hreg := (hRL.1 f h₁ h₂ v hv haff hnopole).1 hres
      omega
    · obtain ⟨⟨C, hC, hCv⟩, -⟩ :=
        exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace hqN P v haff
      have hlaw := hR.2.2.1 f h₁ h₂ hne₁ hne₂ D' hD' C hC
      rw [hCv] at hlaw
      have hb : 0 ≤ Finsupp.mapDomain P.reduceFst (D'.filter (IsInftySide P)) v :=
        mapDomain_filter_nonneg_at _ _ D' v (fun V _ hV => by rw [hD']; exact hnopole V hV)
      omega
  · have hlaw := hR.1 f h₁ h₂ hne₁ hne₂ D' hD' v hv
    exact (neg_mapDomain_filter_le P.reduceFst P.IsStrictFst D' D hXY v).trans_eq hlaw

theorem bound₂ (v : Place k ↥(modularFunctionFieldC k N)) :
    -(Finsupp.mapDomain P.reduceSnd (P.sndDiv D) v) ≤ v.ord (R.residue₂ ⟨f, h₂⟩ : ↥(modularFunctionFieldC k N)) := by
  classical
  have hf0 : f ≠ 0 := by
    rintro rfl
    apply hne₂
    have : (⟨(0 : ↥(modularFunctionFieldBar (N * q))), h₂⟩ : R.R₂.integers) = 0 := rfl
    rw [this, map_zero]
  obtain ⟨D', hD', -⟩ :=
    (hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)).exists_divisor f hf0
  have hXY : ∀ V, -D V ≤ D' V := fun V => by rw [hD' V]; exact hfD V
  have h0 : 0 ≤ Finsupp.mapDomain P.reduceSnd (P.sndDiv D) v := by
    unfold PlaceSpecialization.sndDiv
    exact mapDomain_nonneg _ _ (filter_nonneg _ D hD) _
  have hres : (R.residue₂ ⟨f, h₂⟩ : ↥(modularFunctionFieldC k N)) ≠ 0 := by
    rw [residue₂_apply]
    exact (map_ne_zero_iff R.ι R.ι.injective).mpr hne₂
  by_cases hv : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v
  · by_cases haff : IsAffineGeomPlace k N v
    ·
      have hu : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v)) = frobOnPlacesGeomLevel k N data hKr v := by rw [hv]
      have huaff : IsAffineGeomPlace k N (frobOnPlacesGeomLevel k N data hKr v) := isAffineGeomPlace_frob haff
      have hnopole : ∀ V : Place 𝕂 ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = frobOnPlacesGeomLevel k N data hKr v → 0 ≤ V.ord f := fun V hV => by
        have h := hfD V
        rw [apply_eq_zero_of_reduceFst_fixed P hgood hu V hV] at h
        simpa using h
      have hreg := (hRL.1 f h₁ h₂ (frobOnPlacesGeomLevel k N data hKr v) hu huaff hnopole).2 hres
      rw [hv] at hreg
      omega
    · obtain ⟨-, ⟨C, hC, hCv⟩⟩ :=
        exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace hqN P v haff
      have hlaw := hR.2.2.2 f h₁ h₂ hne₁ hne₂ D' hD' C hC
      rw [hCv] at hlaw
      have hnopole : ∀ V : Place 𝕂 ↥(modularFunctionFieldBar (N * q)), P.reduceSnd V = v → 0 ≤ V.ord f := fun V hV => by
        have h := hfD V
        rw [apply_eq_zero_of_reduceSnd_fixed P hgood hv V hV] at h
        simpa using h
      have hb : 0 ≤ Finsupp.mapDomain P.reduceSnd (D'.filter (IsZeroSide P)) v :=
        mapDomain_filter_nonneg_at _ _ D' v (fun V _ hV => by rw [hD']; exact hnopole V hV)
      omega
  · have hlaw := hR.2.1 f h₁ h₂ hne₁ hne₂ D' hD' v hv
    exact (neg_mapDomain_filter_le P.reduceSnd P.IsStrictSnd D' D hXY v).trans_eq hlaw

end Bounds

theorem main {P : PlaceSpecialization A q N data hKr k red hα hβ} (hqN : ¬ q ∣ N)
    {W : Finset (Place k ↥(modularFunctionFieldC k N))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W)
    (D : Divisor 𝕂 ↥(modularFunctionFieldBar (N * q))) (hD : ∀ V, 0 ≤ D V) (hgood : P.IsGoodDiv D)
    (G : ↥(modularFunctionFieldBar (N * q))) (hGmem : G ∈ riemannRochSpace D)
    (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers) :
    (R.residue₁ ⟨G, h₁⟩ : ↥(modularFunctionFieldC k N)) ∈ riemannRochSpace (Finsupp.mapDomain P.reduceFst (P.fstDiv D)) ∧
    (R.residue₂ ⟨G, h₂⟩ : ↥(modularFunctionFieldC k N)) ∈ riemannRochSpace (Finsupp.mapDomain P.reduceSnd (P.sndDiv D)) ∧
    (∀ w ∈ W, ∃ c : k,
      w.HasValue (R.residue₁ ⟨G, h₁⟩ : ↥(modularFunctionFieldC k N)) c ∧
      (arithFrobC q k N • w).HasValue (R.residue₂ ⟨G, h₂⟩ : ↥(modularFunctionFieldC k N)) c) := by
  classical
  have hGD : ∀ V : Place 𝕂 ↥(modularFunctionFieldBar (N * q)), -D V ≤ V.ord G := fun V => by
    rcases (mem_riemannRochSpace_iff.mp hGmem) V with h0 | h
    · rw [h0, Place.ord_zero]
      have := hD V
      omega
    · exact h

  obtain ⟨c, hc₁, hc₂⟩ := exists_residue_add_ne_zero R G h₁ h₂
  set G' := G + algebraMap 𝕂 ↥(modularFunctionFieldBar (N * q)) (c : 𝕂) with hG'
  have h₁' : G' ∈ R.R₁.integers := add_mem h₁ (algebraMap_mem_integers₁ R c)
  have h₂' : G' ∈ R.R₂.integers := add_mem h₂ (algebraMap_mem_integers₂ R c)
  have hG'mem : G' ∈ riemannRochSpace D := add_mem hGmem (algebraMap_mem_riemannRochSpace hD _)
  have hG'D : ∀ V : Place 𝕂 ↥(modularFunctionFieldBar (N * q)), -D V ≤ V.ord G' := fun V => by
    rcases (mem_riemannRochSpace_iff.mp hG'mem) V with h0 | h
    · rw [h0, Place.ord_zero]
      have := hD V
      omega
    · exact h

  have hD₁ : ∀ v, 0 ≤ Finsupp.mapDomain P.reduceFst (P.fstDiv D) v := fun v => by
    unfold PlaceSpecialization.fstDiv
    exact mapDomain_nonneg _ _ (filter_nonneg _ D hD) v
  have hD₂ : ∀ v, 0 ≤ Finsupp.mapDomain P.reduceSnd (P.sndDiv D) v := fun v => by
    unfold PlaceSpecialization.sndDiv
    exact mapDomain_nonneg _ _ (filter_nonneg _ D hD) v

  have hm₁ : (R.residue₁ ⟨G', h₁'⟩ : ↥(modularFunctionFieldC k N))
      ∈ riemannRochSpace (Finsupp.mapDomain P.reduceFst (P.fstDiv D)) := by
    rw [mem_riemannRochSpace_iff]
    exact fun v => Or.inr (bound₁ hqN R hR hRL hD hgood h₁' h₂' hc₁ hc₂ hG'D v)
  have hm₂ : (R.residue₂ ⟨G', h₂'⟩ : ↥(modularFunctionFieldC k N))
      ∈ riemannRochSpace (Finsupp.mapDomain P.reduceSnd (P.sndDiv D)) := by
    rw [mem_riemannRochSpace_iff]
    exact fun v => Or.inr (bound₂ hqN R hR hRL hD hgood h₁' h₂' hc₁ hc₂ hG'D v)

  have hsub₁ : (⟨G, h₁⟩ : R.R₁.integers) = ⟨G', h₁'⟩ - ⟨_, algebraMap_mem_integers₁ R c⟩ := by
    apply Subtype.ext
    show G = G' - algebraMap 𝕂 ↥(modularFunctionFieldBar (N * q)) (c : 𝕂)
    rw [hG', add_sub_cancel_right]
  have hsub₂ : (⟨G, h₂⟩ : R.R₂.integers) = ⟨G', h₂'⟩ - ⟨_, algebraMap_mem_integers₂ R c⟩ := by
    apply Subtype.ext
    show G = G' - algebraMap 𝕂 ↥(modularFunctionFieldBar (N * q)) (c : 𝕂)
    rw [hG', add_sub_cancel_right]
  have hcst₁ : R.residue₁ ⟨G, h₁⟩ = R.residue₁ ⟨G', h₁'⟩
      - algebraMap k ↥(modularFunctionFieldC k N) (R.redBar (IsLocalRing.residue A c)) := by
    rw [residue₁_apply, residue₁_apply, ← ι_algebraMap R, ← R.R₁.residue_algebraMap c, ← map_sub,
      ← map_sub, ← hsub₁]
  have hcst₂ : R.residue₂ ⟨G, h₂⟩ = R.residue₂ ⟨G', h₂'⟩
      - algebraMap k ↥(modularFunctionFieldC k N) (R.redBar (IsLocalRing.residue A c)) := by
    rw [residue₂_apply, residue₂_apply, ← ι_algebraMap R, ← R.R₂.residue_algebraMap c, ← map_sub,
      ← map_sub, ← hsub₂]
  have hmG₁ : (R.residue₁ ⟨G, h₁⟩ : ↥(modularFunctionFieldC k N))
      ∈ riemannRochSpace (Finsupp.mapDomain P.reduceFst (P.fstDiv D)) := by
    rw [hcst₁]; exact sub_mem hm₁ (algebraMap_mem_riemannRochSpace hD₁ _)
  have hmG₂ : (R.residue₂ ⟨G, h₂⟩ : ↥(modularFunctionFieldC k N))
      ∈ riemannRochSpace (Finsupp.mapDomain P.reduceSnd (P.sndDiv D)) := by
    rw [hcst₂]; exact sub_mem hm₂ (algebraMap_mem_riemannRochSpace hD₂ _)
  refine ⟨hmG₁, hmG₂, fun w hw => ?_⟩
  ·
    have hwss : w ∈ ssPlaces q N k := (hW w).mp hw
    have hwfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w :=
      frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed k N hqN data hKr w hwss
    have hs : smulNodePair (arithFrobC q k N) w ∈ nodePairsOfPlaces (arithFrobC q k N) W :=
      smulNodePair_mem_nodePairsOfPlaces _ hw
    have hnopole : ∀ V : Place 𝕂 ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = (smulNodePair (arithFrobC q k N) w).1 → 0 ≤ V.ord G := by
      intro V hV
      rw [smulNodePair_fst] at hV
      have h := hGD V
      rw [apply_eq_zero_of_reduceFst_fixed P hgood hwfix V hV] at h
      simpa using h
    obtain ⟨c', hc'⟩ := hRL.2 G h₁ h₂ _ hs hnopole
    rw [smulNodePair_fst, smulNodePair_snd] at hc'
    exact ⟨c', hc'⟩

end ModularCurve.RespairN

open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple in
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
    (G : ↥(modularFunctionFieldBar (N * q))) (hG : G ∈ riemannRochSpace D)
    (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers) :
    (R.residue₁ ⟨G, h₁⟩ : ↥(modularFunctionFieldC k N)) ∈ riemannRochSpace (Finsupp.mapDomain P.reduceFst (P.fstDiv D)) ∧
    (R.residue₂ ⟨G, h₂⟩ : ↥(modularFunctionFieldC k N)) ∈ riemannRochSpace (Finsupp.mapDomain P.reduceSnd (P.sndDiv D)) ∧
    ∀ w ∈ W, ∃ c : k, w.HasValue (R.residue₁ ⟨G, h₁⟩ : ↥(modularFunctionFieldC k N)) c ∧
      (arithFrobC q k N • w).HasValue (R.residue₂ ⟨G, h₂⟩ : ↥(modularFunctionFieldC k N)) c :=
  ModularCurve.RespairN.main hqN hW R hR hRL D (fun V => by simpa using (Finsupp.le_def.mp hD V)) hgood G hG h₁ h₂

#print axioms solution

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_residue_mem_riemannRochSpace_mapDomain_and_hasValue_of_isGoodDiv
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_residue_mem_riemannRochSpace_mapDomain_and_hasValue_of_isGoodDiv (solution)
