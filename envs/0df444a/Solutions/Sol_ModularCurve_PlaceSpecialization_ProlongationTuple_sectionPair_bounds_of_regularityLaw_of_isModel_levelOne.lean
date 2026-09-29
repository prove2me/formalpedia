-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.sectionPair_bounds_of_regularityLaw_of_isModel_levelOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/d3c2c9f2-802e-5516-95e9-74df1e97966d

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_divisorLawFst_oneSided_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_divisorLawSnd_oneSided_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_oneSided_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawZero_oneSided_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace
import Theorems.Thm_ModularCurve_arithFrobC_smul_arithFrobC_smul_eq_self_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_PlaceSpecialization_not_fixed_reduceFst_of_isStrictSnd
import Theorems.Thm_ModularCurve_isAffineGeomPlace_frobOnPlacesGeomLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_sectionPair_bounds_of_regularityLaw_of_isModel_levelOne
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X"
p2m_attr_erase "simp" "ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁"
p2m_attr_erase "simp" "ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply"
p2m_attr_erase "simp" "WeierstrassCurve.mapPoint_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
set_option autoImplicit false

open AlgebraicCurve ModularCurve

p2m_open "ModularCurve.PlaceSpecialization~LevelOneProlongationPair" in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    {R : P.ProlongationTuple} (hR : R.IsModel)
    {W : Finset (Place k ↥(modularFunctionFieldC k 1))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (hRL : R.RegularityLaw W)
    {d₁ d₂ : ℕ}
    (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j))
    (hinj₁ : Function.Injective fun i => P.reduceFst (Q₁ i))
    (hinj₂ : Function.Injective fun j => P.reduceSnd (Q₂ j))
    {T₁ T₂ : Finset (Place k ↥(modularFunctionFieldC k 1))}
    (hT₁ : ∀ v, v ∈ T₁ ↔ ∃ i, P.reduceFst (Q₁ i) = v)
    (hT₂ : ∀ v, v ∈ T₂ ↔ ∃ j, P.reduceSnd (Q₂ j) = v)
    (hT₁W : Disjoint T₁ W)
    (hT₁aff : ∀ v ∈ T₁, IsAffineGeomPlace k 1 v) (hT₂aff : ∀ v ∈ T₂, IsAffineGeomPlace k 1 v)
    (E D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hE : 0 ≤ E)
    (hD : P.IsGoodDiv D)
    (G : ↥(modularFunctionFieldBar (1 * q))) (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers)
    (hdiv : ∀ V, (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) - D) V
      = V.ord G)
    (hb₁ hb₂ : ↥(modularFunctionFieldC k 1)) (hb₁0 : hb₁ ≠ 0) (hb₂0 : hb₂ ≠ 0)
    (hdiv₁ : ∀ v, Finsupp.mapDomain P.reduceFst (P.fstDiv D) v = v.ord hb₁)
    (hdiv₂ : ∀ v, Finsupp.mapDomain P.reduceSnd (P.sndDiv D) v = v.ord hb₂)
    (hvals : ∀ w ∈ W, ∃ c : k, c ≠ 0 ∧ w.HasValue hb₁ c ∧ (arithFrobC q k 1 • w).HasValue hb₂ c) :
    (∀ v : Place k ↥(modularFunctionFieldC k 1), v ∉ T₁ → 0 ≤ v.ord (R.residue₁ ⟨G, h₁⟩ * hb₁)) ∧
    (∀ v ∈ T₁, -1 ≤ v.ord (R.residue₁ ⟨G, h₁⟩ * hb₁)) ∧
    (∀ v : Place k ↥(modularFunctionFieldC k 1), v ∉ T₂ → 0 ≤ v.ord (R.residue₂ ⟨G, h₂⟩ * hb₂)) ∧
    (∀ v ∈ T₂, -1 ≤ v.ord (R.residue₂ ⟨G, h₂⟩ * hb₂)) ∧
    (∀ w ∈ W, ∃ c : k, w.HasValue (R.residue₁ ⟨G, h₁⟩ * hb₁) c ∧
      (arithFrobC q k 1 • w).HasValue (R.residue₂ ⟨G, h₂⟩ * hb₂) c) := by
  classical
  have hqN : ¬ q ∣ 1 := fun h => (Fact.out : q.Prime).ne_one (Nat.dvd_one.mp h)

  set E₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) :=
    ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) with hE₁
  set E₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) :=
    ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) with hE₂
  have hE' : ∀ W, 0 ≤ E W := fun W => by simpa using Finsupp.le_def.mp hE W
  have hphiσ : ∀ w : Place k ↥(modularFunctionFieldC k 1), arithFrobC q k 1 • w = frobOnPlacesGeomLevel k 1 data hKr w :=
    fun w => ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k 1 data hKr w
  have hphiinj : Function.Injective (frobOnPlacesGeomLevel k 1 data hKr) := by
    intro a b h
    rw [← hphiσ, ← hphiσ] at h
    exact smul_left_cancel _ h
  have hWfix : ∀ w ∈ W, frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr w) = w := by
    intro w hw
    have h := ModularCurve.arithFrobC_smul_arithFrobC_smul_eq_self_of_mem_ssPlaces q 1 hqN k w
      ((hW w).mp hw)
    rwa [hphiσ, hphiσ] at h

  have hnf₁ : ∀ V, P.IsStrictFst V ∨ P.IsStrictSnd V → frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.reduceFst V)) ≠ P.reduceFst V := by
    rintro V (hV | hV)
    · exact hV.2
    · exact ModularCurve.PlaceSpecialization.not_fixed_reduceFst_of_isStrictSnd P V hV
  have hnf₂ : ∀ V, P.IsStrictFst V ∨ P.IsStrictSnd V → frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.reduceSnd V)) ≠ P.reduceSnd V := by
    rintro V (hV | hV)
    · intro hfix
      apply hV.2
      have h1 : frobOnPlacesGeomLevel k 1 data hKr (P.reduceFst V) = P.reduceSnd V := hV.1
      apply hphiinj
      rw [h1]
      exact hfix
    · exact hV.2
  have hexcl : ∀ V, P.IsStrictFst V → P.IsStrictSnd V → False := by
    intro V h1 h2
    apply h1.2
    have e1 : frobOnPlacesGeomLevel k 1 data hKr (P.reduceFst V) = P.reduceSnd V := h1.1
    have e2 : P.reduceFst V = frobOnPlacesGeomLevel k 1 data hKr (P.reduceSnd V) := h2.1
    conv_rhs => rw [e2]
    rw [e1]

  have hE₁apply : ∀ V, E₁ V = ∑ i, if Q₁ i = V then (1 : ℤ) else 0 := fun V => by
    rw [hE₁, Finsupp.finset_sum_apply]; simp only [Finsupp.single_apply]
  have hE₂apply : ∀ V, E₂ V = ∑ j, if Q₂ j = V then (1 : ℤ) else 0 := fun V => by
    rw [hE₂, Finsupp.finset_sum_apply]; simp only [Finsupp.single_apply]
  have hE₁zero : ∀ V, (∀ i, Q₁ i ≠ V) → E₁ V = 0 := fun V h => by
    rw [hE₁apply]; exact Finset.sum_eq_zero fun i _ => if_neg (h i)
  have hE₂zero : ∀ V, (∀ j, Q₂ j ≠ V) → E₂ V = 0 := fun V h => by
    rw [hE₂apply]; exact Finset.sum_eq_zero fun j _ => if_neg (h j)
  have hE₁strict : ∀ V, E₁ V ≠ 0 → P.IsStrictFst V := fun V hV => by
    by_contra h; exact hV (hE₁zero V fun i hi => h (hi ▸ hQ₁ i))
  have hE₂strict : ∀ V, E₂ V ≠ 0 → P.IsStrictSnd V := fun V hV => by
    by_contra h; exact hV (hE₂zero V fun j hj => h (hj ▸ hQ₂ j))
  have hE₀strict : ∀ V, (E₁ + E₂) V ≠ 0 → P.IsStrictFst V ∨ P.IsStrictSnd V := by
    intro V hV
    rw [Finsupp.add_apply] at hV
    by_cases h1 : E₁ V = 0
    · rw [h1, zero_add] at hV; exact Or.inr (hE₂strict V hV)
    · exact Or.inl (hE₁strict V h1)
  have hDstrict : ∀ V, D V ≠ 0 → P.IsStrictFst V ∨ P.IsStrictSnd V :=
    fun V hV => hD V (Finsupp.mem_support_iff.mpr hV)
  have hE₁T1 : E₁.filter P.IsStrictFst = E₁ := by
    rw [Finsupp.filter_eq_self_iff]; exact hE₁strict
  have hE₂T2 : E₂.filter P.IsStrictSnd = E₂ := by
    rw [Finsupp.filter_eq_self_iff]; exact hE₂strict
  have hE₂T1 : E₂.filter P.IsStrictFst = 0 := by
    rw [Finsupp.filter_eq_zero_iff]
    intro V hV; by_contra h; exact hexcl V hV (hE₂strict V h)
  have hE₁T2 : E₁.filter P.IsStrictSnd = 0 := by
    rw [Finsupp.filter_eq_zero_iff]
    intro V hV; by_contra h; exact hexcl V (hE₁strict V h) hV

  have hfix₁ : ∀ V, frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.reduceFst V)) = P.reduceFst V → (E₁ + E₂) V = 0 ∧ D V = 0 := by
    intro V hV
    exact ⟨by_contra fun h => hnf₁ V (hE₀strict V h) hV, by_contra fun h => hnf₁ V (hDstrict V h) hV⟩
  have hfix₂ : ∀ V, frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.reduceSnd V)) = P.reduceSnd V → (E₁ + E₂) V = 0 ∧ D V = 0 := by
    intro V hV
    exact ⟨by_contra fun h => hnf₂ V (hE₀strict V h) hV, by_contra fun h => hnf₂ V (hDstrict V h) hV⟩
  have hGreg₁ : ∀ V, frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.reduceFst V)) = P.reduceFst V → 0 ≤ V.ord G := by
    intro V hV
    rw [← hdiv V, Finsupp.sub_apply, Finsupp.sub_apply, (hfix₁ V hV).1, (hfix₁ V hV).2,
      sub_zero, sub_zero]
    exact hE' V

  have mapDomain_nonneg : ∀ (g : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) →
        Place k ↥(modularFunctionFieldC k 1))
      (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))), (∀ V, 0 ≤ X V) →
      ∀ v, 0 ≤ Finsupp.mapDomain g X v := by
    intro g X hX v
    rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
    exact Finset.sum_nonneg fun V _ => by
      simp only [Finsupp.single_apply]
      split_ifs
      · exact hX V
      · exact le_rfl
  have mapDomain_eq_zero : ∀ (g : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) →
        Place k ↥(modularFunctionFieldC k 1))
      (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
      (v : Place k ↥(modularFunctionFieldC k 1)),
      (∀ V, X V ≠ 0 → g V ≠ v) → Finsupp.mapDomain g X v = 0 := by
    intro g X v h
    rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
    exact Finset.sum_eq_zero fun V hV => by
      simp only [Finsupp.single_apply]
      exact if_neg (h V (Finsupp.mem_support_iff.mp hV))
  have hfilter_nonneg : ∀ (p : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → Prop)
      [DecidablePred p] (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))),
      0 ≤ (E.filter p) V := by
    intro p _ V
    rw [Finsupp.filter_apply]
    split_ifs
    · exact hE' V
    · exact le_rfl
  have filter_ne_zero : ∀ (p : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → Prop)
      [DecidablePred p] (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (V),
      (X.filter p) V ≠ 0 → X V ≠ 0 := by
    intro p _ X V h hX
    apply h
    rw [Finsupp.filter_apply, hX, ite_self]

  have hEbar₁ : ∀ v, Finsupp.mapDomain P.reduceFst E₁ v =
      ∑ i, if P.reduceFst (Q₁ i) = v then (1 : ℤ) else 0 := by
    intro v
    rw [hE₁, Finsupp.mapDomain_finset_sum, Finsupp.finset_sum_apply]
    simp only [Finsupp.mapDomain_single, Finsupp.single_apply]
  have hEbar₂ : ∀ v, Finsupp.mapDomain P.reduceSnd E₂ v =
      ∑ j, if P.reduceSnd (Q₂ j) = v then (1 : ℤ) else 0 := by
    intro v
    rw [hE₂, Finsupp.mapDomain_finset_sum, Finsupp.finset_sum_apply]
    simp only [Finsupp.mapDomain_single, Finsupp.single_apply]
  have hEbar₁_nn : ∀ v, 0 ≤ Finsupp.mapDomain P.reduceFst E₁ v := fun v => by
    rw [hEbar₁]; exact Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num
  have hEbar₂_nn : ∀ v, 0 ≤ Finsupp.mapDomain P.reduceSnd E₂ v := fun v => by
    rw [hEbar₂]; exact Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num
  have hEbar₁_off : ∀ v, v ∉ T₁ → Finsupp.mapDomain P.reduceFst E₁ v = 0 := fun v hv => by
    rw [hEbar₁]; exact Finset.sum_eq_zero fun i _ => if_neg fun h => hv ((hT₁ v).mpr ⟨i, h⟩)
  have hEbar₂_off : ∀ v, v ∉ T₂ → Finsupp.mapDomain P.reduceSnd E₂ v = 0 := fun v hv => by
    rw [hEbar₂]; exact Finset.sum_eq_zero fun j _ => if_neg fun h => hv ((hT₂ v).mpr ⟨j, h⟩)
  have hEbar₁_le : ∀ v, Finsupp.mapDomain P.reduceFst E₁ v ≤ 1 := by
    intro v
    rw [hEbar₁]
    by_cases hv : ∃ i, P.reduceFst (Q₁ i) = v
    · obtain ⟨i, hi⟩ := hv
      rw [Finset.sum_eq_single i (fun j _ hji => if_neg fun h => hji (hinj₁ (h.trans hi.symm)))
        (fun h => absurd (Finset.mem_univ i) h), if_pos hi]
    · push Not at hv
      rw [Finset.sum_eq_zero fun i _ => if_neg (hv i)]; norm_num
  have hEbar₂_le : ∀ v, Finsupp.mapDomain P.reduceSnd E₂ v ≤ 1 := by
    intro v
    rw [hEbar₂]
    by_cases hv : ∃ j, P.reduceSnd (Q₂ j) = v
    · obtain ⟨j, hj⟩ := hv
      rw [Finset.sum_eq_single j (fun i _ hij => if_neg fun h => hij (hinj₂ (h.trans hj.symm)))
        (fun h => absurd (Finset.mem_univ j) h), if_pos hj]
    · push Not at hv
      rw [Finset.sum_eq_zero fun j _ => if_neg (hv j)]; norm_num

  have hfst0 : ∀ v, frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v → Finsupp.mapDomain P.reduceFst (P.fstDiv D) v = 0 := by
    intro v hv
    apply mapDomain_eq_zero
    intro V hV hVv
    rw [ModularCurve.PlaceSpecialization.fstDiv, Finsupp.filter_apply] at hV
    split_ifs at hV with hT
    · exact hT.2 (by rw [hVv]; exact hv)
    · exact hV rfl
  have hsnd0 : ∀ v, frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v → Finsupp.mapDomain P.reduceSnd (P.sndDiv D) v = 0 := by
    intro v hv
    apply mapDomain_eq_zero
    intro V hV hVv
    rw [ModularCurve.PlaceSpecialization.sndDiv, Finsupp.filter_apply] at hV
    split_ifs at hV with hT
    · exact hT.2 (by rw [hVv]; exact hv)
    · exact hV rfl

  have hf₁ : R.residue₁ ⟨G, h₁⟩ ≠ 0 → R.R₁.residue ⟨G, h₁⟩ ≠ 0 := fun hr h =>
    hr (by rw [ProlongationTuple.residue₁_apply, h, map_zero])
  have hf₂ : R.residue₂ ⟨G, h₂⟩ ≠ 0 → R.R₂.residue ⟨G, h₂⟩ ≠ 0 := fun hr h =>
    hr (by rw [ProlongationTuple.residue₂_apply, h, map_zero])

  have hdiv' : ∀ V, (E - (E₁ + E₂) - D) V = V.ord G := hdiv

  have key₁ : R.residue₁ ⟨G, h₁⟩ ≠ 0 → ∀ v : Place k ↥(modularFunctionFieldC k 1),
      -Finsupp.mapDomain P.reduceFst E₁ v ≤ v.ord (R.residue₁ ⟨G, h₁⟩ * hb₁) := by
    intro hr v
    rw [v.ord_mul hr hb₁0, ← hdiv₁ v]
    by_cases hv : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v
    ·
      rw [hfst0 v hv, add_zero]
      refine le_trans (neg_nonpos.mpr (hEbar₁_nn v)) ?_
      by_cases haff : IsAffineGeomPlace k 1 v
      ·
        exact (hRL.1 G h₁ h₂ v hv haff (fun V hV => hGreg₁ V (by rw [hV]; exact hv))).1 hr
      ·
        obtain ⟨⟨C, hC, hCv⟩, -⟩ :=
          ModularCurve.PlaceSpecialization.exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace
            hqN P v haff
        have hlaw := ModularCurve.PlaceSpecialization.ProlongationTuple.cuspLawInfty_oneSided_levelOne P R hR
          G h₁ (hf₁ hr) (E - (E₁ + E₂) - D) hdiv' C hC
        rw [hCv] at hlaw
        rw [← hlaw, Finsupp.filter_sub, Finsupp.filter_sub, Finsupp.mapDomain_sub,
          Finsupp.mapDomain_sub, Finsupp.sub_apply, Finsupp.sub_apply,
          mapDomain_eq_zero P.reduceFst ((E₁ + E₂).filter _) v
            (fun V hV hVv => hnf₁ V (hE₀strict V (filter_ne_zero _ _ V hV)) (by rw [hVv]; exact hv)),
          mapDomain_eq_zero P.reduceFst (D.filter _) v
            (fun V hV hVv => hnf₁ V (hDstrict V (filter_ne_zero _ _ V hV)) (by rw [hVv]; exact hv)),
          sub_zero, sub_zero]
        exact mapDomain_nonneg _ _ (hfilter_nonneg _) _
    ·
      have hlaw := ModularCurve.PlaceSpecialization.ProlongationTuple.divisorLawFst_oneSided_levelOne P R hR
        G h₁ (hf₁ hr) (E - (E₁ + E₂) - D) hdiv' v hv
      rw [← hlaw, ModularCurve.PlaceSpecialization.fstDiv, ← Finsupp.add_apply,
        ← Finsupp.mapDomain_add, ← Finsupp.filter_add, sub_add_cancel, Finsupp.filter_sub,
        Finsupp.filter_add, hE₁T1, hE₂T1, add_zero, Finsupp.mapDomain_sub, Finsupp.sub_apply]
      linarith [mapDomain_nonneg P.reduceFst (E.filter P.IsStrictFst) (hfilter_nonneg _) v]

  have key₂ : R.residue₂ ⟨G, h₂⟩ ≠ 0 → ∀ v : Place k ↥(modularFunctionFieldC k 1),
      -Finsupp.mapDomain P.reduceSnd E₂ v ≤ v.ord (R.residue₂ ⟨G, h₂⟩ * hb₂) := by
    intro hr v
    rw [v.ord_mul hr hb₂0, ← hdiv₂ v]
    by_cases hv : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v
    · rw [hsnd0 v hv, add_zero]
      refine le_trans (neg_nonpos.mpr (hEbar₂_nn v)) ?_
      by_cases haff : IsAffineGeomPlace k 1 v
      ·
        have hu : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v)) = frobOnPlacesGeomLevel k 1 data hKr v := by rw [hv]
        have huaff : IsAffineGeomPlace k 1 (frobOnPlacesGeomLevel k 1 data hKr v) :=
          ModularCurve.isAffineGeomPlace_frobOnPlacesGeomLevel k 1 data hKr v haff
        have h := (hRL.1 G h₁ h₂ (frobOnPlacesGeomLevel k 1 data hKr v) hu huaff (fun V hV => hGreg₁ V (by rw [hV]; exact hu))).2 hr
        rwa [hv] at h
      ·
        obtain ⟨-, ⟨C, hC, hCv⟩⟩ :=
          ModularCurve.PlaceSpecialization.exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace
            hqN P v haff
        have hlaw := ModularCurve.PlaceSpecialization.ProlongationTuple.cuspLawZero_oneSided_levelOne P R hR
          G h₂ (hf₂ hr) (E - (E₁ + E₂) - D) hdiv' C hC
        rw [hCv] at hlaw
        rw [← hlaw, Finsupp.filter_sub, Finsupp.filter_sub, Finsupp.mapDomain_sub,
          Finsupp.mapDomain_sub, Finsupp.sub_apply, Finsupp.sub_apply,
          mapDomain_eq_zero P.reduceSnd ((E₁ + E₂).filter _) v
            (fun V hV hVv => hnf₂ V (hE₀strict V (filter_ne_zero _ _ V hV)) (by rw [hVv]; exact hv)),
          mapDomain_eq_zero P.reduceSnd (D.filter _) v
            (fun V hV hVv => hnf₂ V (hDstrict V (filter_ne_zero _ _ V hV)) (by rw [hVv]; exact hv)),
          sub_zero, sub_zero]
        exact mapDomain_nonneg _ _ (hfilter_nonneg _) _
    · have hlaw := ModularCurve.PlaceSpecialization.ProlongationTuple.divisorLawSnd_oneSided_levelOne P R hR
        G h₂ (hf₂ hr) (E - (E₁ + E₂) - D) hdiv' v hv
      rw [← hlaw, ModularCurve.PlaceSpecialization.sndDiv, ← Finsupp.add_apply,
        ← Finsupp.mapDomain_add, ← Finsupp.filter_add, sub_add_cancel, Finsupp.filter_sub,
        Finsupp.filter_add, hE₁T2, hE₂T2, zero_add, Finsupp.mapDomain_sub, Finsupp.sub_apply]
      linarith [mapDomain_nonneg P.reduceSnd (E.filter P.IsStrictSnd) (hfilter_nonneg _) v]

  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    by_cases hr : R.residue₁ ⟨G, h₁⟩ = 0
    · simp only [hr, zero_mul, Place.ord_zero, le_refl]
    · have h := key₁ hr v
      rw [hEbar₁_off v hv, neg_zero] at h
      exact h
  · intro v hv
    by_cases hr : R.residue₁ ⟨G, h₁⟩ = 0
    · simp only [hr, zero_mul, Place.ord_zero]; norm_num
    · exact le_trans (by linarith [hEbar₁_le v]) (key₁ hr v)
  · intro v hv
    by_cases hr : R.residue₂ ⟨G, h₂⟩ = 0
    · simp only [hr, zero_mul, Place.ord_zero, le_refl]
    · have h := key₂ hr v
      rw [hEbar₂_off v hv, neg_zero] at h
      exact h
  · intro v hv
    by_cases hr : R.residue₂ ⟨G, h₂⟩ = 0
    · simp only [hr, zero_mul, Place.ord_zero]; norm_num
    · exact le_trans (by linarith [hEbar₂_le v]) (key₂ hr v)
  ·
    intro w hw
    have hs : smulNodePair (arithFrobC q k 1) w ∈ nodePairsOfPlaces (arithFrobC q k 1) W :=
      smulNodePair_mem_nodePairsOfPlaces (arithFrobC q k 1) hw
    obtain ⟨c, hc₁, hc₂⟩ := hRL.2 G h₁ h₂ _ hs
      (fun V hV => hGreg₁ V (by
        rw [smulNodePair_fst] at hV
        rw [hV]; exact hWfix w hw))
    rw [smulNodePair_fst] at hc₁
    rw [smulNodePair_snd] at hc₂
    obtain ⟨c', -, hw₁, hw₂⟩ := hvals w hw
    exact ⟨c * c', hc₁.mul hw₁, hc₂.mul hw₂⟩

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_sectionPair_bounds_of_regularityLaw_of_isModel_levelOne
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_sectionPair_bounds_of_regularityLaw_of_isModel_levelOne (solution)
