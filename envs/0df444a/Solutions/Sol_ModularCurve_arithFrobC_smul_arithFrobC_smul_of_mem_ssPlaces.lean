-- Prove2me | solution 1 for ModularCurve.arithFrobC_smul_arithFrobC_smul_of_mem_ssPlaces
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/05db2db9-594f-5434-ac6c-045071ca87f0

import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Theorems.Thm_ModularCurve_jqNModC_mul_pow_eq_pow
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_arithFrobC_smul_arithFrobC_smul_of_mem_ssPlaces_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_arithFrobC_smul_arithFrobC_smul_of_mem_ssPlaces
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two"
p2m_attr_erase "simp" "compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply"
p2m_attr_erase "simp" "WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply HahnSeries.ramScale_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve IntermediateField
open scoped Pointwise

namespace SsfrobCaseC

section FieldEquality

variable (K : Type) [Field K] (q : ℕ) [Fact q.Prime] [CharP K q] (M k : ℕ) [NeZero M]
  [NeZero (M * q ^ k)]

theorem modularFunctionFieldC_mul_pow_eq (hqM : ¬ q ∣ M) :
    ModularCurve.modularFunctionFieldC K (M * q ^ k) = ModularCurve.modularFunctionFieldC K M := by
  have hMK : (M : K) ≠ 0 := fun h => hqM ((CharP.cast_eq_zero_iff K q M).mp h)
  have hsep := ModularCurve.isSeparable_jqNModC_of_natCast_ne_zero K M hMK
  haveI : ExpChar K q := ExpChar.prime (Fact.out : q.Prime)
  have key := IntermediateField.adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable
    (F := ↥(IntermediateField.adjoin K ({ModularCurve.jqModC K} : Set (LaurentSeries K))))
    (E := LaurentSeries K) hsep q k
  have key' := congrArg (IntermediateField.restrictScalars K) key
  have e1 := IntermediateField.adjoin_simple_adjoin_simple K (ModularCurve.jqModC K)
    (ModularCurve.jqNModC K M)
  have e2 := IntermediateField.adjoin_simple_adjoin_simple K (ModularCurve.jqModC K)
    (ModularCurve.jqNModC K M ^ q ^ k)
  unfold ModularCurve.modularFunctionFieldC
  rw [ModularCurve.jqNModC_mul_pow_eq_pow K M k]
  exact e2.symm.trans (key'.symm.trans e1)

end FieldEquality

section Transport

variable {K F F' : Type} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (e : F ≃+* F') (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a)

theorem isRational_congrRingEquiv {v : Place K F} (hv : v.IsRational) :
    (Place.congrRingEquiv e he v).IsRational := by
  intro y
  obtain ⟨x, hx⟩ := (Place.congrResidueAlgEquiv e he v).surjective y
  obtain ⟨a, ha⟩ := hv x
  refine ⟨a, ?_⟩
  rw [← hx, ← ha, AlgEquiv.commutes]

theorem evalAt_congrRingEquiv {v : Place K F} (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) :
    (Place.congrRingEquiv e he v).evalAt (e f) = v.evalAt f := by
  have hw : (Place.congrRingEquiv e he v).IsRational := isRational_congrRingEquiv e he hv
  have hf' : e f ∈ (Place.congrRingEquiv e he v).toValuationSubring := by
    show e.symm (e f) ∈ v.toValuationSubring
    rw [e.symm_apply_apply]
    exact hf
  apply (algebraMap K (Place.congrRingEquiv e he v).ResidueField).injective
  rw [(Place.congrRingEquiv e he v).algebraMap_evalAt hw hf',
    ← (Place.congrResidueAlgEquiv e he v).commutes (v.evalAt f), v.algebraMap_evalAt hv hf]
  show _ = IsLocalRing.ResidueField.mapEquiv (Place.comapSymmRingEquiv e v.toValuationSubring)
    (IsLocalRing.residue _ ⟨f, hf⟩)
  rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  rfl

theorem mem_congrRingEquiv_iff (v : Place K F) (x : F') :
    x ∈ (Place.congrRingEquiv e he v).toValuationSubring ↔ e.symm x ∈ v.toValuationSubring :=
  Iff.rfl

open scoped Pointwise in

theorem congrRingEquiv_smul (g : SemilinearAut K F) (g' : SemilinearAut K F')
    (hgg' : ∀ x : F, g' • e x = e (g • x)) (v : Place K F) :
    Place.congrRingEquiv e he (g • v) = g' • Place.congrRingEquiv e he v := by
  ext x
  rw [mem_congrRingEquiv_iff, SemilinearAut.smul_toValuationSubring,
    SemilinearAut.smul_toValuationSubring, ValuationSubring.mem_smul_pointwise_iff_exists,
    ValuationSubring.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, hsx⟩
    refine ⟨e s, ?_, ?_⟩
    · rw [mem_congrRingEquiv_iff, e.symm_apply_apply]
      exact hs
    · rw [hgg', hsx, e.apply_symm_apply]
  · rintro ⟨s', hs', hs'x⟩
    refine ⟨e.symm s', (mem_congrRingEquiv_iff e he v s').mp hs', ?_⟩
    apply e.injective
    rw [← hgg', e.apply_symm_apply, e.apply_symm_apply, hs'x]

theorem congrRingEquiv_smul_smul (g : SemilinearAut K F) (g' : SemilinearAut K F')
    (hgg' : ∀ x : F, g' • e x = e (g • x)) (v : Place K F) :
    Place.congrRingEquiv e he (g • (g • v)) = g' • (g' • Place.congrRingEquiv e he v) := by
  rw [congrRingEquiv_smul e he g g' hgg', congrRingEquiv_smul e he g g' hgg']

end Transport

section LevelEquiv

variable (K : Type) [Field K]

theorem exists_ringEquiv_of_eq {E : Type} [Field E] [Algebra K E] {S T : IntermediateField K E} (h : S = T) :
    ∃ e : ↥S ≃+* ↥T, (∀ x : S, ((e x : T) : E) = x) ∧ ∀ a : K, e (algebraMap K S a) = algebraMap K T a := by
  subst h
  exact ⟨RingEquiv.refl _, fun _ => rfl, fun _ => rfl⟩

variable (q : ℕ) [Fact q.Prime] [CharP K q] [PerfectField K] {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂]

theorem arithFrobC_smul_ringEquiv
    (e : ↥(ModularCurve.modularFunctionFieldC K N₁) ≃+* ↥(ModularCurve.modularFunctionFieldC K N₂))
    (hecoe : ∀ x : ModularCurve.modularFunctionFieldC K N₁,
      ((e x : ModularCurve.modularFunctionFieldC K N₂) : LaurentSeries K) = x)
    (x : ModularCurve.modularFunctionFieldC K N₁) :
    ModularCurve.arithFrobC q K N₂ • e x = e (ModularCurve.arithFrobC q K N₁ • x) := by
  apply Subtype.ext
  rw [hecoe]
  unfold ModularCurve.arithFrobC
  rw [ModularCurve.coe_coeffSemilinearAut_smul, ModularCurve.coe_coeffSemilinearAut_smul, hecoe]

end LevelEquiv

section Wrapper

variable (q : ℕ) (K : Type) [Field K] [DecidableEq K] [Fact q.Prime] [CharP K q] [IsAlgClosed K]

theorem caseC (M k : ℕ) [NeZero M] [NeZero (M * q ^ k)] (hqM : ¬ q ∣ M)
    (hcop : ∀ w ∈ ModularCurve.ssPlaces q M K,
      ModularCurve.arithFrobC q K M • (ModularCurve.arithFrobC q K M • w) = w) :
    ∀ w ∈ ModularCurve.ssPlaces q (M * q ^ k) K,
      ModularCurve.arithFrobC q K (M * q ^ k) • (ModularCurve.arithFrobC q K (M * q ^ k) • w) = w := by
  obtain ⟨e, hecoe, he⟩ := exists_ringEquiv_of_eq K (modularFunctionFieldC_mul_pow_eq K q M k hqM)
  have hecoe' : ∀ y : ModularCurve.modularFunctionFieldC K M,
      ((e.symm y : ModularCurve.modularFunctionFieldC K (M * q ^ k)) : LaurentSeries K) = y := by
    intro y
    rw [← hecoe (e.symm y), e.apply_symm_apply]
  intro w hw
  rw [ModularCurve.mem_ssPlaces_iff] at hw
  unfold ModularCurve.IsSupersingularPlace ModularCurve.IsAffineGeomPlace at hw
  obtain ⟨hrat, ⟨hj, hjN⟩, hss⟩ := hw

  have h1 : e.symm (ModularCurve.jGeomGen K M) = ModularCurve.jGeomGen K (M * q ^ k) := by
    apply Subtype.ext
    rw [hecoe', ModularCurve.coe_jGeomGen, ModularCurve.coe_jGeomGen]
  have h2 : (e.symm (ModularCurve.jNGeomGen K M)) ^ (q ^ k) = ModularCurve.jNGeomGen K (M * q ^ k) := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, hecoe', ModularCurve.coe_jNGeomGen, ModularCurve.coe_jNGeomGen,
      ModularCurve.jqNModC_mul_pow_eq_pow K M k]
  have h3 : ModularCurve.jGeomGen K M = e (ModularCurve.jGeomGen K (M * q ^ k)) := by
    apply Subtype.ext
    rw [hecoe, ModularCurve.coe_jGeomGen, ModularCurve.coe_jGeomGen]
  have hW : Place.congrRingEquiv e he w ∈ ModularCurve.ssPlaces q M K := by
    refine (ModularCurve.mem_ssPlaces_iff _ _ _).mpr ?_
    unfold ModularCurve.IsSupersingularPlace ModularCurve.IsAffineGeomPlace
    refine ⟨isRational_congrRingEquiv e he hrat, ⟨?_, ?_⟩, ?_⟩
    · rw [mem_congrRingEquiv_iff, h1]
      exact hj
    · rw [mem_congrRingEquiv_iff]
      refine ValuationSubring.mem_of_pow_mem' _ (n := q ^ k)
        (pow_ne_zero k (Fact.out : q.Prime).ne_zero) ?_
      rw [h2]
      exact hjN
    · rw [h3]

      convert hss using 1
      exact evalAt_congrRingEquiv e he hrat hj
  have hfix := hcop _ hW

  have hequi2 := congrRingEquiv_smul_smul e he (ModularCurve.arithFrobC q K (M * q ^ k))
    (ModularCurve.arithFrobC q K M) (arithFrobC_smul_ringEquiv K q e hecoe) w
  have key : Place.congrEquiv e he
        (ModularCurve.arithFrobC q K (M * q ^ k) • (ModularCurve.arithFrobC q K (M * q ^ k) • w))
      = Place.congrEquiv e he w :=
    hequi2.trans hfix
  exact (Place.congrEquiv e he).injective key

theorem target_of_coprime
    (hcop : ∀ (M : ℕ) [NeZero M], ¬ q ∣ M → ∀ w ∈ ModularCurve.ssPlaces q M K,
      ModularCurve.arithFrobC q K M • (ModularCurve.arithFrobC q K M • w) = w)
    (N : ℕ) [NeZero N] :
    ∀ w ∈ ModularCurve.ssPlaces q N K,
      ModularCurve.arithFrobC q K N • (ModularCurve.arithFrobC q K N • w) = w := by
  obtain ⟨k, M, hM, hN⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (NeZero.ne N) q (Fact.out : q.Prime).ne_one
  rw [mul_comm] at hN
  subst hN
  haveI : NeZero M := ⟨left_ne_zero_of_mul (NeZero.ne (M * q ^ k))⟩
  exact caseC q K M k hM (hcop M hM)

end Wrapper

end SsfrobCaseC

theorem solution
    (q N : ℕ) [NeZero N] (K : Type) [Field K] [DecidableEq K] [Fact q.Prime] [CharP K q]
    [IsAlgClosed K] :
    ∀ w ∈ ModularCurve.ssPlaces q N K,
      ModularCurve.arithFrobC q K N • (ModularCurve.arithFrobC q K N • w) = w :=
  SsfrobCaseC.target_of_coprime q K
    (fun M _ hM => ModularCurve.arithFrobC_smul_arithFrobC_smul_of_mem_ssPlaces_of_not_dvd q M hM K) N

end S_ModularCurve_arithFrobC_smul_arithFrobC_smul_of_mem_ssPlaces
end P2MW
export P2MW.S_ModularCurve_arithFrobC_smul_arithFrobC_smul_of_mem_ssPlaces (solution)
