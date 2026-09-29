-- Prove2me | solution 1 for ModularCurve.exists_coe_eq_thetaL_jqModC_zpow_and_stackOrd_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/4442b14d-18fd-51c0-b267-b04ef318d08f

import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_thetaL_jqModC_pow_mul_prod_sq_eq
import Theorems.Thm_ModularCurve_zero_mem_ssJSet_iff
import Theorems.Thm_ModularCurve_ofNat1728_mem_ssJSet_iff
import Theorems.Thm_ModularCurve_card_eq_of_ssJSet
import Theorems.Thm_ModularCurve_ssJSet_finite
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidth_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidth_of_ord_pos
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_evalAt_congr
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_neg
import Theorems.Thm_AlgebraicCurve_Place_ord_add_eq_of_lt
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_coe_eq_thetaL_jqModC_zpow_and_stackOrd_eq
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero"
p2m_attr_erase "simp" "ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

open AlgebraicCurve ModularCurve

noncomputable section

namespace HasseDiv

def mOf (p : ℕ) : ℕ := p / 12

def e4Of (p : ℕ) : ℕ := if p % 3 = 2 then 1 else 0

def e6Of (p : ℕ) : ℕ := if p % 4 = 3 then 1 else 0

theorem e4Of_le (p : ℕ) : e4Of p ≤ 2 := by unfold e4Of; split_ifs <;> omega
theorem e6Of_le (p : ℕ) : e6Of p ≤ 1 := by unfold e6Of; split_ifs <;> omega

theorem not_two_dvd (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) : ¬ 2 ∣ p := fun h => by
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h; omega

theorem not_three_dvd (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) : ¬ 3 ∣ p := fun h => by
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h; omega

theorem twelve_mul_mOf (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    12 * mOf p + 4 * e4Of p + 6 * e6Of p = p - 1 := by
  have h2 := not_two_dvd p hp hp5
  have h3 := not_three_dvd p hp hp5
  unfold mOf e4Of e6Of
  split_ifs <;> omega

def aOf (p : ℕ) : ℕ := 4 * mOf p + e4Of p + 2 * e6Of p

def bOf (p : ℕ) : ℕ := 3 * mOf p + e4Of p + e6Of p

section Field

variable (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
  (N : ℕ) [NeZero N]

def S0 : Finset K := (ssJSet_finite p K).toFinset

theorem mem_S0 (a : K) : a ∈ S0 p K ↔ a ∈ ssJSet p K := Set.Finite.mem_toFinset _

def S1 : Finset K := S0 p K \ {0, 1728}

theorem mem_S1 (a : K) : a ∈ S1 p K ↔ a ∈ ssJSet p K ∧ a ≠ 0 ∧ a ≠ 1728 := by
  simp [S1, mem_S0]

def R : ↥(modularFunctionFieldC K N) :=
  jGeomGen K N ^ aOf p * (jGeomGen K N - 1728) ^ bOf p *
    (∏ a ∈ S1 p K, (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) a))⁻¹

def Pl : LaurentSeries K := ∏ a ∈ S1 p K, (jqModC K - HahnSeries.C a)

end Field

section Orders

variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]

theorem ord_finset_prod (x : Place K F) {ι : Type*} (s : Finset ι) (f : ι → F)
    (hf : ∀ i ∈ s, f i ≠ 0) : x.ord (∏ i ∈ s, f i) = ∑ i ∈ s, x.ord (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [x.ord_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      x.ord_mul (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.2 fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem ord_pow' (x : Place K F) (f : F) (n : ℕ) : x.ord (f ^ n) = n * x.ord f := by
  rw [← zpow_natCast, x.ord_zpow]

theorem ord_sub_algebraMap_eq_zero_of_evalAt_ne (x : Place K F) (hx : x.IsRational) {f : F}
    (hf : f ∈ x.toValuationSubring) {c : K} (hc : x.evalAt f ≠ c) (hne : f - algebraMap K F c ≠ 0) :
    x.ord (f - algebraMap K F c) = 0 := by
  have hmem : f - algebraMap K F c ∈ x.toValuationSubring := sub_mem hf (x.algebraMap_mem' c)
  have h0 : 0 ≤ x.ord (f - algebraMap K F c) := (x.mem_iff_ord_nonneg hne).1 hmem
  by_contra h
  have hpos : 0 < x.ord (f - algebraMap K F c) := lt_of_le_of_ne h0 (Ne.symm h)
  apply hc
  rw [x.evalAt_congr hf (x.algebraMap_mem' c) (Or.inr hpos), x.evalAt_algebraMap]

theorem ord_sub_algebraMap_of_ord_neg (x : Place K F) {f : F} (hf : x.ord f < 0) (c : K) :
    x.ord (f - algebraMap K F c) = x.ord f := by
  by_cases hc : c = 0
  · rw [hc, map_zero, sub_zero]
  have hf0 : f ≠ 0 := fun h => by rw [h, x.ord_zero] at hf; exact lt_irrefl _ hf
  rw [sub_eq_add_neg]
  refine x.ord_add_eq_of_lt hf0 (neg_ne_zero.2 ((map_ne_zero _).2 hc)) ?_
  rw [x.ord_neg, x.ord_algebraMap]; exact hf

end Orders

section OrdR

variable (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (N : ℕ) [NeZero N]

theorem jGeomGen_ne_zero : (jGeomGen K N : ↥(modularFunctionFieldC K N)) ≠ 0 := by
  simpa using jGeomGen_sub_algebraMap_ne_zero K N 0

theorem jGeomGen_sub_ofNat_ne_zero :
    (jGeomGen K N : ↥(modularFunctionFieldC K N)) - 1728 ≠ 0 := by
  have := jGeomGen_sub_algebraMap_ne_zero K N 1728
  rwa [map_ofNat] at this

theorem prod_sub_ne_zero (S : Finset K) :
    ∏ a ∈ S, (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) a) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun a _ => jGeomGen_sub_algebraMap_ne_zero K N a

variable [CharP K p] [IsAlgClosed K] [DecidableEq K]

theorem R_ne_zero : R p K N ≠ 0 := by
  unfold R
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (jGeomGen_ne_zero K N))
    (pow_ne_zero _ (jGeomGen_sub_ofNat_ne_zero K N))) (inv_ne_zero (prod_sub_ne_zero K N _))

theorem ord_R (x : Place K ↥(modularFunctionFieldC K N)) :
    x.ord (R p K N) = aOf p * x.ord (jGeomGen K N) + bOf p * x.ord (jGeomGen K N - 1728)
      - ∑ a ∈ S1 p K, x.ord (jGeomGen K N - algebraMap K ↥(modularFunctionFieldC K N) a) := by
  unfold R
  rw [x.ord_mul (mul_ne_zero (pow_ne_zero _ (jGeomGen_ne_zero K N))
      (pow_ne_zero _ (jGeomGen_sub_ofNat_ne_zero K N))) (inv_ne_zero (prod_sub_ne_zero K N _)),
    x.ord_mul (pow_ne_zero _ (jGeomGen_ne_zero K N)) (pow_ne_zero _ (jGeomGen_sub_ofNat_ne_zero K N)),
    ord_pow', ord_pow', x.ord_inv,
    ord_finset_prod _ _ _ (fun a _ => jGeomGen_sub_algebraMap_ne_zero K N a)]
  ring

end OrdR

section Coe

variable (p : ℕ) [hp : Fact p.Prime] (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
  (N : ℕ) [NeZero N]

omit hp [CharP K p] [IsAlgClosed K] [DecidableEq K] in
theorem C_eq_algebraMap' (a : K) : (HahnSeries.C a : LaurentSeries K) = algebraMap K (LaurentSeries K) a := by
  rw [HahnSeries.algebraMap_apply']
  simp

omit hp [CharP K p] [IsAlgClosed K] [DecidableEq K] in
theorem coe_algebraMap' (a : K) :
    ((algebraMap K ↥(modularFunctionFieldC K N) a : ↥(modularFunctionFieldC K N)) : LaurentSeries K)
      = HahnSeries.C a := by
  rw [C_eq_algebraMap']
  rfl

theorem coe_prod_sub (S : Finset K) :
    ((∏ a ∈ S, (jGeomGen K N - algebraMap K ↥(modularFunctionFieldC K N) a) :
        ↥(modularFunctionFieldC K N)) : LaurentSeries K) = ∏ a ∈ S, (jqModC K - HahnSeries.C a) := by
  rw [SubmonoidClass.coe_finsetProd]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [AddSubgroupClass.coe_sub, coe_jGeomGen, coe_algebraMap']

theorem coe_R : ((R p K N : ↥(modularFunctionFieldC K N)) : LaurentSeries K) =
    jqModC K ^ aOf p * (jqModC K - 1728) ^ bOf p * (Pl p K)⁻¹ := by
  unfold R Pl
  rw [IntermediateField.coe_mul, IntermediateField.coe_mul, IntermediateField.coe_pow,
    IntermediateField.coe_pow, IntermediateField.coe_inv, coe_prod_sub, AddSubgroupClass.coe_sub,
    coe_jGeomGen]
  norm_cast

theorem Pl_ne_zero : Pl p K ≠ 0 := by
  unfold Pl
  refine Finset.prod_ne_zero_iff.2 fun a _ h => ?_
  apply transcendental_jqModC K
  rw [sub_eq_zero.1 h, C_eq_algebraMap']
  exact isAlgebraic_algebraMap a

variable (hp5 : 5 ≤ p)
include hp5

theorem coe_R_sq : ((R p K N : ↥(modularFunctionFieldC K N)) : LaurentSeries K) ^ 2
    = thetaL K (jqModC K) ^ (p - 1) := by
  have key := thetaL_jqModC_pow_mul_prod_sq_eq p hp5 (mOf p) (e4Of p) (e6Of p)
    (twelve_mul_mOf p hp.out hp5) (e4Of_le p) (e6Of_le p) K (S0 p K) (mem_S0 p K)
  have hPl : (∏ a ∈ S0 p K \ {0, 1728}, (jqModC K - HahnSeries.C a)) = Pl p K := rfl
  rw [hPl] at key
  apply mul_right_cancel₀ (pow_ne_zero 2 (Pl_ne_zero p K))
  rw [key, coe_R, show 8 * mOf p + 2 * e4Of p + 4 * e6Of p = aOf p * 2 by unfold aOf; ring,
    show 6 * mOf p + 2 * e4Of p + 2 * e6Of p = bOf p * 2 by unfold bOf; ring, pow_mul, pow_mul]
  have hPl0 := Pl_ne_zero p K
  field_simp

theorem thetaPow_eq_or :
    thetaL K (jqModC K) ^ ((p - 1) / 2) = ((R p K N : ↥(modularFunctionFieldC K N)) : LaurentSeries K) ∨
    thetaL K (jqModC K) ^ ((p - 1) / 2) = -((R p K N : ↥(modularFunctionFieldC K N)) : LaurentSeries K) := by
  apply mul_self_eq_mul_self_iff.1
  rw [← pow_two, ← pow_two, coe_R_sq p K N hp5, ← pow_mul]
  congr 1
  have := not_two_dvd p hp.out hp5
  omega

omit hp5 in
open scoped Classical in

def sgn : K :=
  if thetaL K (jqModC K) ^ ((p - 1) / 2) = ((R p K N : ↥(modularFunctionFieldC K N)) : LaurentSeries K)
  then 1 else -1

omit hp5 in
theorem sgn_ne_zero : sgn p K N ≠ 0 := by
  classical
  unfold sgn; split_ifs
  · exact one_ne_zero
  · exact neg_ne_zero.2 one_ne_zero

omit hp5 in

def hasseFn : ↥(modularFunctionFieldC K N) := algebraMap K _ (sgn p K N) * (R p K N)⁻¹

omit hp5 in
theorem hasseFn_ne_zero : hasseFn p K N ≠ 0 :=
  mul_ne_zero ((map_ne_zero _).2 (sgn_ne_zero p K N)) (inv_ne_zero (R_ne_zero p K N))

theorem coe_hasseFn : ((hasseFn p K N : ↥(modularFunctionFieldC K N)) : LaurentSeries K)
    = thetaL K (jqModC K) ^ (-(((p : ℤ) - 1) / 2)) := by
  have hz : (-(((p : ℤ) - 1) / 2)) = -(((p - 1) / 2 : ℕ) : ℤ) := by
    have := hp.out.two_le; omega
  rw [hz, zpow_neg, zpow_natCast]
  unfold hasseFn
  rw [IntermediateField.coe_mul, IntermediateField.coe_inv, coe_algebraMap']
  by_cases hc : thetaL K (jqModC K) ^ ((p - 1) / 2)
      = ((R p K N : ↥(modularFunctionFieldC K N)) : LaurentSeries K)
  · have hs : sgn p K N = 1 := if_pos hc
    rw [hs, map_one, one_mul, hc]
  · have hs : sgn p K N = -1 := if_neg hc
    rw [hs, map_neg, map_one, (thetaPow_eq_or p K N hp5).resolve_left hc, inv_neg, neg_one_mul]

end Coe

section Places

variable (K : Type) [Field K] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]

theorem isRational (x : Place K ↥(modularFunctionFieldC K N)) : x.IsRational := by
  haveI := isCurveOver_modularFunctionFieldC_of_perfectField K N
  exact (Place.isRational_iff_deg_eq_one x).2 (IsCurveOver.deg_eq_one_of_isAlgClosed x)

variable {K N}

theorem natCast_placeRamificationJ {x : Place K ↥(modularFunctionFieldC K N)}
    (haff : IsAffineGeomPlace K N x) :
    (placeRamificationJ N x : ℤ) = x.ord (jGeomGen K N -
      algebraMap K ↥(modularFunctionFieldC K N) (x.evalAt (jGeomGen K N))) := by
  unfold placeRamificationJ
  exact Int.toNat_of_nonneg (ord_sub_evalAt_pos_of_isRational (isRational K N x) haff.1
    (jGeomGen_sub_algebraMap_ne_zero K N _)).le

theorem placeRamificationJ_pos {x : Place K ↥(modularFunctionFieldC K N)}
    (haff : IsAffineGeomPlace K N x) : 0 < placeRamificationJ N x := by
  have h := ord_sub_evalAt_pos_of_isRational (isRational K N x) haff.1
    (jGeomGen_sub_algebraMap_ne_zero K N (x.evalAt (jGeomGen K N)))
  have h2 := natCast_placeRamificationJ haff
  omega

theorem ord_jGeomGen_sub {x : Place K ↥(modularFunctionFieldC K N)} (haff : IsAffineGeomPlace K N x)
    (c : K) : x.ord (jGeomGen K N - algebraMap K ↥(modularFunctionFieldC K N) c)
      = if x.evalAt (jGeomGen K N) = c then (placeRamificationJ N x : ℤ) else 0 := by
  split_ifs with h
  · rw [natCast_placeRamificationJ haff, h]
  · exact ord_sub_algebraMap_eq_zero_of_evalAt_ne x (isRational K N x) haff.1 h
      (jGeomGen_sub_algebraMap_ne_zero K N c)

variable (p : ℕ) [hp : Fact p.Prime] [CharP K p]

variable (K) in
omit [IsAlgClosed K] [DecidableEq K] in

theorem ofNat1728_ne_zero (hp5 : 5 ≤ p) : (1728 : K) ≠ 0 := by
  intro h
  have hqp : p.Prime := hp.out
  have h' : ((1728 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff K p] at h'
  have h1728 : (1728 : ℕ) = 2 ^ 6 * 3 ^ 3 := by norm_num
  rw [h1728] at h'
  rcases (Nat.Prime.dvd_mul hqp).mp h' with h2 | h3
  · have := Nat.le_of_dvd (by norm_num) (hqp.dvd_of_dvd_pow h2); omega
  · have := Nat.le_of_dvd (by norm_num) (hqp.dvd_of_dvd_pow h3); omega

theorem ord_R_affine (hp5 : 5 ≤ p) {x : Place K ↥(modularFunctionFieldC K N)}
    (haff : IsAffineGeomPlace K N x) :
    x.ord (R p K N) = (placeRamificationJ N x : ℤ) *
      ((if x.evalAt (jGeomGen K N) = 0 then (aOf p : ℤ) else 0)
        + (if x.evalAt (jGeomGen K N) = 1728 then (bOf p : ℤ) else 0)
        - (if x.evalAt (jGeomGen K N) ∈ S1 p K then 1 else 0)) := by
  rw [ord_R]
  have h0 : x.ord (jGeomGen K N) = if x.evalAt (jGeomGen K N) = 0 then (placeRamificationJ N x : ℤ) else 0 := by
    rw [← ord_jGeomGen_sub haff 0, map_zero, sub_zero]
  have h1 : x.ord (jGeomGen K N - 1728)
      = if x.evalAt (jGeomGen K N) = 1728 then (placeRamificationJ N x : ℤ) else 0 := by
    rw [← ord_jGeomGen_sub haff 1728, map_ofNat]
  have h2 : ∑ a ∈ S1 p K, x.ord (jGeomGen K N - algebraMap K ↥(modularFunctionFieldC K N) a)
      = if x.evalAt (jGeomGen K N) ∈ S1 p K then (placeRamificationJ N x : ℤ) else 0 := by
    simp_rw [ord_jGeomGen_sub haff]
    rw [Finset.sum_ite_eq]
  rw [h0, h1, h2]
  split_ifs <;> ring

end Places

section StackOrd

variable (p : ℕ) [hp : Fact p.Prime] (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
  (N : ℕ) [NeZero N]

open scoped Classical in

theorem stackOrd_hasseFn_of_dvd (hp5 : 5 ≤ p) {x : Place K ↥(modularFunctionFieldC K N)}
    (haff : IsAffineGeomPlace K N x)
    (hdvd : placeRamificationJ N x ∣ jWidth (x.evalAt (jGeomGen K N))) :
    stackOrd N (((p : ℤ) - 1) / 2) (hasseFn p K N) x
      = if x.evalAt (jGeomGen K N) ∈ ssJSet p K then 1 else 0 := by

  set a₀ := x.evalAt (jGeomGen K N) with ha₀
  set e := placeRamificationJ N x with he
  have hepos : 0 < e := placeRamificationJ_pos haff
  have h12 := twelve_mul_mOf p hp.out hp5
  have hk : (((p : ℤ) - 1) / 2) = (6 * mOf p + 2 * e4Of p + 3 * e6Of p : ℕ) := by
    have := hp.out.two_le; omega

  have hordh : x.ord (hasseFn p K N) = -x.ord (R p K N) := by
    unfold hasseFn
    rw [x.ord_mul ((map_ne_zero _).2 (sgn_ne_zero p K N)) (inv_ne_zero (R_ne_zero p K N)),
      x.ord_algebraMap, x.ord_inv, zero_add]
  have hWn : placeWidth N x * e = jWidth a₀ := by
    unfold placeWidth
    rw [← ha₀, ← he]
    exact Nat.div_mul_cancel hdvd
  unfold stackOrd
  rw [hordh, ord_R_affine p hp5 haff, ← ha₀, ← he, hk]

  have h1728 : (1728 : K) ≠ 0 := ofNat1728_ne_zero K p hp5
  by_cases hz : a₀ = 0
  ·
    have hW3 : jWidth a₀ = 3 := jWidth_of_eq_zero hz
    have hS : a₀ ∉ S1 p K := by rw [mem_S1]; exact fun h => h.2.1 hz
    have h1 : a₀ ≠ 1728 := by rw [hz]; exact h1728.symm
    rw [hW3] at hWn
    rw [if_pos hz, if_neg h1, if_neg hS, hW3]
    have hss : (a₀ ∈ ssJSet p K) ↔ p % 3 = 2 := by rw [hz]; exact zero_mem_ssJSet_iff p hp5 K
    have hW' : (placeWidth N x : ℤ) * (e : ℤ) = 3 := by exact_mod_cast hWn
    by_cases hs : a₀ ∈ ssJSet p K
    · rw [if_pos hs]
      have h3 : e4Of p = 1 := by unfold e4Of; rw [if_pos (hss.1 hs)]
      unfold aOf
      rw [h3]
      push_cast
      linear_combination (-(4 * (mOf p : ℤ) + 1 + 2 * (e6Of p : ℤ))) * hW'
    · rw [if_neg hs]
      have h3 : e4Of p = 0 := by unfold e4Of; rw [if_neg (fun h => hs (hss.2 h))]
      unfold aOf
      rw [h3]
      push_cast
      linear_combination (-(4 * (mOf p : ℤ) + 0 + 2 * (e6Of p : ℤ))) * hW'
  by_cases hsv : a₀ = 1728
  ·
    have hW2 : jWidth a₀ = 2 := jWidth_of_eq_1728 hsv hz
    have hS : a₀ ∉ S1 p K := by rw [mem_S1]; exact fun h => h.2.2 hsv
    rw [hW2] at hWn
    rw [if_neg hz, if_pos hsv, if_neg hS, hW2]
    have hss : (a₀ ∈ ssJSet p K) ↔ p % 4 = 3 := by rw [hsv]; exact ofNat1728_mem_ssJSet_iff p hp5 K
    have hW' : (placeWidth N x : ℤ) * (e : ℤ) = 2 := by exact_mod_cast hWn
    by_cases hs : a₀ ∈ ssJSet p K
    · rw [if_pos hs]
      have h3 : e6Of p = 1 := by unfold e6Of; rw [if_pos (hss.1 hs)]
      unfold bOf
      rw [h3]
      push_cast
      linear_combination (-(3 * (mOf p : ℤ) + (e4Of p : ℤ) + 1)) * hW'
    · rw [if_neg hs]
      have h3 : e6Of p = 0 := by unfold e6Of; rw [if_neg (fun h => hs (hss.2 h))]
      unfold bOf
      rw [h3]
      push_cast
      linear_combination (-(3 * (mOf p : ℤ) + (e4Of p : ℤ) + 0)) * hW'
  ·
    have hW1 : jWidth a₀ = 1 := jWidth_of_ne hz hsv
    have hS : a₀ ∈ S1 p K ↔ a₀ ∈ ssJSet p K := by rw [mem_S1]; exact ⟨fun h => h.1, fun h => ⟨h, hz, hsv⟩⟩
    rw [hW1] at hWn
    rw [if_neg hz, if_neg hsv, hW1]
    have hW' : (placeWidth N x : ℤ) * (e : ℤ) = 1 := by exact_mod_cast hWn
    by_cases hs : a₀ ∈ ssJSet p K
    · rw [if_pos hs, if_pos (hS.2 hs)]
      push_cast
      linear_combination hW'
    · rw [if_neg hs, if_neg (fun h => hs (hS.1 h))]
      push_cast
      ring

end StackOrd

section Cusp

variable (p : ℕ) [hp : Fact p.Prime] (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
  (N : ℕ) [NeZero N]

theorem card_S1 (hp5 : 5 ≤ p) : (S1 p K).card = mOf p := by
  have hS := mem_S0 p K
  have hcard := card_eq_of_ssJSet p hp5 K (S0 p K) hS
  have h0 : (0 : K) ∈ S0 p K ↔ p % 3 = 2 := (hS 0).trans (zero_mem_ssJSet_iff p hp5 K)
  have h1728 : (1728 : K) ∈ S0 p K ↔ p % 4 = 3 := (hS 1728).trans (ofNat1728_mem_ssJSet_iff p hp5 K)
  have hne : (1728 : K) ≠ 0 := ofNat1728_ne_zero K p hp5
  have hnot : (0 : K) ∉ ({1728} : Finset K) := by
    rw [Finset.mem_singleton]; exact fun h => hne h.symm
  have key := Finset.card_sdiff_add_card_inter (S0 p K) {0, 1728}
  have hinter : (S0 p K ∩ {0, 1728}).card =
      (if p % 3 = 2 then 1 else 0) + (if p % 4 = 3 then 1 else 0) := by
    rw [Finset.inter_comm]
    by_cases a : (0 : K) ∈ S0 p K <;> by_cases b : (1728 : K) ∈ S0 p K
    · rw [Finset.insert_inter_of_mem a, Finset.singleton_inter_of_mem b,
        Finset.card_insert_of_notMem hnot, Finset.card_singleton, if_pos (h0.mp a), if_pos (h1728.mp b)]
    · rw [Finset.insert_inter_of_mem a, Finset.singleton_inter_of_notMem b,
        Finset.card_insert_of_notMem (Finset.notMem_empty _), Finset.card_empty, if_pos (h0.mp a),
        if_neg (mt h1728.mpr b)]
    · rw [Finset.insert_inter_of_notMem a, Finset.singleton_inter_of_mem b, Finset.card_singleton,
        if_neg (mt h0.mpr a), if_pos (h1728.mp b)]
    · rw [Finset.insert_inter_of_notMem a, Finset.singleton_inter_of_notMem b, Finset.card_empty,
        if_neg (mt h0.mpr a), if_neg (mt h1728.mpr b)]
  rw [hinter, hcard] at key
  unfold S1 mOf
  omega

theorem ord_R_cusp (hp5 : 5 ≤ p) {x : Place K ↥(modularFunctionFieldC K N)}
    (hx : x.ord (jGeomGen K N) < 0) :
    x.ord (R p K N) = (((p : ℤ) - 1) / 2) * x.ord (jGeomGen K N) := by
  rw [ord_R]
  have h1 : x.ord (jGeomGen K N - 1728) = x.ord (jGeomGen K N) := by
    rw [← map_ofNat (algebraMap K ↥(modularFunctionFieldC K N)) 1728]
    exact ord_sub_algebraMap_of_ord_neg x hx _
  have h2 : ∑ a ∈ S1 p K, x.ord (jGeomGen K N - algebraMap K ↥(modularFunctionFieldC K N) a)
      = (mOf p : ℤ) * x.ord (jGeomGen K N) := by
    rw [Finset.sum_congr rfl fun a _ => ord_sub_algebraMap_of_ord_neg x hx a, Finset.sum_const,
      card_S1 p K hp5, nsmul_eq_mul]
  rw [h1, h2]
  have hk : (((p : ℤ) - 1) / 2) = (6 * mOf p + 2 * e4Of p + 3 * e6Of p : ℕ) := by
    have := twelve_mul_mOf p hp.out hp5; have := hp.out.two_le; omega
  rw [hk]
  unfold aOf bOf
  push_cast
  ring

theorem ord_hasseFn_cusp (hp5 : 5 ≤ p) {x : Place K ↥(modularFunctionFieldC K N)}
    (hx : x.ord (jGeomGen K N) < 0) :
    x.ord (hasseFn p K N) = (((p : ℤ) - 1) / 2) * (-(x.ord (jGeomGen K N))) := by
  unfold hasseFn
  rw [x.ord_mul ((map_ne_zero _).2 (sgn_ne_zero p K N)) (inv_ne_zero (R_ne_zero p K N)),
    x.ord_algebraMap, x.ord_inv, zero_add, ord_R_cusp p K N hp5 hx]
  ring

end Cusp

section Main

theorem hasseDiv
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] :
    ∃ h : ↥(modularFunctionFieldC K N),
      (h : LaurentSeries K) = thetaL K (jqModC K) ^ (-(((p : ℤ) - 1) / 2)) ∧
      (∀ x : Place K (modularFunctionFieldC K N), IsAffineGeomPlace K N x →
          (x ∈ ssPlaces p N K → stackOrd N (((p : ℤ) - 1) / 2) h x = 1) ∧
          (x ∉ ssPlaces p N K → stackOrd N (((p : ℤ) - 1) / 2) h x = 0)) ∧
      (∀ x : Place K (modularFunctionFieldC K N), x.ord (jGeomGen K N) < 0 →
          x.ord h = (((p : ℤ) - 1) / 2) * (-(x.ord (jGeomGen K N)))) := by
  refine ⟨hasseFn p K N, coe_hasseFn p K N hp5, fun x haff => ⟨fun hss => ?_, fun hns => ?_⟩,
    fun x hx => ord_hasseFn_cusp p K N hp5 hx⟩
  ·
    rw [stackOrd_hasseFn_of_dvd p K N hp5 haff (placeRamificationJ_dvd_jWidth_of_mem_ssPlaces hp5 hpN hss),
      if_pos hss.2.2]
  ·
    have hrat := isRational K N x
    have hnss : x.evalAt (jGeomGen K N) ∉ ssJSet p K := fun h => hns ⟨hrat, haff, h⟩
    rw [stackOrd_hasseFn_of_dvd p K N hp5 haff
      (placeRamificationJ_dvd_jWidth_of_ord_pos hp5 hpN (placeRamificationJ_pos haff)), if_neg hnss]

end Main

end HasseDiv

end

open AlgebraicCurve ModularCurve in

theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] :
    ∃ h : ↥(modularFunctionFieldC K N),
      (h : LaurentSeries K) = thetaL K (jqModC K) ^ (-(((p : ℤ) - 1) / 2)) ∧
      (∀ x : Place K (modularFunctionFieldC K N), IsAffineGeomPlace K N x →
          (x ∈ ssPlaces p N K → stackOrd N (((p : ℤ) - 1) / 2) h x = 1) ∧
          (x ∉ ssPlaces p N K → stackOrd N (((p : ℤ) - 1) / 2) h x = 0)) ∧
      (∀ x : Place K (modularFunctionFieldC K N), x.ord (jGeomGen K N) < 0 →
          x.ord h = (((p : ℤ) - 1) / 2) * (-(x.ord (jGeomGen K N)))) :=
  HasseDiv.hasseDiv p hp5 N hpN K

end S_ModularCurve_exists_coe_eq_thetaL_jqModC_zpow_and_stackOrd_eq
end P2MW
export P2MW.S_ModularCurve_exists_coe_eq_thetaL_jqModC_zpow_and_stackOrd_eq (solution)
