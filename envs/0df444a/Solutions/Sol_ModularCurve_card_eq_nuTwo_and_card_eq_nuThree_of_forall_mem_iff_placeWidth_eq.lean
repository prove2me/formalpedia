-- Prove2me | solution 1 for ModularCurve.card_eq_nuTwo_and_card_eq_nuThree_of_forall_mem_iff_placeWidth_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/96f84077-e16a-561d-bf82-7b4b07780560

import Mathlib
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_ModuliPoint
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidth_of_ord_pos
import Theorems.Thm_ModularCurve_card_places_modularFunctionFieldFullC_over_eq_natCard_moduliPoint_j_eq
import Theorems.Thm_ModularCurve_two_mul_natCard_moduliPoint_j_eq_1728_eq_dedekindPsi_add_nuTwo_of_ne_zero
import Theorems.Thm_ModularCurve_three_mul_natCard_moduliPoint_j_eq_zero_eq_dedekindPsi_add_two_mul_nuThree_of_ne_zero
import Theorems.Thm_ModularCurve_sum_ord_jGeomGen_sub_eq_dedekindPsi
import Theorems.Thm_ModularCurve_finite_setOf_ord_jGeomGen_sub_pos
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_good
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_AlgebraicCurve_Place_evalAt_congr
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_card_eq_nuTwo_and_card_eq_nuThree_of_forall_mem_iff_placeWidth_eq
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one"
p2m_attr_erase "simp" "TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

open AlgebraicCurve ModularCurve

namespace I2B1Aux

variable {k : Type*} [Field k] (N : ℕ) [NeZero N]

theorem evalAt_jGeomGen_eq {a : k} {w : Place k (modularFunctionFieldC k N)}
    (h : 0 < w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) a)) :
    w.evalAt (jGeomGen k N) = a := by
  have hj : jGeomGen k N ∈ w.toValuationSubring := by
    have h' := add_mem (w.mem_of_ord_nonneg (jGeomGen_sub_algebraMap_ne_zero k N a) h.le)
      (w.algebraMap_mem' a)
    rwa [sub_add_cancel] at h'
  rw [w.evalAt_congr hj (w.algebraMap_mem' a) (Or.inr h), w.evalAt_algebraMap]

theorem placeRamificationJ_eq {a : k} {w : Place k (modularFunctionFieldC k N)}
    (h : 0 < w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) a)) :
    (placeRamificationJ N w : ℤ) = w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) a) := by
  unfold placeRamificationJ
  rw [evalAt_jGeomGen_eq N h]
  exact Int.toNat_of_nonneg h.le

theorem eq_one_and_eq_of_jWidth_div_eq [DecidableEq k] (c : k) (e m : ℕ) (hm : 2 ≤ m) (h : jWidth c / e = m) :
    e = 1 ∧ jWidth c = m := by
  have hle3 : jWidth c ≤ 3 := by rcases jWidth_eq_one_or c with h' | h' | h' <;> omega
  have he1 : e = 1 := by
    by_contra hne
    rcases Nat.eq_zero_or_pos e with h0 | hpos
    · rw [h0, Nat.div_zero] at h; omega
    · have h2 : 2 ≤ e := by omega
      have : jWidth c / e ≤ 1 :=
        calc jWidth c / e ≤ 3 / e := Nat.div_le_div_right hle3
          _ ≤ 3 / 2 := Nat.div_le_div_left h2 (by norm_num)
          _ = 1 := by norm_num
      omega
  subst he1
  rw [Nat.div_one] at h
  exact ⟨rfl, h⟩

theorem placeWidth_eq_two_iff [DecidableEq k] (h1728 : (1728 : k) ≠ 0) (w : Place k (modularFunctionFieldC k N)) :
    placeWidth N w = 2 ↔ w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) 1728) = 1 := by
  constructor
  · intro h
    obtain ⟨he, hj⟩ := eq_one_and_eq_of_jWidth_div_eq (w.evalAt (jGeomGen k N)) (placeRamificationJ N w) 2 le_rfl h
    have hc : w.evalAt (jGeomGen k N) = 1728 := by
      by_contra hne
      by_cases h0 : w.evalAt (jGeomGen k N) = 0
      · rw [jWidth_of_eq_zero h0] at hj; omega
      · rw [jWidth_of_ne h0 hne] at hj; omega
    unfold placeRamificationJ at he
    rw [hc] at he
    omega
  · intro h
    have hpos : 0 < w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) 1728) := by omega
    unfold placeWidth placeRamificationJ
    rw [evalAt_jGeomGen_eq N hpos, h, jWidth_of_eq_1728 rfl h1728]
    rfl

theorem placeWidth_eq_three_iff [DecidableEq k] (w : Place k (modularFunctionFieldC k N)) :
    placeWidth N w = 3 ↔ w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) 0) = 1 := by
  constructor
  · intro h
    obtain ⟨he, hj⟩ := eq_one_and_eq_of_jWidth_div_eq (w.evalAt (jGeomGen k N)) (placeRamificationJ N w) 3 (by norm_num) h
    have hc : w.evalAt (jGeomGen k N) = 0 := by
      by_contra h0
      by_cases h17 : w.evalAt (jGeomGen k N) = 1728
      · rw [jWidth_of_eq_1728 h17 h0] at hj; omega
      · rw [jWidth_of_ne h0 h17] at hj; omega
    unfold placeRamificationJ at he
    rw [hc] at he
    omega
  · intro h
    have hpos : 0 < w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) 0) := by omega
    unfold placeWidth placeRamificationJ
    rw [evalAt_jGeomGen_eq N hpos, h, jWidth_of_eq_zero rfl]
    rfl

theorem ord_toNat_dvd_jWidth [DecidableEq k] {q : ℕ} [Fact q.Prime] [CharP k q] [IsAlgClosed k]
    (hq5 : 5 ≤ q) (hqN : ¬ q ∣ N) {a : k} {w : Place k (modularFunctionFieldC k N)}
    (h : 0 < w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) a)) :
    (w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) a)).toNat ∣ jWidth a := by
  have hr : (placeRamificationJ N w : ℤ) = _ := placeRamificationJ_eq N h
  have hrN : placeRamificationJ N w = (w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) a)).toNat := by
    omega
  have hpos : 0 < placeRamificationJ N w := by omega
  have := ModularCurve.placeRamificationJ_dvd_jWidth_of_ord_pos (q := q) hq5 hqN hpos
  rwa [evalAt_jGeomGen_eq N h, hrN] at this

theorem card_eq_natCard_of_eq (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K]
    (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (F : IntermediateField K (LaurentSeries K)) (E : modularFunctionFieldFullC K N = F)
    (hmem : jqModC K ∈ F) (j₀ : K)
    (S : Finset (Place K F))
    (hS : ∀ P, P ∈ S ↔ 0 < P.ord ((⟨jqModC K, hmem⟩ : F) - algebraMap K F j₀)) :
    S.card = Nat.card {x : ModuliPoint N K // ModuliPoint.j x = j₀} := by
  subst E
  exact ModularCurve.card_places_modularFunctionFieldFullC_over_eq_natCard_moduliPoint_j_eq K N hN j₀ S hS

theorem card_eq_natCard (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K]
    (q N : ℕ) [Fact q.Prime] [CharP K q] [NeZero N] (hqN : ¬ q ∣ N) (j₀ : K)
    (S : Finset (Place K (modularFunctionFieldC K N)))
    (hS : ∀ P, P ∈ S ↔ 0 < P.ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) j₀)) :
    S.card = Nat.card {x : ModuliPoint N K // ModuliPoint.j x = j₀} := by
  have hN : (N : K) ≠ 0 := fun h => hqN ((CharP.cast_eq_zero_iff K q N).mp h)
  exact card_eq_natCard_of_eq K N hN (modularFunctionFieldC K N)
    (modularFunctionFieldC_eq_modularFunctionFieldFullC K q N hqN).symm (jqModC_mem K N) j₀ S hS

theorem cast_ne_zero_of_not_dvd (q : ℕ) [Fact q.Prime] [CharP k q] (m : ℕ) (hm : ¬ q ∣ m) : (m : k) ≠ 0 :=
  fun h => hm ((CharP.cast_eq_zero_iff k q m).mp h)

theorem constants_ne_zero (q : ℕ) [Fact q.Prime] [CharP k q] (hq5 : 5 ≤ q) :
    (2 : k) ≠ 0 ∧ (3 : k) ≠ 0 ∧ (1728 : k) ≠ 0 := by
  have hprime : q.Prime := Fact.out
  have hq2 : ¬ q ∣ 2 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have hq3 : ¬ q ∣ 3 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have h2k : (2 : k) ≠ 0 := by simpa using cast_ne_zero_of_not_dvd (k := k) q 2 hq2
  have h3k : (3 : k) ≠ 0 := by simpa using cast_ne_zero_of_not_dvd (k := k) q 3 hq3
  refine ⟨h2k, h3k, ?_⟩
  have h12 : ((1728 : ℕ) : k) ≠ 0 := by
    apply cast_ne_zero_of_not_dvd (k := k) q
    intro hdvd
    rcases (Nat.Prime.dvd_mul hprime).mp (by norm_num at hdvd ⊢; exact hdvd : q ∣ 2 ^ 6 * 3 ^ 3) with h | h
    · exact hq2 (hprime.dvd_of_dvd_pow h)
    · exact hq3 (hprime.dvd_of_dvd_pow h)
  simpa using h12

end I2B1Aux

open I2B1Aux in

theorem solution
    (q N : ℕ) [Fact q.Prime] [NeZero N] (hq5 : 5 ≤ q) (hqN : ¬ q ∣ N)
    (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (S₂ : Finset (Place k (modularFunctionFieldC k N))) (hS₂ : ∀ w, w ∈ S₂ ↔ placeWidth N w = 2)
    (S₃ : Finset (Place k (modularFunctionFieldC k N))) (hS₃ : ∀ w, w ∈ S₃ ↔ placeWidth N w = 3) :
    S₂.card = nuTwo N ∧ S₃.card = nuThree N := by
  have hprime : q.Prime := Fact.out
  obtain ⟨h2k, h3k, h1728⟩ := I2B1Aux.constants_ne_zero (k := k) q hq5
  have hNk : (N : k) ≠ 0 := I2B1Aux.cast_ne_zero_of_not_dvd (k := k) q N hqN
  have hsep := ModularCurve.isSeparable_jqNModC_of_good k N q hqN

  have fibre : ∀ a : k, ∃ T : Finset (Place k (modularFunctionFieldC k N)),
      (∀ w, w ∈ T ↔ 0 < w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) a)) := fun a =>
    ⟨(ModularCurve.finite_setOf_ord_jGeomGen_sub_pos k N hsep a).toFinset, fun w => by
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]⟩
  constructor
  ·
    obtain ⟨T, hT⟩ := fibre 1728
    have hsum := ModularCurve.sum_ord_jGeomGen_sub_eq_dedekindPsi q N hqN k hsep 1728 T hT
    have hcard : 2 * T.card = dedekindPsi N + nuTwo N := by
      rw [I2B1Aux.card_eq_natCard k q N hqN 1728 T hT]
      exact ModularCurve.two_mul_natCard_moduliPoint_j_eq_1728_eq_dedekindPsi_add_nuTwo_of_ne_zero N k hNk h2k h3k
    have hS : S₂ = T.filter (fun w => w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) 1728) = 1) := by
      ext w
      rw [hS₂, Finset.mem_filter, hT, I2B1Aux.placeWidth_eq_two_iff N h1728]
      constructor
      · intro h; exact ⟨by omega, h⟩
      · exact And.right
    have hval : ∀ w ∈ T, w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) 1728) =
        2 - (if w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) 1728) = 1 then 1 else 0 : ℤ) := by
      intro w hw
      have hpos := (hT w).mp hw
      have hd := I2B1Aux.ord_toNat_dvd_jWidth N hq5 hqN hpos
      rw [jWidth_of_eq_1728 rfl h1728] at hd
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h <;> split_ifs <;> omega
    rw [Finset.sum_congr rfl hval, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_boole, ← hS,
      nsmul_eq_mul] at hsum
    omega
  ·
    obtain ⟨T, hT⟩ := fibre 0
    have hsum := ModularCurve.sum_ord_jGeomGen_sub_eq_dedekindPsi q N hqN k hsep 0 T hT
    have hcard : 3 * T.card = dedekindPsi N + 2 * nuThree N := by
      rw [I2B1Aux.card_eq_natCard k q N hqN 0 T hT]
      exact ModularCurve.three_mul_natCard_moduliPoint_j_eq_zero_eq_dedekindPsi_add_two_mul_nuThree_of_ne_zero N k hNk h2k h3k
    have hS : S₃ = T.filter (fun w => w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) 0) = 1) := by
      ext w
      rw [hS₃, Finset.mem_filter, hT, I2B1Aux.placeWidth_eq_three_iff N]
      constructor
      · intro h; exact ⟨by omega, h⟩
      · exact And.right
    have hval : ∀ w ∈ T, w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) 0) =
        3 - 2 * (if w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) 0) = 1 then 1 else 0 : ℤ) := by
      intro w hw
      have hpos := (hT w).mp hw
      have hd := I2B1Aux.ord_toNat_dvd_jWidth N hq5 hqN hpos
      rw [jWidth_of_eq_zero rfl] at hd
      rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h <;> split_ifs <;> omega
    rw [Finset.sum_congr rfl hval, Finset.sum_sub_distrib, Finset.sum_const, ← Finset.mul_sum, Finset.sum_boole,
      ← hS, nsmul_eq_mul] at hsum
    omega

#print axioms solution

end S_ModularCurve_card_eq_nuTwo_and_card_eq_nuThree_of_forall_mem_iff_placeWidth_eq
end P2MW
export P2MW.S_ModularCurve_card_eq_nuTwo_and_card_eq_nuThree_of_forall_mem_iff_placeWidth_eq (solution)
