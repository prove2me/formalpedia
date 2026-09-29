-- Prove2me | solution 1 for ModularCurve.ord_jqModC_dvd_three_and_ord_sub_dvd_two_of_charP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/1c9c155b-da35-5f01-b039-c58da719fba6

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_PlaceWidth
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidth_of_ord_pos
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charP_pos
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_jqModC_dvd_three_and_ord_sub_dvd_two_of_charP
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois"

set_option autoImplicit false

open AlgebraicCurve ModularCurve

namespace RamC3

section Ord

variable {K : Type*} {FF : Type*} [Field K] [Field FF] [Algebra K FF] (w : Place K FF)

theorem mem_iff_le_one {f : FF} : f ∈ w.toValuationSubring ↔ w.adicValuation f ≤ 1 :=
  Place.mem_iff_adicValuation_le_one w

theorem ord_pos_iff {f : FF} (hf : f ≠ 0) : 0 < w.ord f ↔ w.adicValuation f < 1 := by
  rw [Place.ord, neg_pos, ← WithZero.log_one,
    WithZero.log_lt_log (w.adicValuation_ne_zero hf) one_ne_zero]

theorem evalAt_eq_of_ord_sub_algebraMap_pos {f : FF} (c : K) (hfc : f - algebraMap K FF c ≠ 0)
    (h : 0 < w.ord (f - algebraMap K FF c)) : w.evalAt f = c := by
  have hv : w.adicValuation (f - algebraMap K FF c) < 1 := (ord_pos_iff w hfc).1 h
  have hm : f - algebraMap K FF c ∈ w.toValuationSubring := (mem_iff_le_one w).2 hv.le
  have hc : algebraMap K FF c ∈ w.toValuationSubring := w.algebraMap_mem' c
  have hf : f ∈ w.toValuationSubring := by simpa using add_mem hm hc
  rw [w.evalAt_of_mem hf]

  have hunit : ¬ IsUnit (⟨f - algebraMap K FF c, hm⟩ : w.toValuationSubring) := by
    rw [← Place.adicValuation_coe_eq_one_iff]; exact hv.ne
  have hmax : (⟨f - algebraMap K FF c, hm⟩ : w.toValuationSubring) ∈
      IsLocalRing.maximalIdeal w.toValuationSubring := hunit
  have hres0 : IsLocalRing.residue w.toValuationSubring ⟨f - algebraMap K FF c, hm⟩ = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).2 hmax
  have hsplit : (⟨f, hf⟩ : w.toValuationSubring) =
      ⟨f - algebraMap K FF c, hm⟩ + algebraMap K w.toValuationSubring c := by
    apply Subtype.ext
    simp
  rw [hsplit, map_add, hres0, zero_add]
  exact w.residueInv_algebraMap c

theorem evalAt_eq_zero_of_ord_pos {f : FF} (hf : f ≠ 0) (h : 0 < w.ord f) : w.evalAt f = 0 := by
  apply evalAt_eq_of_ord_sub_algebraMap_pos w (0 : K) <;> simpa using ‹_›

end Ord

section Level

variable (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
  (K : Type) [Field K] [CharP K p] [IsAlgClosed K]

omit [Fact p.Prime] [IsAlgClosed K] in
include hp5 in
theorem h1728 : (1728 : K) ≠ 0 := by
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).1 (by exact_mod_cast h)
    have := Nat.le_of_dvd two_pos this
    omega
  have h3 : (3 : K) ≠ 0 := by
    intro h
    have : p ∣ 3 := (CharP.cast_eq_zero_iff K p 3).1 (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  rw [show (1728 : K) = 2 ^ 6 * 3 ^ 3 by norm_num]
  exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)

include hp5 hpN in

theorem onC (w : Place K ↥(modularFunctionFieldC K N)) :
    (0 < w.ord (jGeomGen K N) → w.ord (jGeomGen K N) ∣ 3) ∧
    (0 < w.ord (jGeomGen K N - algebraMap K _ 1728) → w.ord (jGeomGen K N - algebraMap K _ 1728) ∣ 2) := by
  classical
  have hj0 : jGeomGen K N ≠ 0 := by
    intro h
    have : (jqModC K) = 0 := by rw [← coe_jGeomGen K N, h]; rfl
    exact (transcendental_jqModC K) (this ▸ isAlgebraic_zero)
  have hjc : jGeomGen K N - algebraMap K ↥(modularFunctionFieldC K N) 1728 ≠ 0 := by
    intro h
    have h' : (jqModC K) = algebraMap K (LaurentSeries K) 1728 := by
      rw [sub_eq_zero] at h; rw [← coe_jGeomGen K N, h]; rfl
    exact (transcendental_jqModC K) (h' ▸ isAlgebraic_algebraMap (1728 : K))
  have key : ∀ (c : K) (hc : jGeomGen K N - algebraMap K _ c ≠ 0), 0 < w.ord (jGeomGen K N - algebraMap K _ c) →
      w.ord (jGeomGen K N - algebraMap K _ c) ∣ (jWidth c : ℤ) := by
    intro c hc h
    have hev : w.evalAt (jGeomGen K N) = c := evalAt_eq_of_ord_sub_algebraMap_pos w c hc h
    have hram : placeRamificationJ N w = (w.ord (jGeomGen K N - algebraMap K _ c)).toNat := by
      unfold placeRamificationJ; rw [hev]
    have hpos : 0 < placeRamificationJ N w := by
      rw [hram]; omega
    have hdvd := placeRamificationJ_dvd_jWidth_of_ord_pos (q := p) (N := N) (K := K) hp5 hpN hpos
    rw [hev, hram] at hdvd
    have hcast : (w.ord (jGeomGen K N - algebraMap K _ c) : ℤ) =
        ((w.ord (jGeomGen K N - algebraMap K _ c)).toNat : ℤ) := (Int.toNat_of_nonneg h.le).symm
    rw [hcast]
    exact Int.natCast_dvd_natCast.mpr hdvd
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := key 0 (by simpa using hj0) (by simpa using h)
    simpa [jWidth_of_eq_zero] using this
  · have := key 1728 hjc h
    rwa [jWidth_of_eq_1728 rfl (h1728 p hp5 K), Nat.cast_ofNat] at this

end Level

end RamC3

theorem RamC3.transport (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K]
    (E : IntermediateField K (LaurentSeries K)) (hE : modularFunctionFieldC K N = E) (hj : jqModC K ∈ E)
    (w : Place K ↥E) :
    (0 < w.ord (⟨jqModC K, hj⟩ : ↥E) → w.ord (⟨jqModC K, hj⟩ : ↥E) ∣ 3) ∧
    (0 < w.ord ((⟨jqModC K, hj⟩ : ↥E) - algebraMap K _ 1728) → w.ord ((⟨jqModC K, hj⟩ : ↥E) - algebraMap K _ 1728) ∣ 2) := by
  subst hE
  exact RamC3.onC p hp5 N hpN K w

theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] :
    ∀ w : Place K ↥(modularFunctionFieldFullC K N),
      (0 < w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) →
          w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) ∣ 3) ∧
      (0 < w.ord ((⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) - algebraMap K _ 1728) →
          w.ord ((⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) - algebraMap K _ 1728) ∣ 2) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  intro w
  exact RamC3.transport p hp5 N hpN K _ (modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charP_pos K p N hpN)
    (jqModC_mem_full K N) w

end S_ModularCurve_ord_jqModC_dvd_three_and_ord_sub_dvd_two_of_charP
end P2MW
export P2MW.S_ModularCurve_ord_jqModC_dvd_three_and_ord_sub_dvd_two_of_charP (solution)
