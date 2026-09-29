-- Prove2me | solution 1 for ModularCurve.mem_riemannRochSpace_of_isModPFormFn_of_charP_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/7676a6a0-6f91-57b2-8720-4224d3420776

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_ord_jGeomGen_eq_three_or_eq_six_of_exists_prime_dvd_mod_three_eq_two_of_isAlgClosed
import Theorems.Thm_ModularCurve_jGeomGen_eq_mk_jqModC
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mem_riemannRochSpace_of_isModPFormFn_of_charP_three
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois"
p2m_attr_erase "simp" "ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply"

set_option autoImplicit false

open AlgebraicCurve ModularCurve

namespace Ws12Member3

section Ord

variable {K : Type*} {FF : Type*} [Field K] [Field FF] [Algebra K FF] (w : Place K FF)

theorem mem_iff_le_one {f : FF} : f ∈ w.toValuationSubring ↔ w.adicValuation f ≤ 1 :=
  Place.mem_iff_adicValuation_le_one w

theorem ord_nonneg_iff {f : FF} (hf : f ≠ 0) : 0 ≤ w.ord f ↔ w.adicValuation f ≤ 1 := by
  rw [Place.ord, neg_nonneg, WithZero.log_le_iff_le_exp (w.adicValuation_ne_zero hf), WithZero.exp_zero]

theorem ord_pos_iff {f : FF} (hf : f ≠ 0) : 0 < w.ord f ↔ w.adicValuation f < 1 := by
  rw [Place.ord, neg_pos, ← WithZero.log_one,
    WithZero.log_lt_log (w.adicValuation_ne_zero hf) one_ne_zero]

theorem ord_neg_iff {f : FF} (hf : f ≠ 0) : w.ord f < 0 ↔ 1 < w.adicValuation f := by
  rw [Place.ord, neg_lt_zero, ← WithZero.log_one,
    WithZero.log_lt_log one_ne_zero (w.adicValuation_ne_zero hf)]

theorem ord_nonneg_of_mem {f : FF} (h : f ∈ w.toValuationSubring) : 0 ≤ w.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [Place.ord_zero]
  · exact (ord_nonneg_iff w hf).2 ((mem_iff_le_one w).1 h)

theorem mem_of_ord_nonneg {f : FF} (h : 0 ≤ w.ord f) : f ∈ w.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact zero_mem _
  · exact (mem_iff_le_one w).2 ((ord_nonneg_iff w hf).1 h)

theorem ord_pow (f : FF) (n : ℕ) : w.ord (f ^ n) = n * w.ord f := by
  rw [← zpow_natCast, Place.ord_zpow]

theorem adicValuation_algebraMap {c : K} (hc : c ≠ 0) : w.adicValuation (algebraMap K FF c) = 1 := by
  apply le_antisymm (w.adicValuation_algebraMap_le_one c)
  have h1 : w.adicValuation (algebraMap K FF c) * w.adicValuation (algebraMap K FF c⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hc, map_one, map_one]
  have h2 := w.adicValuation_algebraMap_le_one c⁻¹
  by_contra h
  rw [not_le] at h
  have : w.adicValuation (algebraMap K FF c) * w.adicValuation (algebraMap K FF c⁻¹) < 1 * 1 :=
    mul_lt_mul_of_lt_of_le_of_nonneg_of_pos h h2 zero_le' zero_lt_one
  rw [h1, one_mul] at this
  exact lt_irrefl _ this

theorem ord_algebraMap {c : K} (hc : c ≠ 0) : w.ord (algebraMap K FF c) = 0 := by
  rw [Place.ord, adicValuation_algebraMap w hc, WithZero.log_one, neg_zero]

theorem ord_sub_algebraMap_eq_zero_of_ord_pos {t : FF} (ht : t ≠ 0) {c : K} (hc : c ≠ 0) (h : 0 < w.ord t) :
    w.ord (t - algebraMap K FF c) = 0 := by
  have hv : w.adicValuation t < w.adicValuation (algebraMap K FF c) := by
    rw [adicValuation_algebraMap w hc]; exact (ord_pos_iff w ht).1 h
  rw [Place.ord, Valuation.map_sub_swap, Valuation.map_sub_eq_of_lt_left _ hv, adicValuation_algebraMap w hc,
    WithZero.log_one, neg_zero]

theorem ord_sub_algebraMap_eq_of_ord_neg {t : FF} (ht : t ≠ 0) (c : K) (h : w.ord t < 0) :
    w.ord (t - algebraMap K FF c) = w.ord t := by
  have hv : w.adicValuation (algebraMap K FF c) < w.adicValuation t :=
    lt_of_le_of_lt (w.adicValuation_algebraMap_le_one c) ((ord_neg_iff w ht).1 h)
  rw [Place.ord, Place.ord, Valuation.map_sub_eq_of_lt_left _ hv]

theorem ord_eq_zero_of_ord_sub_algebraMap_pos {t : FF} {c : K} (hc : c ≠ 0) (htc : t - algebraMap K FF c ≠ 0)
    (h : 0 < w.ord (t - algebraMap K FF c)) : w.ord t = 0 := by
  have hv : w.adicValuation (t - algebraMap K FF c) < w.adicValuation (algebraMap K FF c) := by
    rw [adicValuation_algebraMap w hc]; exact (ord_pos_iff w htc).1 h
  have : t = (t - algebraMap K FF c) + algebraMap K FF c := by ring
  rw [Place.ord, this, Valuation.map_add_eq_of_lt_right _ hv, adicValuation_algebraMap w hc, WithZero.log_one, neg_zero]

end Ord

theorem mem_of_isIntegral_adjoin {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L] {E : IntermediateField K L}
    (w : Place K ↥E) {t : ↥E} (ht : t ∈ w.toValuationSubring) (y : ↥E)
    (hy : IsIntegral (Algebra.adjoin K ({(t : L)} : Set L)) (y : L)) :
    y ∈ w.toValuationSubring := by
  classical
  set A := Algebra.adjoin K ({(t : L)} : Set L) with hA
  obtain ⟨P, hPm, hP0⟩ := hy

  have hcoef : ∀ i, ∃ c : Polynomial K, Polynomial.aeval (t : L) c = (P.coeff i : L) := by
    intro i
    have hm : (P.coeff i : L) ∈ (Polynomial.aeval (R := K) (t : L)).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact (P.coeff i).2
    exact (AlgHom.mem_range _).1 hm
  choose c hc using hcoef

  let O : Subalgebra K ↥E :=
    { carrier := w.toValuationSubring
      mul_mem' := fun ha hb => w.toValuationSubring.mul_mem _ _ ha hb
      add_mem' := fun ha hb => w.toValuationSubring.add_mem _ _ ha hb
      algebraMap_mem' := fun a => w.algebraMap_mem' a }
  have hbO : ∀ i, Polynomial.aeval t (c i) ∈ w.toValuationSubring := fun i => by
    have h1 : Polynomial.aeval t (c i) = O.val (Polynomial.aeval (⟨t, ht⟩ : O) (c i)) :=
      Polynomial.aeval_algHom_apply O.val (⟨t, ht⟩ : O) (c i)
    rw [h1]
    exact (Polynomial.aeval (⟨t, ht⟩ : O) (c i)).2

  set n := P.natDegree with hn
  have hrelLS : (y : L) ^ n +
      ∑ i ∈ Finset.range n, (P.coeff i : L) * (y : L) ^ i = 0 := by
    have h := hP0
    rw [hPm.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum] at h
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at h
    exact h
  have hrel : y ^ n + ∑ i ∈ Finset.range n, Polynomial.aeval t (c i) * y ^ i = 0 := by
    apply Subtype.val_injective
    push_cast
    rw [← hrelLS]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hc i]
    congr 1
    exact (Polynomial.aeval_algHom_apply E.val t (c i)).symm

  let Q : Polynomial ↥(w.toValuationSubring) :=
    Polynomial.X ^ n + ∑ i ∈ Finset.range n,
      Polynomial.C (⟨Polynomial.aeval t (c i), hbO i⟩ : ↥(w.toValuationSubring)) * Polynomial.X ^ i
  have hQm : Q.Monic := by
    apply Polynomial.monic_X_pow_add
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).2 fun i hi => ?_
    refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le i _) ?_
    exact WithBot.coe_lt_coe.2 (Finset.mem_range.1 hi)
  have hQ0 : Polynomial.eval₂ (algebraMap ↥(w.toValuationSubring) ↥E) y Q = 0 := by
    simp only [Q, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul,
      Polynomial.eval₂_C]
    exact hrel
  have hint : IsIntegral ↥(w.toValuationSubring) y := ⟨Q, hQm, hQ0⟩
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥(w.toValuationSubring)) (K := ↥E)).1 hint
  rw [← hz]
  exact z.2

end Ws12Member3

theorem Ws12Member3.ord_jq_eq_three_or_six (N : ℕ) [NeZero N] (hpN : ¬ 3 ∣ N)
    (hε : ∃ q : ℕ, q.Prime ∧ q ∣ N ∧ q % 3 = 2) (K : Type) [Field K] [CharP K 3] [IsAlgClosed K]
    (w : Place K ↥(modularFunctionFieldFullC K N))
    (hw : 0 < w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N))) :
    w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) = 3 ∨ w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) = 6 := by
  have key : ∀ (E : IntermediateField K (LaurentSeries K)) (hE : modularFunctionFieldC K N = E)
      (hmem : jqModC K ∈ E) (x : Place K ↥E), 0 < x.ord (⟨jqModC K, hmem⟩ : ↥E) →
      x.ord (⟨jqModC K, hmem⟩ : ↥E) = 3 ∨ x.ord (⟨jqModC K, hmem⟩ : ↥E) = 6 := by
    intro E hE hmem x hx
    subst hE
    have hj : (⟨jqModC K, hmem⟩ : ↥(modularFunctionFieldC K N)) = jGeomGen K N := (jGeomGen_eq_mk_jqModC K N).symm
    rw [hj] at hx ⊢
    exact ord_jGeomGen_eq_three_or_eq_six_of_exists_prime_dvd_mod_three_eq_two_of_isAlgClosed N hpN hε K x hx
  exact key _ (modularFunctionFieldC_eq_modularFunctionFieldFullC K 3 N hpN) (jqModC_mem_full K N) w hw

set_option maxHeartbeats 3200000 in
open Ws12Member3 in
theorem solution
    (N : ℕ) [NeZero N] (hpN : ¬ 3 ∣ N) (hε : ∃ q : ℕ, q.Prime ∧ q ∣ N ∧ q % 3 = 2)
    (K : Type) [Field K] [CharP K 3] [IsAlgClosed K] (m : ℕ)
    (D : Divisor K ↥(modularFunctionFieldFullC K N))
    (hD : ∀ w : Place K ↥(modularFunctionFieldFullC K N),
      D w = (if 0 < w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N))
               then (2 * (m : ℤ) * w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N))) / 3 else 0)
          + (if 0 < w.ord ((⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) - algebraMap K _ 1728)
               then ((m : ℤ) * w.ord ((⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) - algebraMap K _ 1728)) / 2 else 0)
          + (if w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) < 0
               then (m : ℤ) * w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) else 0))
    (G : ↥(modularFunctionFieldFullC K N)) (hG : IsModPFormFn K m (G : LaurentSeries K)) :
    G ∈ riemannRochSpace D := by
  classical
  set j : ↥(modularFunctionFieldFullC K N) := ⟨jqModC K, jqModC_mem_full K N⟩ with hjdef
  have hjcoe : (j : LaurentSeries K) = jqModC K := rfl

  have h1728 : (1728 : K) = 0 := by
    have h : ((1728 : ℕ) : K) = 0 := (CharP.cast_eq_zero_iff K 3 1728).mpr (by norm_num)
    exact_mod_cast h
  have h1728L : algebraMap K (LaurentSeries K) 1728 = 0 := by rw [h1728, map_zero]
  have h1728F : algebraMap K ↥(modularFunctionFieldFullC K N) 1728 = 0 := by rw [h1728, map_zero]
  have hjsub : j - algebraMap K ↥(modularFunctionFieldFullC K N) 1728 = j := by rw [h1728F, sub_zero]

  have hj0 : j ≠ 0 := by
    intro h
    have : (j : LaurentSeries K) = 0 := by rw [h]; rfl
    rw [hjcoe] at this
    exact (transcendental_jqModC K) (this ▸ isAlgebraic_zero)
  rw [mem_riemannRochSpace_iff]
  intro w
  rcases eq_or_ne G 0 with hG0 | hG0
  · exact Or.inl hG0
  right
  rw [hD w, hjsub]

  obtain ⟨hint1, hint2⟩ := hG
  simp only [h1728L, sub_zero] at hint1 hint2
  try rw [mul_assoc, ← pow_add] at hint1
  try rw [mul_assoc, ← pow_add] at hint2
  have hcoe1 : ((G ^ 6 * j ^ (4 * m + 3 * m) : ↥(modularFunctionFieldFullC K N)) : LaurentSeries K) =
      (G : LaurentSeries K) ^ 6 * jqModC K ^ (4 * m + 3 * m) := by
    push_cast; rfl
  have hcoe2 : ((G ^ 2 * j ^ (m + m) : ↥(modularFunctionFieldFullC K N)) : LaurentSeries K) =
      (G : LaurentSeries K) ^ 2 * jqModC K ^ (m + m) := by
    push_cast; rfl
  rw [← hcoe1] at hint1
  rw [← hcoe2] at hint2

  have hord1 : w.ord (G ^ 6 * j ^ (4 * m + 3 * m)) = 6 * w.ord G + (7 * m : ℕ) * w.ord j := by
    rw [w.ord_mul (pow_ne_zero _ hG0) (pow_ne_zero _ hj0), ord_pow, ord_pow]
    push_cast; ring
  have hord2 : w.ord (G ^ 2 * j ^ (m + m)) = 2 * w.ord G + (2 * m : ℕ) * w.ord j := by
    rw [w.ord_mul (pow_ne_zero _ hG0) (pow_ne_zero _ hj0), ord_pow, ord_pow]
    push_cast; ring

  rcases lt_trichotomy (w.ord j) 0 with hneg | hzero | hpos
  ·
    have hinv : j⁻¹ ∈ w.toValuationSubring := mem_of_ord_nonneg w (by rw [Place.ord_inv]; omega)
    have hjinvcoe : ((j⁻¹ : ↥(modularFunctionFieldFullC K N)) : LaurentSeries K) = (jqModC K)⁻¹ := by push_cast; rfl
    rw [← hjinvcoe] at hint2
    have hmem := mem_of_isIntegral_adjoin w hinv _ hint2
    have h0 := ord_nonneg_of_mem w hmem
    rw [hord2] at h0
    rw [if_neg (show ¬ 0 < w.ord j from by omega), if_neg (show ¬ 0 < w.ord j from by omega), if_pos hneg]
    simp only [zero_add]
    push_cast at h0
    nlinarith
  ·
    have hjm : j ∈ w.toValuationSubring := mem_of_ord_nonneg w hzero.ge
    have hmem := mem_of_isIntegral_adjoin w hjm _ hint1
    have h0 := ord_nonneg_of_mem w hmem
    rw [hord1, hzero] at h0
    rw [if_neg (show ¬ 0 < w.ord j from by omega), if_neg (show ¬ 0 < w.ord j from by omega),
      if_neg (show ¬ w.ord j < 0 from by omega)]
    simp only [add_zero, neg_zero]
    push_cast at h0
    omega
  ·
    have hjm : j ∈ w.toValuationSubring := mem_of_ord_nonneg w hpos.le
    have hmem := mem_of_isIntegral_adjoin w hjm _ hint1
    have h0 := ord_nonneg_of_mem w hmem
    rw [hord1] at h0
    rw [if_pos hpos, if_pos hpos, if_neg (show ¬ w.ord j < 0 from by omega)]
    simp only [add_zero]
    push_cast at h0
    rcases ord_jq_eq_three_or_six N hpN hε K w hpos with he | he
    · rw [he] at h0 ⊢
      omega
    · rw [he] at h0 ⊢
      omega

end S_ModularCurve_mem_riemannRochSpace_of_isModPFormFn_of_charP_three
end P2MW
export P2MW.S_ModularCurve_mem_riemannRochSpace_of_isModPFormFn_of_charP_three (solution)
