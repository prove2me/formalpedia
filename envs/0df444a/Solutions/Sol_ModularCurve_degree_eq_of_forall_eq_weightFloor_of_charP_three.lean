-- Prove2me | solution 1 for ModularCurve.degree_eq_of_forall_eq_weightFloor_of_charP_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/9c735e17-5386-5c88-9e4f-928133e62a11

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_AlgebraicCurve_degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_ord_jGeomGen_eq_three_or_eq_six_of_exists_prime_dvd_mod_three_eq_two_of_isAlgClosed
import Theorems.Thm_ModularCurve_jGeomGen_eq_mk_jqModC
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_ncard_setOf_ord_jGeomGen_eq_three_and_eq_six_of_exists_prime_dvd_mod_three_eq_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_degree_eq_of_forall_eq_weightFloor_of_charP_three
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.coe_nodeEquivOfPlaces_apply"
p2m_attr_erase "simp" "ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice"
p2m_attr_erase "simp" "PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply"

set_option autoImplicit false

open AlgebraicCurve ModularCurve

namespace Ws12Deg3

theorem nuThree_eq_zero_of_prime_dvd (N : ℕ) (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hq3 : q % 3 = 2) : nuThree N = 0 := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  rw [nuThree, Nat.card_eq_zero]
  left
  refine ⟨fun ⟨x, hx⟩ => ?_⟩

  let φ : ZMod N →+* ZMod q := ZMod.castHom hqN (ZMod q)
  set y : ZMod q := φ x with hy
  have hy1 : y ^ 2 + y + 1 = 0 := by
    have := congrArg φ hx
    simpa [map_add, map_pow, map_one] using this
  have hy3 : y ^ 3 = 1 := by
    have : y ^ 3 - 1 = (y - 1) * (y ^ 2 + y + 1) := by ring
    rw [hy1, mul_zero, sub_eq_zero] at this
    exact this

  have hq3' : q ≠ 3 := by rintro rfl; norm_num at hq3
  have hy_ne : y ≠ 1 := by
    intro h
    rw [h] at hy1
    have h3 : (3 : ZMod q) = 0 := by
      have : (1 : ZMod q) ^ 2 + 1 + 1 = 3 := by norm_num
      rw [← this]; exact hy1
    have : (q : ℕ) ∣ 3 := by
      have h3' : ((3 : ℕ) : ZMod q) = 0 := by exact_mod_cast h3
      exact (ZMod.natCast_eq_zero_iff 3 q).mp h3'
    have := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp this
    exact hq3' this

  have hord : orderOf y = 3 := orderOf_eq_prime hy3 hy_ne
  have hyu : IsUnit y := IsUnit.of_pow_eq_one hy3 (by norm_num)
  have hdvd : 3 ∣ q - 1 := by
    rw [← ZMod.card_units q, ← hord, ← hyu.unit_spec, orderOf_units]
    exact orderOf_dvd_card

  have hq1 : 1 ≤ q := hq.one_lt.le
  omega

theorem ord_jq_eq_three_or_six (N : ℕ) [NeZero N] (hpN : ¬ 3 ∣ N)
    (hε : ∃ q : ℕ, q.Prime ∧ q ∣ N ∧ q % 3 = 2) (K : Type) [Field K] [CharP K 3] [IsAlgClosed K]
    (w : Place K ↥(modularFunctionFieldFullC K N)) (hw : 0 < w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N))) :
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

theorem ncard_ord_jq_eq_three (N : ℕ) [NeZero N] (hpN : ¬ 3 ∣ N)
    (hε : ∃ q : ℕ, q.Prime ∧ q ∣ N ∧ q % 3 = 2) (K : Type) [Field K] [CharP K 3] [IsAlgClosed K] :
    (Set.ncard {w : Place K ↥(modularFunctionFieldFullC K N) | w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) = 3} : ℚ) = (nuTwo N : ℚ) := by
  have key : ∀ (E : IntermediateField K (LaurentSeries K)) (hE : modularFunctionFieldC K N = E)
      (hmem : jqModC K ∈ E),
      (Set.ncard {w : Place K ↥E | w.ord (⟨jqModC K, hmem⟩ : ↥E) = 3} : ℚ) = (nuTwo N : ℚ) := by
    intro E hE hmem
    subst hE
    have hj : (⟨jqModC K, hmem⟩ : ↥(modularFunctionFieldC K N)) = jGeomGen K N := (jGeomGen_eq_mk_jqModC K N).symm
    rw [hj]
    exact (ncard_setOf_ord_jGeomGen_eq_three_and_eq_six_of_exists_prime_dvd_mod_three_eq_two N hpN hε K).1
  exact key _ (modularFunctionFieldC_eq_modularFunctionFieldFullC K 3 N hpN) (jqModC_mem_full K N)

end Ws12Deg3

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
open Ws12Deg3 in
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
               then (m : ℤ) * w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) else 0)) :
    (D.degree : ℚ) = (m : ℚ) * (2 * genusFormula N - 2) + ((m / 2 : ℕ) : ℚ) * (nuTwo N : ℚ)
        + ((2 * m / 3 : ℕ) : ℚ) * (nuThree N : ℚ) + (m : ℚ) * (cuspCount N : ℚ) := by
  classical
  set b : ℕ := m / 2 with hb
  set j : ↥(modularFunctionFieldFullC K N) := ⟨jqModC K, jqModC_mem_full K N⟩ with hjdef
  have hjcoe : (j : LaurentSeries K) = jqModC K := rfl

  have hN : (N : K) ≠ 0 := fun h => hpN ((CharP.cast_eq_zero_iff K 3 N).mp h)
  have h1728 : (1728 : K) = 0 := by
    have h : ((1728 : ℕ) : K) = 0 := (CharP.cast_eq_zero_iff K 3 1728).mpr (by norm_num)
    exact_mod_cast h
  have hjsub : j - algebraMap K ↥(modularFunctionFieldFullC K N) 1728 = j := by rw [h1728, map_zero, sub_zero]
  obtain ⟨q, hq, hqN, hq3⟩ := hε
  have hν3 : nuThree N = 0 := nuThree_eq_zero_of_prime_dvd N q hq hqN hq3
  haveI : IsCurveOver K ↥(modularFunctionFieldFullC K N) := isCurveOver_modularFunctionFieldFullC K N
  have hdeg1 : ∀ v : Place K ↥(modularFunctionFieldFullC K N), v.deg = 1 :=
    IsCurveOver.forall_deg_eq_one_of_isAlgClosed

  have hj0 : j ≠ 0 := by
    intro h
    have : (j : LaurentSeries K) = 0 := by rw [h]; rfl
    rw [hjcoe] at this
    exact (transcendental_jqModC K) (this ▸ isAlgebraic_zero)
  have htr : Transcendental K j := fun h =>
    (transcendental_jqModC K) (by simpa using h.algHom (modularFunctionFieldFullC K N).val)

  have hD' : ∀ w : Place K ↥(modularFunctionFieldFullC K N),
      D w = (if 0 < w.ord j then (2 * (m : ℤ) * w.ord j) / 3 + ((m : ℤ) * w.ord j) / 2 else 0)
          + (if w.ord j < 0 then (m : ℤ) * w.ord j else 0) := by
    intro w
    rw [hD w, hjsub]
    split_ifs <;> ring

  obtain ⟨Dj, hDj, hDj0⟩ :=
    HasPrincipalDivisors.exists_divisor (K := K) (F := ↥(modularFunctionFieldFullC K N)) j hj0
  set S0 := Dj.support.filter (fun v => 0 < v.ord j) with hS0def
  set T := Dj.support.filter (fun v => v.ord j < 0) with hTdef
  have hS0 : ∀ v, v ∈ S0 ↔ 0 < v.ord j := fun v => by
    rw [hS0def, Finset.mem_filter, Finsupp.mem_support_iff, hDj v]
    exact ⟨And.right, fun h => ⟨ne_of_gt h, h⟩⟩
  have hT : ∀ v, v ∈ T ↔ v.ord j < 0 := fun v => by
    rw [hTdef, Finset.mem_filter, Finsupp.mem_support_iff, hDj v]
    exact ⟨And.right, fun h => ⟨ne_of_lt h, h⟩⟩

  have hψpos : 0 < dedekindPsi N := by
    rw [dedekindPsi]
    have h1 : (1 : ℕ) ∈ N.divisors.filter Squarefree := by
      rw [Finset.mem_filter]; exact ⟨Nat.one_mem_divisors.2 (NeZero.ne N), squarefree_one⟩
    have := Finset.single_le_sum (f := fun d => N / d) (fun _ _ => Nat.zero_le _) h1
    simp only [Nat.div_one] at this
    exact lt_of_lt_of_le (Nat.pos_of_ne_zero (NeZero.ne N)) this
  have hfr := finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi K N hN
  haveI : FiniteDimensional ↥(IntermediateField.adjoin K ({j} : Set ↥(modularFunctionFieldFullC K N)))
      ↥(modularFunctionFieldFullC K N) := Module.finite_of_finrank_pos (by rw [hfr]; exact hψpos)
  let P : Divisor K ↥(modularFunctionFieldFullC K N) := ∑ v ∈ T, Finsupp.single v (-(v.ord j))
  have hP : ∀ v, P v = max 0 (-v.ord j) := by
    intro v
    simp only [P, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply]
    rw [Finset.sum_ite_eq' T v]
    by_cases hv : v ∈ T
    · rw [if_pos hv, max_eq_right]; have := (hT v).1 hv; omega
    · rw [if_neg hv, max_eq_left]; have := (hT v).not.1 hv; omega
  have hPdeg := degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental j htr P hP
  rw [hfr] at hPdeg
  have hPdeg' : Divisor.degree P = ∑ v ∈ T, -(v.ord j) := by
    simp only [P, map_sum, Divisor.degree_single, hdeg1, Nat.cast_one, mul_one]
  have hTsum : ∑ v ∈ T, v.ord j = -(dedekindPsi N : ℤ) := by
    have : ∑ v ∈ T, -(v.ord j) = (dedekindPsi N : ℤ) := hPdeg'.symm.trans hPdeg
    rw [Finset.sum_neg_distrib] at this
    linarith

  have hdegsum : ∀ E : Divisor K ↥(modularFunctionFieldFullC K N), Divisor.degree E = ∑ v ∈ E.support, E v := by
    intro E
    conv_lhs => rw [← Finsupp.sum_single E]
    rw [Finsupp.sum, map_sum]
    simp only [Divisor.degree_single, hdeg1, Nat.cast_one, mul_one]

  have hsupp_j : Dj.support = S0 ∪ T := by
    ext v
    rw [Finset.mem_union, hS0, hT, Finsupp.mem_support_iff, hDj v]
    constructor
    · intro h; rcases lt_trichotomy (v.ord j) 0 with h' | h' | h'
      · exact Or.inr h'
      · exact absurd h' h
      · exact Or.inl h'
    · rintro (h | h) <;> omega
  have hdisj_0T : Disjoint S0 T := by
    rw [Finset.disjoint_left]; intro v h0 hT'
    have := (hS0 v).1 h0; have := (hT v).1 hT'; omega
  have hS0sum : ∑ v ∈ S0, v.ord j = (dedekindPsi N : ℤ) := by
    have h := hdegsum Dj
    rw [hDj0, hsupp_j, Finset.sum_union hdisj_0T] at h
    simp only [hDj] at h
    linarith

  have hval0 : ∀ v ∈ S0, v.ord j = 3 ∨ v.ord j = 6 := fun v hv =>
    ord_jq_eq_three_or_six N hpN ⟨q, hq, hqN, hq3⟩ K v ((hS0 v).1 hv)
  set A0 := S0.filter (fun v => v.ord j = 3) with hA0
  set B0 := S0.filter (fun v => ¬ v.ord j = 3) with hB0
  have hA0val : ∀ v : Place K ↥(modularFunctionFieldFullC K N), v ∈ A0 → v.ord j = 3 :=
    fun v hv => (Finset.mem_filter.1 hv).2
  have hB0val : ∀ v : Place K ↥(modularFunctionFieldFullC K N), v ∈ B0 → v.ord j = 6 := fun v hv => by
    rw [hB0, Finset.mem_filter] at hv
    exact (hval0 v hv.1).resolve_left hv.2
  have hsum0 : 3 * (A0.card : ℤ) + 6 * B0.card = (dedekindPsi N : ℤ) := by
    rw [← hS0sum, ← Finset.sum_filter_add_sum_filter_not S0 (fun v => v.ord j = 3)]
    have hA : ∑ v ∈ A0, v.ord j = ∑ v ∈ A0, (3 : ℤ) := Finset.sum_congr rfl fun v hv => hA0val v hv
    have hB : ∑ v ∈ B0, v.ord j = ∑ v ∈ B0, (6 : ℤ) := Finset.sum_congr rfl fun v hv => hB0val v hv
    rw [hA, hB]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring

  have hA0set : ({w : Place K ↥(modularFunctionFieldFullC K N) | w.ord j = 3} : Set _) = ↑A0 := by
    ext w
    simp only [Set.mem_setOf_eq, Finset.coe_filter, hA0]
    constructor
    · intro h; exact ⟨(hS0 w).2 (by omega), h⟩
    · intro h; exact h.2
  have hA0card : (A0.card : ℚ) = nuTwo N := by
    have h := ncard_ord_jq_eq_three N hpN ⟨q, hq, hqN, hq3⟩ K
    rw [hA0set, Set.ncard_coe_finset] at h
    exact h

  have h32 : ((m : ℤ) * 3) / 2 = (m : ℤ) + (b : ℤ) := by omega
  have hDS0A : ∀ v ∈ A0, D v = 2 * (m : ℤ) + ((m : ℤ) + (b : ℤ)) := fun v hv => by
    have hv' : v ∈ S0 := (Finset.mem_filter.1 hv).1
    have h0 := (hS0 v).1 hv'
    rw [hD' v, if_pos h0, if_neg (show ¬ v.ord j < 0 from by omega), hA0val v hv, ← h32]
    have e1 : (2 * (m : ℤ) * 3) / 3 = 2 * (m : ℤ) := by omega
    rw [e1]; ring
  have hDS0B : ∀ v ∈ B0, D v = 7 * (m : ℤ) := fun v hv => by
    have hv' : v ∈ S0 := (Finset.mem_filter.1 hv).1
    have h0 := (hS0 v).1 hv'
    rw [hD' v, if_pos h0, if_neg (show ¬ v.ord j < 0 from by omega), hB0val v hv]
    have e1 : (2 * (m : ℤ) * 6) / 3 = 4 * (m : ℤ) := by omega
    have e2 : ((m : ℤ) * 6) / 2 = 3 * (m : ℤ) := by omega
    rw [e1, e2]; ring
  have hDT : ∀ v ∈ T, D v = (m : ℤ) * v.ord j := fun v hv => by
    have ht := (hT v).1 hv
    rw [hD' v, if_neg (show ¬ 0 < v.ord j from by omega), if_pos ht]
    ring
  have hDsupp : D.support ⊆ S0 ∪ T := by
    intro v hv
    rw [Finsupp.mem_support_iff, hD' v] at hv
    rw [Finset.mem_union, hS0, hT]
    by_contra h
    push_neg at h
    obtain ⟨h0, h2⟩ := h
    rw [if_neg (not_lt.2 h0), if_neg (not_lt.2 h2)] at hv
    exact hv (by ring)
  have hDdeg : Divisor.degree D = ∑ v ∈ S0 ∪ T, D v := by
    rw [hdegsum D]
    exact Finset.sum_subset hDsupp fun v _ hv => by simpa [Finsupp.mem_support_iff] using hv
  have hsumS0 : ∑ v ∈ S0, D v = (A0.card : ℤ) * (2 * (m : ℤ) + ((m : ℤ) + (b : ℤ))) + (B0.card : ℤ) * (7 * (m : ℤ)) := by
    rw [← Finset.sum_filter_add_sum_filter_not S0 (fun v => v.ord j = 3), Finset.sum_congr rfl hDS0A, Finset.sum_congr rfl hDS0B]
    simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_union hdisj_0T, hsumS0, Finset.sum_congr rfl hDT, ← Finset.mul_sum, hTsum] at hDdeg

  have hB0q : (B0.card : ℚ) = ((dedekindPsi N : ℚ) - 3 * nuTwo N) / 6 := by
    have : (3 : ℚ) * A0.card + 6 * B0.card = dedekindPsi N := by exact_mod_cast hsum0
    rw [hA0card] at this
    linarith
  rw [hDdeg, genusFormula, hν3]
  push_cast
  rw [hA0card, hB0q]
  ring

end S_ModularCurve_degree_eq_of_forall_eq_weightFloor_of_charP_three
end P2MW
export P2MW.S_ModularCurve_degree_eq_of_forall_eq_weightFloor_of_charP_three (solution)
