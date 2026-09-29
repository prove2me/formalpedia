-- Prove2me | solution 1 for ModularCurve.FullLevel.finrank_adjoin_jqNModC_laurentBaseChange_xHFunctionField_levelH_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/21c0ba66-7db1-5920-94bc-f7d3d670c0d1

import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index_of_algebraRat
import Theorems.Thm_ModularCurve_finrank_adjoin_jqNModC_eq_finrank_adjoin_jqModC_of_squarefree
import Theorems.Thm_ModularCurve_FullLevel_two_mul_index_gammaH_levelH_mul_sup_zpowers_neg_one_eq
import Theorems.Thm_ModularCurve_dedekindPsi_eq_prod_primeFactors
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_finrank_adjoin_jqNModC_laurentBaseChange_xHFunctionField_levelH_eq
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
open ModularCurve

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (y : ↥K) (hy : ((y : ↥K) : LaurentSeries L) = ModularCurve.jqNModC L (q * ℓ)) :
    Module.finrank ↥(IntermediateField.adjoin L ({y} : Set ↥K)) ↥K =
      (∏ p ∈ M'.primeFactors, p ^ (M'.factorization p - 1) * (p + 1)) *
        (q * (q ^ 2 - 1)) * (ℓ * (ℓ ^ 2 - 1)) / 2 := by
  have hqp : q.Prime := Fact.out
  have hℓp : ℓ.Prime := Fact.out
  haveI hn0 : NeZero (q * ℓ) := ⟨(Nat.mul_pos hqp.pos hℓp.pos).ne'⟩
  haveI hN0 : NeZero ((q * ℓ) ^ 2 * M') :=
    ⟨(Nat.mul_pos (pow_pos (Nat.mul_pos hqp.pos hℓp.pos) 2) (Nat.pos_of_ne_zero (NeZero.ne M'))).ne'⟩
  subst hK

  have hjq : ModularCurve.jq ∈ ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
      (ModularCurve.FullLevel.levelH (q * ℓ) M') := by
    have h1 : ModularCurve.jqModC ℚ ∈ ModularCurve.modularFunctionFieldC ℚ ((q * ℓ) ^ 2 * M') :=
      ModularCurve.jqModC_mem ℚ _
    rw [ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero] at h1
    exact ModularCurve.x0_le_xHFunctionFieldC ℚ _ _
      (ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ _ h1)
  have hxmem : ModularCurve.jqModC L ∈ ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M')) := by
    rw [← ModularCurve.coeffEmb_jq]
    exact ModularCurve.coeffEmb_mem_laurentBaseChange L hjq
  let x : ↥(ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M'))) := ⟨ModularCurve.jqModC L, hxmem⟩

  have hB1 : Module.finrank ↥(IntermediateField.adjoin L ({x} : Set ↥(ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M'))))) ↥(ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M'))) =
      (CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') ⊔
        Subgroup.zpowers (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)).index :=
    ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index_of_algebraRat
      L ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') x rfl

  have hG3 := ModularCurve.FullLevel.two_mul_index_gammaH_levelH_mul_sup_zpowers_neg_one_eq
    q (by omega) ℓ hℓ3 hℓq M' hqM' hℓM'

  have hG4 := ModularCurve.dedekindPsi_eq_prod_primeFactors M' (NeZero.ne M')
  have hψpos : 0 < ModularCurve.dedekindPsi M' := by
    rw [hG4]
    exact Finset.prod_pos fun p hp =>
      Nat.mul_pos (pow_pos (Nat.prime_of_mem_primeFactors hp).pos _) (Nat.succ_pos p)
  have hidxpos : 0 < (CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') ⊔
        Subgroup.zpowers (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)).index := by
    have h1 : 0 < q * (q ^ 2 - 1) := Nat.mul_pos hqp.pos (Nat.sub_pos_of_lt (by nlinarith))
    have h2 : 0 < ℓ * (ℓ ^ 2 - 1) := Nat.mul_pos hℓp.pos (Nat.sub_pos_of_lt (by nlinarith))
    have := Nat.mul_pos (Nat.mul_pos h1 h2) hψpos
    rw [← hG3] at this
    omega
  haveI : Module.Free ↥(IntermediateField.adjoin L ({x} : Set ↥(ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M'))))) ↥(ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M'))) := Module.Free.of_divisionRing _ _
  haveI : FiniteDimensional ↥(IntermediateField.adjoin L ({x} : Set ↥(ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M'))))) ↥(ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M'))) :=
    Module.finite_of_finrank_pos (by rw [hB1]; exact hidxpos)

  have hsq : Squarefree (q * ℓ) :=
    (Nat.squarefree_mul ((Nat.coprime_primes hqp hℓp).mpr hℓq.symm)).mpr
      ⟨hqp.prime.squarefree, hℓp.prime.squarefree⟩
  have h1lt : 1 < q * ℓ := by nlinarith [hqp.two_le, hℓp.two_le]
  rw [ModularCurve.finrank_adjoin_jqNModC_eq_finrank_adjoin_jqModC_of_squarefree L (q * ℓ) hsq h1lt _ x y
      rfl hy, hB1, ← hG4]
  symm
  apply Nat.div_eq_of_eq_mul_left two_pos
  linarith [hG3]

end S_ModularCurve_FullLevel_finrank_adjoin_jqNModC_laurentBaseChange_xHFunctionField_levelH_eq
end P2MW
export P2MW.S_ModularCurve_FullLevel_finrank_adjoin_jqNModC_laurentBaseChange_xHFunctionField_levelH_eq (solution)
