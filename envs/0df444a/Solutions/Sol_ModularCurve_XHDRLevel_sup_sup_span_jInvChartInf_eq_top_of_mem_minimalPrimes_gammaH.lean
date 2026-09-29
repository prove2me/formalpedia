-- Prove2me | solution 1 for ModularCurve.XHDRLevel.sup_sup_span_jInvChartInf_eq_top_of_mem_minimalPrimes_gammaH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/c2527980-7da1-555c-b40a-1b292aa2d239

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin
import Theorems.Thm_ModularCurve_XHDRLevel_valuationSubring_eq_gauss_or_eq_comap_atkinLehner_gammaH
import Theorems.Thm_ModularCurve_XHDRLevel_exists_valuationSubring_gauss_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar
import Theorems.Thm_ModularCurve_qExpand_jq_div_pow_mem_chartAlgInf_and_coeff_zero_and_mem_nonunits_gauss
import Theorems.Thm_ModularCurve_diamondAutHBar_apply_eq_self_of_coe_eq_coeffEmb_of_mem_gamma0
import Theorems.Thm_ModularCurve_qExpand_mem_xHFunctionField_of_mem_div
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Theorems.Thm_GaloisRep_irreducible_natCast_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRLevel_sup_sup_span_jInvChartInf_eq_top_of_mem_minimalPrimes_gammaH
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single"
p2m_attr_erase "simp" "ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve ModularCurve ModularCurve.XHDRLevel Polynomial
open scoped MatrixGroups

namespace CuspUnibranch

theorem adjoin_singleton_inv_eq {K L : Type*} [Field K] [Field L] [Algebra K L] (s : L) :
    IntermediateField.adjoin K ({s⁻¹} : Set L) = IntermediateField.adjoin K ({s} : Set L) := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    exact Set.singleton_subset_iff.mpr ((IntermediateField.adjoin K _).inv_mem (IntermediateField.mem_adjoin_simple_self K s))
  · have h1 := (IntermediateField.adjoin K ({s⁻¹} : Set L)).inv_mem (IntermediateField.mem_adjoin_simple_self K s⁻¹)
    rw [inv_inv] at h1
    rw [IntermediateField.adjoin_le_iff]
    exact Set.singleton_subset_iff.mpr h1

theorem mul_mem_nonunits {F : Type*} [Field F] (V : ValuationSubring F) {x y : F}
    (hx : x ∈ V.nonunits) (hy : y ∈ V) : x * y ∈ V.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hx ⊢
  rw [map_mul]
  calc V.valuation x * V.valuation y ≤ V.valuation x * 1 := mul_le_mul_right ((V.valuation_le_one_iff y).mpr hy) _
    _ = V.valuation x := mul_one _
    _ < 1 := hx

theorem branch_of_branch_inv {R F : Type*} [CommRing R] [Field F] [Algebra R F] (ϖ : R) (V : ValuationSubring F)
    (hRV : ∀ r : R, algebraMap R F r ∈ V) (j : F) (hj0 : j ≠ 0) (hjV : j ∈ V) (hjiV : j⁻¹ ∈ V)
    (h : ∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) → Polynomial.aeval j⁻¹ P ∈ V ∧ (Polynomial.aeval j⁻¹ P)⁻¹ ∈ V) :
    ∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) → Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V := by
  intro P hP

  have hmem : Polynomial.aeval j P ∈ V := by
    rw [Polynomial.aeval_eq_sum_range]
    refine V.toSubring.sum_mem fun n _ => ?_
    rw [Algebra.smul_def]
    exact mul_mem (hRV _) (pow_mem hjV n)
  refine ⟨hmem, ?_⟩

  set N := P.natDegree with hN
  haveI : Invertible j := invertibleOfNonzero hj0
  have hrefl : Polynomial.aeval j⁻¹ (Polynomial.reflect N P) * j ^ N = Polynomial.aeval j P := by
    have := Polynomial.eval₂_reflect_mul_pow (algebraMap R F) j N P le_rfl
    rw [invOf_eq_inv] at this
    exact this

  have hP' : ¬ (Polynomial.C ϖ ∣ Polynomial.reflect N P) := by
    intro hd
    apply hP
    rw [Polynomial.C_dvd_iff_dvd_coeff] at hd ⊢
    intro n
    by_cases hn : n ≤ N
    · have := hd (N - n)
      rwa [Polynomial.coeff_reflect, Polynomial.revAt_le (Nat.sub_le N n), Nat.sub_sub_self hn] at this
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hn)]
      exact dvd_zero _
  obtain ⟨-, hinv⟩ := h _ hP'
  have : (Polynomial.aeval j P)⁻¹ = (Polynomial.aeval j⁻¹ (Polynomial.reflect N P))⁻¹ * (j⁻¹) ^ N := by
    rw [← hrefl, mul_inv, inv_pow]
  rw [this]
  exact mul_mem hinv (pow_mem hjiV N)

theorem fd_adjoin_inv {K L : Type*} [Field K] [Field L] [Algebra K L] (s : L)
    (h : FiniteDimensional ↥(IntermediateField.adjoin K ({s} : Set L)) L) :
    FiniteDimensional ↥(IntermediateField.adjoin K ({s⁻¹} : Set L)) L := by
  rw [adjoin_singleton_inv_eq]; exact h

theorem sep_adjoin_inv {K L : Type*} [Field K] [CharZero K] [Field L] [CharZero L] [Algebra K L] (s : L)
    (h : FiniteDimensional ↥(IntermediateField.adjoin K ({s} : Set L)) L) :
    Algebra.IsSeparable ↥(IntermediateField.adjoin K ({s⁻¹} : Set L)) L := by
  haveI := fd_adjoin_inv s h
  infer_instance

end CuspUnibranch

open CuspUnibranch in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (P P' : Ideal ↥(chartAlgInf p (ΓM M H) hj))
    (hP : P ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgInf p (ΓM M H) hj))}).minimalPrimes)
    (hP' : P' ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgInf p (ΓM M H) hj))}).minimalPrimes) (hne : P ≠ P') :
    P ⊔ P' ⊔ Ideal.span {AlgebraicCurve.TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)} = ⊤ := by
  classical
  haveI hp0 : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero (M / p) := neZero_div p M hpM
  haveI : (CohCarrier.GammaH M H).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)
  haveI : IsPrincipalIdealRing (R p) := GaloisRep.isPrincipalIdealRing_ratLocalizedAt p
  haveI : IsFractionRing (R p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p

  have hprime : Prime ((p : ℕ) : R p) :=
    (GaloisRep.irreducible_natCast_ratLocalizedAt p Fact.out).prime

  have hIST : @IsScalarTower (R p) ℚ ↥(qExpFunctionFieldC ℚ (ΓM M H)) _
      (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ (ΓM M H))).toSMul _ :=
    @IsScalarTower.of_algebraMap_eq' (R p) ℚ ↥(qExpFunctionFieldC ℚ (ΓM M H)) _ _ _ _
      (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ (ΓM M H))) _
      (RingHom.ext fun r => by
        show ((r : ℚ) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) =
          @algebraMap ℚ ↥(qExpFunctionFieldC ℚ (ΓM M H)) _ _ (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ (ΓM M H))) (r : ℚ)
        exact (eq_ratCast _ _).symm)
  have hjq : ((jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = coeffEmb ℚ jq := by
    rw [coe_jAt]
    show jq = coeffMap (algebraMap ℚ ℚ) jq
    ext k
    rw [coeffMap_coeff, Algebra.algebraMap_self, RingHom.id_apply]
  have htj : Transcendental (R p) (jAt (ΓM M H) hj) :=
    @ModularCurve.transcendental_of_coe_eq_coeffEmb_jq ℚ _ _ (qExpFunctionFieldC ℚ (ΓM M H)) (R p) _ _ _ _ _ hIST _ hjq
  have htj' : Transcendental (R p) (jAt (ΓM M H) hj)⁻¹ := fun h => htj (by simpa using h.inv)
  have hFD := (ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index ℚ (CohCarrier.GammaH M H)
    (translation_mem_GammaH M H) _ le_rfl (fun γ h => Or.inl h) (jAt (ΓM M H) hj) (coe_jAt _ _)).1
  have hFD' := @fd_adjoin_inv ℚ ↥(qExpFunctionFieldC ℚ (ΓM M H)) _ _ (SubalgebraClass.toAlgebra _) _ hFD
  have hsep' := @sep_adjoin_inv ℚ ↥(qExpFunctionFieldC ℚ (ΓM M H)) _ _ _ _ (SubalgebraClass.toAlgebra _) _ hFD
  haveI : Fact ((jAt (ΓM M H) hj)⁻¹ ≠ 0) := ⟨inv_ne_zero (Fact.out)⟩
  have hj0 : (jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H))) ≠ 0 := Fact.out

  have hcast : algebraMap (R p) ↥(chartAlgInf p (ΓM M H) hj) ((p : ℕ) : R p) = ((p : ℕ) : ↥(chartAlgInf p (ΓM M H) hj)) :=
    map_natCast _ p
  have branch : ∀ Q : Ideal ↥(chartAlgInf p (ΓM M H) hj), Q ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgInf p (ΓM M H) hj))}).minimalPrimes →
      ∃ V : ValuationSubring ↥(qExpFunctionFieldC ℚ (ΓM M H)),
        (∀ f : ↥(chartAlgInf p (ΓM M H) hj), (f : ↥(qExpFunctionFieldC ℚ (ΓM M H))) ∈ V) ∧
        (∀ f : ↥(chartAlgInf p (ΓM M H) hj), f ∈ Q ↔ (f : ↥(qExpFunctionFieldC ℚ (ΓM M H))) ∈ V.nonunits) ∧
        algebraMap (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) ((p : ℕ) : R p) ∈ V.nonunits ∧
        (∀ Q' : Polynomial (R p), ¬ (Polynomial.C ((p : ℕ) : R p) ∣ Q') →
          Polynomial.aeval (jAt (ΓM M H) hj)⁻¹ Q' ∈ V ∧ (Polynomial.aeval (jAt (ΓM M H) hj)⁻¹ Q')⁻¹ ∈ V) := by
    intro Q hQ
    rw [← hcast] at hQ
    obtain ⟨V, -, h1, h2, h3, h4⟩ :=
      @AlgebraicCurve.TwoChartIntegralModel.exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin (R p) _ _ _ ℚ _ _ _
        ↥(qExpFunctionFieldC ℚ (ΓM M H)) _ _ (SubalgebraClass.toAlgebra _) hIST (jAt (ΓM M H) hj)⁻¹ _ htj' hFD' hsep'
        ((p : ℕ) : R p) hprime Q hQ
    exact ⟨V, h1, h2, h3, h4⟩

  obtain ⟨W₀, hW₀, hRW₀, hpW₀, hjW₀, -⟩ := ModularCurve.XHDRLevel.exists_valuationSubring_gauss_qExpFunctionFieldC p (ΓM M H) hj
  obtain ⟨σ, hσq, hσdia⟩ := ModularCurve.exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar p M H hpM hpM2 hHp
  have classify : ∀ V : ValuationSubring ↥(qExpFunctionFieldC ℚ (ΓM M H)),
      (∀ f : ↥(chartAlgInf p (ΓM M H) hj), (f : ↥(qExpFunctionFieldC ℚ (ΓM M H))) ∈ V) →
      algebraMap (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) ((p : ℕ) : R p) ∈ V.nonunits →
      (∀ Q' : Polynomial (R p), ¬ (Polynomial.C ((p : ℕ) : R p) ∣ Q') →
          Polynomial.aeval (jAt (ΓM M H) hj)⁻¹ Q' ∈ V ∧ (Polynomial.aeval (jAt (ΓM M H) hj)⁻¹ Q')⁻¹ ∈ V) →
      V = W₀ ∨ V = W₀.comap σ.toAlgHom.toRingHom := by
    intro V hOV hpV hbr
    have hRV : ∀ a : R p, algebraMap (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) a ∈ V :=
      fun a => hOV (algebraMap (R p) ↥(chartAlgInf p (ΓM M H) hj) a)
    have hjiV : (jAt (ΓM M H) hj)⁻¹ ∈ V := hOV (TwoChartIntegralModel.jInvChartInf (R p) _ (jAt (ΓM M H) hj))
    have hX : ¬ (Polynomial.C ((p : ℕ) : R p) ∣ (Polynomial.X : Polynomial (R p))) := by
      intro hd
      have := (Polynomial.C_dvd_iff_dvd_coeff _ _).mp hd 1
      rw [Polynomial.coeff_X_one] at this
      exact hprime.not_unit (isUnit_of_dvd_one this)
    have hjV : (jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H))) ∈ V := by
      have := (hbr _ hX).2
      rwa [Polynomial.aeval_X, inv_inv] at this
    refine ModularCurve.XHDRLevel.valuationSubring_eq_gauss_or_eq_comap_atkinLehner_gammaH p M H hpM hpM2 hHp hj σ hσq W₀ hW₀ V
      hRV ?_ ?_
    · intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul]
      rw [mul_comm]
      exact mul_mem_nonunits V hpV (hRV b)
    · intro Q hQ
      refine branch_of_branch_inv ((p : ℕ) : R p) V hRV _ hj0 hjV hjiV hbr Q ?_
      intro hd
      apply hQ
      obtain ⟨Q₁, rfl⟩ := hd
      rw [Polynomial.map_mul, Polynomial.map_C, map_natCast, ZMod.natCast_self, Polynomial.C_0, zero_mul]

  obtain ⟨V, hOV, hcenV, hpV, hbrV⟩ := branch P hP
  obtain ⟨V', hOV', hcenV', hpV', hbrV'⟩ := branch P' hP'
  have hVV' : V ≠ V' := by
    intro h; apply hne; ext f; rw [hcenV, hcenV', h]

  have hjN : jqModC ℚ ∈ qExpFunctionFieldC ℚ (ΓN p M H hpM) := (jAt (ΓN p M H hpM) hj).2
  have hj'mem : qExpand ℚ p (jqModC ℚ) ∈ qExpFunctionFieldC ℚ (ΓM M H) :=
    ModularCurve.qExpand_mem_xHFunctionField_of_mem_div p M H hpM hjN
  set j' : ↥(qExpFunctionFieldC ℚ (ΓM M H)) := ⟨qExpand ℚ p (jqModC ℚ), hj'mem⟩ with hj'def
  have hσj : σ (jAt (ΓM M H) hj) = j' := Subtype.ext (hσq (jAt (ΓM M H) hj) (jAt (ΓN p M H hpM) hj) rfl)
  have hcop : Nat.Coprime p (M / p) := by
    rw [Nat.Prime.coprime_iff_not_dvd Fact.out]
    intro hd
    apply hpM2
    obtain ⟨k, hk⟩ := hd
    refine ⟨k, ?_⟩
    calc M = p * (M / p) := (Nat.mul_div_cancel' hpM).symm
      _ = p ^ 2 * k := by rw [hk]; ring
  have hσj' : σ j' = jAt (ΓM M H) hj := by
    let c : (ZMod (M / p))ˣ := ZMod.unitOfCoprime p hcop
    have hc : (c : ZMod (M / p)) = (p : ZMod (M / p)) := ZMod.coe_unitOfCoprime p hcop
    have h2 := hσdia c hc j' (jAt (ΓN p M H hpM) hj) rfl
    have hfix := ModularCurve.diamondAutHBar_apply_eq_self_of_coe_eq_coeffEmb_of_mem_gamma0 (M / p) (infSubgroup p M H hpM) c
      ⟨coeffEmb (AlgebraicClosure ℚ) ((jAt (ΓN p M H hpM) hj : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jAt (ΓN p M H hpM) hj).2⟩ (jqModC ℚ)
      (qExpFunctionFieldC_mono ℚ le_top hj) rfl
    rw [hfix] at h2
    apply Subtype.ext
    rw [coe_jAt]
    exact (coeffEmb (AlgebraicClosure ℚ)).injective h2
  obtain ⟨ht𝒪, -, -, ⟨ht1, -⟩, ⟨htp, -⟩⟩ :=
    ModularCurve.qExpand_jq_div_pow_mem_chartAlgInf_and_coeff_zero_and_mem_nonunits_gauss p (qExpFunctionFieldC ℚ (ΓM M H))
      (jAt (ΓM M H) hj) (coe_jAt _ _) j' rfl σ hσj hσj' W₀ hW₀

  have key : ∀ P₀ P₁ : Ideal ↥(chartAlgInf p (ΓM M H) hj),
      (∀ f : ↥(chartAlgInf p (ΓM M H) hj), f ∈ P₀ ↔ (f : ↥(qExpFunctionFieldC ℚ (ΓM M H))) ∈ W₀.nonunits) →
      (∀ f : ↥(chartAlgInf p (ΓM M H) hj), f ∈ P₁ ↔ (f : ↥(qExpFunctionFieldC ℚ (ΓM M H))) ∈ (W₀.comap σ.toAlgHom.toRingHom).nonunits) →
      P₀ ⊔ P₁ ⊔ Ideal.span {AlgebraicCurve.TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)} = ⊤ := by
    intro P₀ P₁ h₀ h₁
    let T : ↥(chartAlgInf p (ΓM M H) hj) := ⟨j' * ((jAt (ΓM M H) hj)⁻¹) ^ p, ht𝒪⟩
    let U : ↥(chartAlgInf p (ΓM M H) hj) := AlgebraicCurve.TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)
    have hT1 : T - 1 ∈ P₀ := (h₀ (T - 1)).mpr ht1
    have hTp : T ^ p - U ^ (p ^ 2 - 1) ∈ P₁ := (h₁ (T ^ p - U ^ (p ^ 2 - 1))).mpr htp
    have hTp1 : T ^ p - 1 ∈ P₀ := by
      obtain ⟨r, hr⟩ := sub_dvd_pow_sub_pow T 1 p
      rw [one_pow] at hr
      rw [hr]
      exact Ideal.mul_mem_right _ _ hT1
    have hppos : 0 < p ^ 2 - 1 := by
      have h2 := (Fact.out : p.Prime).two_le
      have : 4 ≤ p ^ 2 := by nlinarith
      omega
    have hUmem : U ∈ Ideal.span ({U} : Set ↥(chartAlgInf p (ΓM M H) hj)) := Ideal.subset_span (Set.mem_singleton U)
    have hU : U ^ (p ^ 2 - 1) ∈ Ideal.span ({U} : Set ↥(chartAlgInf p (ΓM M H) hj)) :=
      Ideal.pow_mem_of_mem (Ideal.span ({U} : Set ↥(chartAlgInf p (ΓM M H) hj))) hUmem (p ^ 2 - 1) hppos
    rw [Ideal.eq_top_iff_one]
    have e1 : (1 : ↥(chartAlgInf p (ΓM M H) hj)) = (T ^ p - U ^ (p ^ 2 - 1)) + U ^ (p ^ 2 - 1) - (T ^ p - 1) := by
      rw [sub_add_cancel, sub_sub_cancel]
    rw [e1]
    refine Ideal.sub_mem _ (Ideal.add_mem _ ?_ ?_) ?_
    · exact Ideal.mem_sup_left (Ideal.mem_sup_right hTp)
    · exact Ideal.mem_sup_right hU
    · exact Ideal.mem_sup_left (Ideal.mem_sup_left hTp1)
  rcases classify V hOV hpV hbrV with hV | hV <;> rcases classify V' hOV' hpV' hbrV' with hV' | hV'
  · exact absurd (hV.trans hV'.symm) hVV'
  · exact key P P' (fun f => by rw [hcenV f, hV]) (fun f => by rw [hcenV' f, hV'])
  · rw [sup_comm P P']
    exact key P' P (fun f => by rw [hcenV' f, hV']) (fun f => by rw [hcenV f, hV])
  · exact absurd (hV.trans hV'.symm) hVV'

end S_ModularCurve_XHDRLevel_sup_sup_span_jInvChartInf_eq_top_of_mem_minimalPrimes_gammaH
end P2MW
export P2MW.S_ModularCurve_XHDRLevel_sup_sup_span_jInvChartInf_eq_top_of_mem_minimalPrimes_gammaH (solution)
