-- Prove2me | solution 1 for ModularForm.exists_not_dvd_and_forall_isIntegral_mul_qExpansion_alSlash_of_isIntegralQExp_of_even
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/77ab127e-d491-57ae-9b14-d082c06f1b5e

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularForm_qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_exists_slash_atkinLehnerCofactor_eq_sum_smul_of_ratCast_qExpansion_of_even
import Theorems.Thm_ModularCurve_exists_algEquiv_xHFunctionFieldBar_slash_atkinLehnerCofactor
import Theorems.Thm_ModularCurve_exists_mul_coeffMap_eq_iff_of_algEquiv_apply_jq_eq_jqN_of_not_dvd
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_exists_not_dvd_and_forall_isIntegral_mul_qExpansion_alSlash_of_isIntegralQExp_of_even
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.coe_heckeAlphaHBar ModularCurve.coe_heckeBetaHBarOf AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.ProjectiveLine.map_mk"

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

open scoped Classical MatrixGroups ModularForm Pointwise
open UpperHalfPlane CongruenceSubgroup ModularCurve

namespace ALCofactorPIntegrality

section Algebra

variable {K : Type*} [Field K] (A : ValuationSubring K)

theorem valuation_natCast_eq_one_of_coprime {p m : ℕ} (hp : (p : K) ∈ A.nonunits)
    (hm : m.Coprime p) : A.valuation (m : K) = 1 := by
  have hmA : (m : K) ∈ A := natCast_mem A m
  have hle : A.valuation (m : K) ≤ 1 := (A.valuation_le_one_iff _).mpr hmA
  rcases hle.lt_or_eq with hlt | h
  · exfalso
    obtain ⟨u, w, huw⟩ := Nat.isCoprime_iff_coprime.mpr hm
    have h1 : (1 : K) = (u : K) * m + (w : K) * p := by
      have h := congrArg (Int.cast : ℤ → K) huw
      push_cast at h
      exact h.symm
    have hu : A.valuation ((u : K) * m) < 1 := by
      rw [map_mul]
      calc A.valuation (u : K) * A.valuation (m : K)
          ≤ 1 * A.valuation (m : K) :=
            mul_le_mul' ((A.valuation_le_one_iff _).mpr (intCast_mem A u)) le_rfl
        _ < 1 := by rw [one_mul]; exact hlt
    have hw : A.valuation ((w : K) * p) < 1 := by
      rw [map_mul]
      calc A.valuation (w : K) * A.valuation (p : K)
          ≤ 1 * A.valuation (p : K) :=
            mul_le_mul' ((A.valuation_le_one_iff _).mpr (intCast_mem A w)) le_rfl
        _ < 1 := by rw [one_mul]; exact A.mem_nonunits_iff.mp hp
    have := Valuation.map_add_lt A.valuation hu hw
    rw [← h1, map_one] at this
    exact lt_irrefl _ this
  · exact h

theorem exists_valuation_natCast_eq_pow {p : ℕ} (hpp : p.Prime) (hp : (p : K) ∈ A.nonunits)
    {n : ℕ} (hn : n ≠ 0) : ∃ e : ℕ, A.valuation (n : K) = A.valuation (p : K) ^ e := by
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hpp.ne_one
  refine ⟨e, ?_⟩
  have hcop : m.Coprime p := (Nat.Prime.coprime_iff_not_dvd hpp).mpr hm |>.symm
  push_cast
  rw [map_mul, map_pow, valuation_natCast_eq_one_of_coprime A hp hcop, mul_one]

theorem exists_valuation_ratCast_eq_zpow [CharZero K] {p : ℕ} (hpp : p.Prime)
    (hp : (p : K) ∈ A.nonunits) {r : ℚ} (hr : r ≠ 0) :
    ∃ e : ℤ, A.valuation (r : K) = A.valuation (p : K) ^ e := by
  have hnum : r.num.natAbs ≠ 0 := by
    rw [ne_eq, Int.natAbs_eq_zero]; exact Rat.num_ne_zero.mpr hr
  obtain ⟨e₁, he₁⟩ := exists_valuation_natCast_eq_pow A hpp hp hnum
  obtain ⟨e₂, he₂⟩ := exists_valuation_natCast_eq_pow A hpp hp r.den_nz
  refine ⟨(e₁ : ℤ) - e₂, ?_⟩
  have hvp : A.valuation (p : K) ≠ 0 := by
    rw [ne_eq, Valuation.zero_iff]; exact_mod_cast hpp.ne_zero
  have hr' : (r : K) = (r.num : K) / (r.den : K) := by
    rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  have hnumv : A.valuation (r.num : K) = A.valuation (p : K) ^ e₁ := by
    rw [← he₁]
    rcases Int.natAbs_eq r.num with h | h
    · conv_lhs => rw [h]; rw [Int.cast_natCast]
    · conv_lhs => rw [h]; rw [Int.cast_neg, Int.cast_natCast, Valuation.map_neg]
  rw [hr', map_div₀, hnumv, he₂, zpow_sub₀ hvp, zpow_natCast, zpow_natCast, div_eq_mul_inv]

theorem exists_valuation_pow_factorial_eq_zpow [CharZero K] {p : ℕ} (hpp : p.Prime)
    (hp : (p : K) ∈ A.nonunits) (L : IntermediateField ℚ K) [FiniteDimensional ℚ L]
    {x : K} (hxL : x ∈ L) (hx : x ≠ 0) :
    ∃ e : ℤ, A.valuation x ^ (Module.finrank ℚ L).factorial = A.valuation (p : K) ^ e := by
  set v := A.valuation with hv
  set xL : L := ⟨x, hxL⟩ with hxLdef
  have hxL0 : xL ≠ 0 := fun h => hx (by rw [hxLdef] at h; exact congrArg Subtype.val h)
  have hint : IsIntegral ℚ xL := IsIntegral.of_finite ℚ xL
  set P : Polynomial ℚ := minpoly ℚ xL with hP
  have hdeg : P.natDegree ≤ Module.finrank ℚ L := minpoly.natDegree_le xL
  have hdegpos : 0 < P.natDegree := minpoly.natDegree_pos hint
  have hmonic : P.Monic := minpoly.monic hint
  have h0 : P.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hxL0

  have haeval : (Polynomial.aeval x) P = 0 := by
    have h1 : (Polynomial.aeval xL) P = 0 := minpoly.aeval ℚ xL
    have h2 : (Polynomial.aeval (algebraMap L K xL)) P = algebraMap L K ((Polynomial.aeval xL) P) :=
      Polynomial.aeval_algebraMap_apply K xL P
    rw [h1, map_zero] at h2
    exact h2
  rw [Polynomial.aeval_eq_sum_range] at haeval

  set S : Finset ℕ := (Finset.range (P.natDegree + 1)).filter fun i => P.coeff i ≠ 0 with hS
  set g : ℕ → K := fun i => P.coeff i • x ^ i with hg
  have hsumS : ∑ i ∈ S, g i = 0 := by
    rw [hS, Finset.sum_filter_of_ne]
    · exact haeval
    · intro i _ hne hci
      apply hne
      simp only [hg, hci, zero_smul]
  have hvp : v (p : K) ≠ 0 := by
    rw [ne_eq, Valuation.zero_iff]; exact_mod_cast hpp.ne_zero
  have hvx : v x ≠ 0 := by rwa [ne_eq, Valuation.zero_iff]

  have hterm : ∀ i ∈ S, ∃ e : ℤ, v (g i) = v (p : K) ^ e * v x ^ i := by
    intro i hi
    have hci : P.coeff i ≠ 0 := (Finset.mem_filter.mp hi).2
    obtain ⟨e, he⟩ := exists_valuation_ratCast_eq_zpow A hpp hp hci
    refine ⟨e, ?_⟩
    simp only [hg, Algebra.smul_def, map_mul, map_pow]
    rw [eq_ratCast (algebraMap ℚ K) (P.coeff i), he]
  have hgne : ∀ i ∈ S, v (g i) ≠ 0 := by
    intro i hi
    obtain ⟨e, he⟩ := hterm i hi
    rw [he]
    exact mul_ne_zero (zpow_ne_zero _ hvp) (pow_ne_zero _ hvx)
  have h0S : 0 ∈ S := by
    rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_range.mpr (Nat.succ_pos _), h0⟩

  have hpair : ∃ i ∈ S, ∃ j ∈ S, i < j ∧ v (g i) = v (g j) := by
    by_contra hcon
    push Not at hcon

    obtain ⟨j, hjS, hjmax⟩ := Finset.exists_max_image S (fun i => v (g i)) ⟨0, h0S⟩
    have hlt : ∀ i ∈ S \ {j}, v (g i) < v (g j) := by
      intro i hi
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
      rcases lt_or_gt_of_ne hi.2 with hij | hij
      · exact lt_of_le_of_ne (hjmax i hi.1) (hcon i hi.1 j hjS hij)
      · exact lt_of_le_of_ne (hjmax i hi.1) (fun h => hcon j hjS i hi.1 hij h.symm)
    have := Valuation.map_sum_eq_of_lt v hjS hlt
    rw [hsumS, map_zero] at this
    exact hgne j hjS this.symm
  obtain ⟨i, hi, j, hj, hij, hvij⟩ := hpair
  obtain ⟨eᵢ, heᵢ⟩ := hterm i hi
  obtain ⟨eⱼ, heⱼ⟩ := hterm j hj

  have hd : v x ^ (j - i) = v (p : K) ^ (eᵢ - eⱼ) := by
    have h1 : v (p : K) ^ eᵢ * v x ^ i = (v (p : K) ^ eⱼ * v x ^ (j - i)) * v x ^ i := by
      rw [mul_assoc, mul_comm (v x ^ (j - i)), ← pow_add, Nat.add_sub_cancel' hij.le, ← heᵢ, ← heⱼ,
        hvij]
    have h2 : v x ^ i ≠ 0 := pow_ne_zero _ hvx
    have h3 := mul_right_cancel₀ h2 h1
    rw [zpow_sub₀ hvp, eq_div_iff (zpow_ne_zero _ hvp), h3, mul_comm]

  have hjdeg : j ≤ P.natDegree := by
    have := (Finset.mem_filter.mp hj).1
    rw [Finset.mem_range] at this
    omega
  have hdvd : (j - i) ∣ (Module.finrank ℚ L).factorial :=
    Nat.dvd_factorial (Nat.sub_pos_of_lt hij) (le_trans (Nat.sub_le j i) (hjdeg.trans hdeg))
  obtain ⟨c, hc⟩ := hdvd
  refine ⟨(eᵢ - eⱼ) * c, ?_⟩
  rw [hc, pow_mul, hd, ← zpow_natCast, ← zpow_mul]

theorem exists_forall_valuation_le [CharZero K] {p : ℕ} (hpp : p.Prime)
    (hp : (p : K) ∈ A.nonunits) (L : IntermediateField ℚ K) [FiniteDimensional ℚ L]
    (t : ℕ → K) (htL : ∀ n, t n ∈ L) {B : ℕ} (hB : B ≠ 0) (hbd : ∀ n, (B : K) * t n ∈ A) :
    ∃ n₀ : ℕ, ∀ n, A.valuation (t n) ≤ A.valuation (t n₀) := by
  set v := A.valuation with hv
  by_cases hall : ∀ n, t n = 0
  · exact ⟨0, fun n => by rw [hall n, map_zero]; exact zero_le'⟩
  push Not at hall
  set N := (Module.finrank ℚ L).factorial with hN
  have hNpos : 0 < N := Nat.factorial_pos _
  have hvp : v (p : K) ≠ 0 := by
    rw [ne_eq, Valuation.zero_iff]; exact_mod_cast hpp.ne_zero
  have hvp0 : 0 < v (p : K) := zero_lt_iff.mpr hvp
  have hvp1 : v (p : K) < 1 := A.mem_nonunits_iff.mp hp

  have hex : ∀ n, t n ≠ 0 → ∃ e : ℤ, v (t n) ^ N = v (p : K) ^ e := fun n hn =>
    exists_valuation_pow_factorial_eq_zpow A hpp hp L (htL n) hn
  choose! ex hex' using hex

  obtain ⟨b, hb⟩ := exists_valuation_natCast_eq_pow A hpp hp hB
  have hlow : ∀ n, t n ≠ 0 → -((N : ℤ) * b) ≤ ex n := by
    intro n hn
    have h1 : v ((B : K) * t n) ≤ 1 := (A.valuation_le_one_iff _).mpr (hbd n)
    rw [map_mul, hb] at h1

    have h2 : v (t n) ≤ (v (p : K) ^ b)⁻¹ := by
      rw [← mul_le_mul_iff_of_pos_left (pow_pos hvp0 b), mul_inv_cancel₀ (pow_ne_zero _ hvp)]
      exact h1
    have h3 : v (t n) ^ N ≤ ((v (p : K) ^ b)⁻¹) ^ N := pow_le_pow_left₀ zero_le' h2 N
    rw [hex' n hn, ← zpow_natCast (v (p : K)) b, ← zpow_neg, ← zpow_natCast, ← zpow_mul] at h3
    rw [zpow_le_zpow_iff_right_of_lt_one₀ hvp0 hvp1] at h3
    linarith

  obtain ⟨n₁, hn₁⟩ := hall
  have hPex : ∃ m : ℕ, ∃ n, t n ≠ 0 ∧ (ex n + (N : ℤ) * b).toNat = m := ⟨_, n₁, hn₁, rfl⟩
  set m₀ := Nat.find hPex with hm₀
  obtain ⟨n₀, hn₀, hm₀eq⟩ := Nat.find_spec hPex
  refine ⟨n₀, fun n => ?_⟩
  by_cases hn : t n = 0
  · rw [hn, map_zero]; exact zero_le'
  have hmin : m₀ ≤ (ex n + (N : ℤ) * b).toNat := Nat.find_min' hPex ⟨n, hn, rfl⟩
  have hle : ex n₀ ≤ ex n := by
    have h1 := hlow n hn
    have h2 := hlow n₀ hn₀
    have h3 : ((ex n₀ + (N : ℤ) * b).toNat : ℤ) ≤ ((ex n + (N : ℤ) * b).toNat : ℤ) := by
      rw [hm₀eq]; exact_mod_cast hmin
    rw [Int.toNat_of_nonneg (by linarith), Int.toNat_of_nonneg (by linarith)] at h3
    linarith

  have hpow : v (t n) ^ N ≤ v (t n₀) ^ N := by
    rw [hex' n hn, hex' n₀ hn₀]
    exact (zpow_le_zpow_iff_right_of_lt_one₀ hvp0 hvp1).mpr hle
  exact (pow_le_pow_iff_left₀ zero_le' zero_le' hNpos.ne').mp hpow

theorem forall_coeff_mem_of_mul_eq (t : PowerSeries K) (Y X : PowerSeries A)
    (hY : ∃ j, IsUnit (PowerSeries.coeff j Y))
    (hXY : t * Y.map A.subtype = X.map A.subtype)
    (hatt : ∃ n₀, ∀ n, A.valuation (PowerSeries.coeff n t) ≤ A.valuation (PowerSeries.coeff n₀ t)) :
    ∀ n, PowerSeries.coeff n t ∈ A := by
  set v := A.valuation with hv
  obtain ⟨n₀, hn₀⟩ := hatt
  by_cases hc1 : v (PowerSeries.coeff n₀ t) ≤ 1
  · exact fun n => (A.valuation_le_one_iff _).mp ((hn₀ n).trans hc1)
  exfalso
  push Not at hc1
  set c := v (PowerSeries.coeff n₀ t) with hc
  have hc0 : c ≠ 0 := ne_of_gt (lt_trans zero_lt_one hc1)

  have hPn : ∃ n, v (PowerSeries.coeff n t) = c := ⟨n₀, rfl⟩
  set n₁ := Nat.find hPn with hn₁
  have hn₁c : v (PowerSeries.coeff n₁ t) = c := Nat.find_spec hPn
  have hbefore : ∀ i, i < n₁ → v (PowerSeries.coeff i t) < c := fun i hi =>
    lt_of_le_of_ne (hn₀ i) (Nat.find_min hPn hi)

  set j₀ := Nat.find hY with hj₀
  have hj₀u : IsUnit (PowerSeries.coeff j₀ Y) := Nat.find_spec hY
  have hYbefore : ∀ j, j < j₀ → v ((PowerSeries.coeff j Y : A) : K) < 1 := by
    intro j hj
    have hnu : ¬ IsUnit (PowerSeries.coeff j Y) := Nat.find_min hY hj
    exact (A.valuation_lt_one_iff _).mp ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
  have hYle : ∀ j, v ((PowerSeries.coeff j Y : A) : K) ≤ 1 := fun j => A.valuation_le_one _
  have hYj₀ : v ((PowerSeries.coeff j₀ Y : A) : K) = 1 := by
    obtain ⟨u, hu⟩ := hj₀u
    rw [← hu]; exact A.valuation_unit u

  have hcoeff := congrArg (PowerSeries.coeff (n₁ + j₀)) hXY
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_map] at hcoeff
  simp only [PowerSeries.coeff_map] at hcoeff

  have hmem : (n₁, j₀) ∈ Finset.HasAntidiagonal.antidiagonal (n₁ + j₀) := Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl
  have hmain : v (PowerSeries.coeff n₁ t * A.subtype (PowerSeries.coeff j₀ Y)) = c := by
    rw [map_mul, hn₁c, ValuationSubring.subtype_apply, hYj₀, mul_one]
  have hothers : ∀ ij ∈ Finset.HasAntidiagonal.antidiagonal (n₁ + j₀) \ {(n₁, j₀)},
      v (PowerSeries.coeff ij.1 t * A.subtype (PowerSeries.coeff ij.2 Y)) <
        v (PowerSeries.coeff n₁ t * A.subtype (PowerSeries.coeff j₀ Y)) := by
    intro ij hij
    rw [Finset.mem_sdiff, Finset.mem_singleton, Finset.HasAntidiagonal.mem_antidiagonal] at hij
    obtain ⟨hsum, hne⟩ := hij
    rw [hmain, map_mul, ValuationSubring.subtype_apply]
    rcases lt_trichotomy ij.1 n₁ with hlt | heq | hgt
    · calc v (PowerSeries.coeff ij.1 t) * v ((PowerSeries.coeff ij.2 Y : A) : K)
          ≤ v (PowerSeries.coeff ij.1 t) * 1 := mul_le_mul' le_rfl (hYle _)
        _ < c := by rw [mul_one]; exact hbefore _ hlt
    · exfalso; apply hne
      have : ij.2 = j₀ := by omega
      exact Prod.ext heq this
    · have hj : ij.2 < j₀ := by omega
      have h1 : v ((PowerSeries.coeff ij.2 Y : A) : K) < 1 := hYbefore _ hj
      rcases eq_or_ne (v (PowerSeries.coeff ij.1 t)) 0 with h0 | h0
      · rw [h0, zero_mul]; exact zero_lt_iff.mpr hc0
      · calc v (PowerSeries.coeff ij.1 t) * v ((PowerSeries.coeff ij.2 Y : A) : K)
            < v (PowerSeries.coeff ij.1 t) * 1 := by
              rw [mul_comm, mul_comm _ (1 : A.ValueGroup)]
              exact mul_lt_mul_of_pos_right h1 (zero_lt_iff.mpr h0)
          _ ≤ c := by rw [mul_one]; exact hn₀ _
  have hval := Valuation.map_sum_eq_of_lt v hmem hothers
  rw [hmain, hcoeff, ValuationSubring.subtype_apply] at hval
  have : v ((PowerSeries.coeff (n₁ + j₀) X : A) : K) ≤ 1 := A.valuation_le_one _
  rw [hval] at this
  exact absurd hc1 (not_lt.mpr this)

theorem isIntegral_of_pow_mul_of_forall_valuationSubring [CharZero K] {p : ℕ} (hpp : p.Prime) (z : K) (a : ℕ)
    (hz : IsIntegral ℤ ((p : K) ^ a * z))
    (hloc : ∀ B : ValuationSubring K, (p : K) ∈ B.nonunits → z ∈ B) : IsIntegral ℤ z := by
  by_contra hnot
  have hzR : z ∉ (integralClosure ℤ K).toSubring := fun h => hnot (mem_integralClosure_iff ℤ K |>.mp h)
  obtain ⟨V, hRV, hzV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hzR
  apply hzV
  by_cases hpV : (p : K) ∈ V.nonunits
  · exact hloc V hpV
  ·
    have hp1 : V.valuation (p : K) = 1 := by
      have hle : V.valuation (p : K) ≤ 1 := (V.valuation_le_one_iff _).mpr (natCast_mem V p)
      rcases hle.lt_or_eq with h | h
      · exact absurd (V.mem_nonunits_iff.mpr h) hpV
      · exact h
    have hpa : (p : K) ^ a ≠ 0 := pow_ne_zero _ (by exact_mod_cast hpp.ne_zero)
    have hmem : (p : K) ^ a * z ∈ V := hRV ((mem_integralClosure_iff ℤ K).mpr hz)
    have hval : V.valuation z ≤ 1 := by
      have h1 : V.valuation ((p : K) ^ a * z) ≤ 1 := (V.valuation_le_one_iff _).mpr hmem
      rwa [map_mul, map_pow, hp1, one_pow, one_mul] at h1
    exact (V.valuation_le_one_iff _).mp hval

end Algebra

section Normalizer

abbrev ΓGL (Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ) :=
  ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem one_mem_strictPeriods_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) :
    (1 : ℝ) ∈ (ΓGL (CohCarrier.GammaH M H)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH M H)]
  exact AddSubgroup.mem_zmultiples _

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

def conjMat (Q p x y z w c : ℤ) (δ : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![Q * x * w * δ 0 0 + w * y * (Q * p) * c - (Q * p) * x * z * δ 0 1 - p * y * z * δ 1 1,
     -x * y * δ 0 0 - p * y ^ 2 * c + Q * x ^ 2 * δ 0 1 + x * y * δ 1 1;
     (Q * p) * (z * w * δ 0 0 - p * z ^ 2 * δ 0 1 - z * w * δ 1 1 + Q * w ^ 2 * c),
     -p * y * z * δ 0 0 - w * y * (Q * p) * c + (Q * p) * x * z * δ 0 1 + Q * x * w * δ 1 1]

theorem det_conjMat (Q p x y z w c : ℤ) (δ : Matrix (Fin 2) (Fin 2) ℤ) (hrel : Q * x * w - p * y * z = 1)
    (h10 : δ 1 0 = Q * p * c) (hdet : δ 0 0 * δ 1 1 - δ 0 1 * δ 1 0 = 1) :
    (conjMat Q p x y z w c δ).det = 1 := by
  rw [h10] at hdet
  rw [conjMat, Matrix.det_fin_two_of]
  linear_combination (-Q ^ 2 * c * p * w * x * δ 0 1 + Q * c * p ^ 2 * y * z * δ 0 1 - Q * c * p * δ 0 1 +
    Q * w * x * δ 0 0 * δ 1 1 - p * y * z * δ 0 0 * δ 1 1 + δ 0 0 * δ 1 1) * hrel + hdet

def conjSL (Q p x y z w : ℤ) (hrel : Q * x * w - p * y * z = 1) (δ : SL(2, ℤ)) (c : ℤ)
    (h10 : (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = Q * p * c) : SL(2, ℤ) :=
  ⟨conjMat Q p x y z w c δ, det_conjMat Q p x y z w c δ hrel h10 (by
    have := δ.prop; rwa [Matrix.det_fin_two] at this)⟩

@[scoped simp]
theorem coe_conjSL (Q p x y z w : ℤ) (hrel : Q * x * w - p * y * z = 1) (δ : SL(2, ℤ)) (c : ℤ)
    (h10 : (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = Q * p * c) :
    ((conjSL Q p x y z w hrel δ c h10 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = conjMat Q p x y z w c δ :=
  rfl

theorem mul_mapGL_eq (Q p x y z w : ℤ) (hrel : Q * x * w - p * y * z = 1) (δ : SL(2, ℤ)) (c : ℤ)
    (h10 : (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = Q * p * c)
    (A : GL (Fin 2) ℝ)
    (hA : (A : Matrix (Fin 2) (Fin 2) ℝ) = !![(Q : ℝ) * x, (y : ℝ); (Q : ℝ) * p * z, (Q : ℝ) * w]) :
    A * Matrix.SpecialLinearGroup.mapGL ℝ δ =
      Matrix.SpecialLinearGroup.mapGL ℝ (conjSL Q p x y z w hrel δ c h10) * A := by
  have hrelR : (Q : ℝ) * x * w - p * y * z = 1 := by exact_mod_cast hrel
  ext i j
  rw [Units.val_mul, Units.val_mul]
  have e00 : ((Matrix.SpecialLinearGroup.mapGL ℝ δ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      ((δ : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.cast : ℤ → ℝ) := rfl
  have e01 : ((Matrix.SpecialLinearGroup.mapGL ℝ (conjSL Q p x y z w hrel δ c h10) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = (conjMat Q p x y z w c δ).map (Int.cast : ℤ → ℝ) := rfl
  rw [e00, e01, hA]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, conjMat, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Fin.isValue, Fin.zero_eta, Fin.mk_one, h10] <;> push_cast
  · linear_combination (-(Q : ℝ) * c * p * y - Q * x * (((δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ℝ)) * hrelR
  · linear_combination (-(Q : ℝ) * x * (((δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ℝ) -
      y * (((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℝ)) * hrelR
  · linear_combination (-(Q : ℝ) ^ 2 * c * p * w - Q * p * z * (((δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ℝ)) * hrelR
  · linear_combination (-(Q : ℝ) * p * z * (((δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ℝ) -
      Q * w * (((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℝ)) * hrelR

theorem conjSL_mem (p : ℕ) [Fact p.Prime] (hpM : p ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (x y z w : ℤ) (hrel : ((M / p : ℕ) : ℤ) * x * w - (p : ℤ) * y * z = 1)
    (δ : SL(2, ℤ)) (hδ : δ ∈ CohCarrier.GammaH M H) (c : ℤ)
    (h10 : (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = ((M / p : ℕ) : ℤ) * (p : ℤ) * c) :
    conjSL ((M / p : ℕ) : ℤ) (p : ℤ) x y z w hrel δ c h10 ∈ CohCarrier.GammaH M H := by
  set Q : ℕ := M / p with hQ
  have hQp : Q * p = M := Nat.div_mul_cancel hpM
  obtain ⟨hδ0, hδH⟩ := CohCarrier.mem_GammaH_iff.mp hδ
  have hdet : (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * ((Q : ℤ) * (p : ℤ) * c) = 1 := by
    have := δ.prop; rw [Matrix.det_fin_two] at this; rwa [h10] at this

  have h0' : conjSL (Q : ℤ) (p : ℤ) x y z w hrel δ c h10 ∈ Gamma0 M := by
    rw [Gamma0_mem, coe_conjSL]
    simp only [conjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    have hM : ((Q : ℤ) * (p : ℤ) : ZMod M) = 0 := by
      have : ((Q : ℤ) * (p : ℤ) : ℤ) = (M : ℤ) := by exact_mod_cast hQp
      rw [show ((Q : ℤ) * (p : ℤ) : ZMod M) = (((Q : ℤ) * (p : ℤ) : ℤ) : ZMod M) by push_cast; rfl, this]
      simp
    push_cast
    rw [show ((Q : ZMod M) * (p : ZMod M)) = ((Q : ℤ) * (p : ℤ) : ZMod M) by push_cast; rfl, hM, zero_mul]
  refine CohCarrier.mem_GammaH_iff.mpr ⟨h0', ?_⟩

  set u' : (ZMod M)ˣ := CohCarrier.gamma0Units M ⟨_, h0'⟩ with hu'
  set u : (ZMod M)ˣ := CohCarrier.gamma0Units M ⟨δ, hδ0⟩ with hu
  have hprod : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) (u' * u) = 1 := by
    apply Units.ext
    rw [map_mul, Units.val_mul, Units.val_one, ZMod.unitsMap_def, Units.coe_map, Units.coe_map]
    change ZMod.castHom (Nat.div_dvd_of_dvd hpM) (ZMod Q) (u' : ZMod M) *
      ZMod.castHom (Nat.div_dvd_of_dvd hpM) (ZMod Q) (u : ZMod M) = 1
    have hu'v : (u' : ZMod M) =
        (((conjMat (Q : ℤ) (p : ℤ) x y z w c δ) 1 1 : ℤ) : ZMod M) := rfl
    have huv : (u : ZMod M) = (((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod M) := rfl
    rw [hu'v, huv, map_intCast, map_intCast, ← Int.cast_mul]

    have hkey : (Q : ℤ) ∣ (conjMat (Q : ℤ) (p : ℤ) x y z w c δ) 1 1 * (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 - 1 := by
      refine ⟨((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 ^ 2 - 1) * x * w -
        (p : ℤ) ^ 2 * y * z * (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * c +
        (p : ℤ) * x * z * (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
        (p : ℤ) * w * y * c * (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1, ?_⟩
      simp only [conjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      linear_combination (-(p : ℤ) * y * z) * hdet + hrel
    obtain ⟨U, hU⟩ := hkey
    have : (conjMat (Q : ℤ) (p : ℤ) x y z w c δ) 1 1 * (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = (Q : ℤ) * U + 1 := by
      linear_combination hU
    rw [this]
    push_cast
    rw [ZMod.natCast_self, zero_mul, zero_add]
  have hmem : u' * u ∈ H := hHp _ hprod
  have : u' = u' * u * u⁻¹ := by group
  rw [this]
  exact H.mul_mem hmem (H.inv_mem hδH)

theorem le_conj_alGL (p : ℕ) [Fact p.Prime] (hpM : p ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (x y z w : ℤ) (hrel : ((M / p : ℕ) : ℤ) * x * w - (p : ℤ) * y * z = 1)
    (A : GL (Fin 2) ℝ)
    (hA : (A : Matrix (Fin 2) (Fin 2) ℝ) =
      !![((M / p : ℕ) : ℝ) * (x : ℝ), (y : ℝ); (M : ℝ) * (z : ℝ), ((M / p : ℕ) : ℝ) * (w : ℝ)]) :
    ΓGL (CohCarrier.GammaH M H) ≤ ConjAct.toConjAct A⁻¹ • ΓGL (CohCarrier.GammaH M H) := by
  set Q : ℕ := M / p with hQ
  have hQp : Q * p = M := Nat.div_mul_cancel hpM
  rintro g ⟨δ, hδ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  obtain ⟨hδ0, _⟩ := CohCarrier.mem_GammaH_iff.mp hδ
  have hdiv : (M : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    have h := Gamma0_mem.mp hδ0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
  obtain ⟨c, hc⟩ := hdiv
  have h10 : (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = ((Q : ℕ) : ℤ) * (p : ℤ) * c := by
    rw [hc]; congr 1; exact_mod_cast hQp.symm
  have hA' : (A : Matrix (Fin 2) (Fin 2) ℝ) =
      !![((Q : ℤ) : ℝ) * x, (y : ℝ); ((Q : ℤ) : ℝ) * (p : ℤ) * z, ((Q : ℤ) : ℝ) * w] := by
    rw [hA]
    have : (M : ℝ) = (Q : ℝ) * (p : ℝ) := by exact_mod_cast hQp.symm
    rw [this]; push_cast; rfl
  refine ⟨conjSL (Q : ℤ) (p : ℤ) x y z w hrel δ c h10, conjSL_mem p hpM hHp x y z w hrel δ hδ c h10, ?_⟩
  have hmul := mul_mapGL_eq (Q : ℤ) (p : ℤ) x y z w hrel δ c h10 A hA'
  rw [Matrix.SpecialLinearGroup.mapGL] at hmul ⊢
  simp only [MonoidHom.coe_comp, Function.comp_apply] at hmul ⊢
  rw [eq_mul_inv_iff_mul_eq]
  exact hmul.symm

def alForm (p : ℕ) [Fact p.Prime] (hpM : p ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (x y z w : ℤ) (hrel : ((M / p : ℕ) : ℤ) * x * w - (p : ℤ) * y * z = 1)
    (A : GL (Fin 2) ℝ)
    (hA : (A : Matrix (Fin 2) (Fin 2) ℝ) =
      !![((M / p : ℕ) : ℝ) * (x : ℝ), (y : ℝ); (M : ℝ) * (z : ℝ), ((M / p : ℕ) : ℝ) * (w : ℝ)])
    {k : ℤ} (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    ModularForm (ΓGL (CohCarrier.GammaH M H)) k :=
  restrictForm (le_conj_alGL p hpM hHp x y z w hrel A hA) (ModularForm.translate f A)

@[scoped simp]
theorem coe_alForm (p : ℕ) [Fact p.Prime] (hpM : p ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (x y z w : ℤ) (hrel : ((M / p : ℕ) : ℤ) * x * w - (p : ℤ) * y * z = 1)
    (A : GL (Fin 2) ℝ)
    (hA : (A : Matrix (Fin 2) (Fin 2) ℝ) =
      !![((M / p : ℕ) : ℝ) * (x : ℝ), (y : ℝ); (M : ℝ) * (z : ℝ), ((M / p : ℕ) : ℝ) * (w : ℝ)])
    {k : ℤ} (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    ⇑(alForm p hpM hHp x y z w hrel A hA f) = ⇑f ∣[k] A := rfl

end Normalizer

section Datum

variable {M : ℕ} [NeZero M] (p : ℕ) [Fact p.Prime] (hpM : p ∣ M)
  (W : ModularForm.AtkinLehnerDatum M (M / p))

include hpM in
theorem neZero_div : NeZero (M / p) :=
  ⟨(Nat.div_ne_zero_iff_of_dvd hpM).mpr ⟨NeZero.ne M, (Fact.out : p.Prime).ne_zero⟩⟩

include hpM in

theorem datum_R : W.R = p := by
  have h1 : M = M / p * W.R := W.hM
  have h2 : M / p * p = M := Nat.div_mul_cancel hpM
  have hQ : M / p ≠ 0 := (neZero_div p hpM).ne
  have : M / p * W.R = M / p * p := by rw [← h1, h2]
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hQ) this

include hpM in
theorem datum_rel : ((M / p : ℕ) : ℤ) * W.a * 1 - (p : ℤ) * W.b * 1 = 1 := by
  have h := W.bezout
  rw [datum_R p hpM W] at h
  linear_combination h

include hpM in
theorem datum_alGL_coe : (W.alGL : Matrix (Fin 2) (Fin 2) ℝ) =
    !![((M / p : ℕ) : ℝ) * ((W.a : ℤ) : ℝ), ((W.b : ℤ) : ℝ);
      (M : ℝ) * ((1 : ℤ) : ℝ), ((M / p : ℕ) : ℝ) * ((1 : ℤ) : ℝ)] := by
  rw [ModularForm.AtkinLehnerDatum.alGL_coe, ModularForm.AtkinLehnerDatum.mat]
  have hR := datum_R p hpM W
  have hM : ((M / p : ℕ) : ℝ) * (p : ℝ) = (M : ℝ) := by exact_mod_cast Nat.div_mul_cancel hpM
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.isValue, Fin.zero_eta, Fin.mk_one, eq_intCast,
      Int.cast_mul, Int.cast_natCast, Int.cast_one, mul_one, hR, hM]

include W hpM in

theorem not_dvd_div : ¬ p ∣ M / p := by
  intro h
  have hb := W.bezout
  rw [datum_R p hpM W] at hb
  obtain ⟨c, hc⟩ := h
  have hQ : ((M / p : ℕ) : ℤ) = (p : ℤ) * c := by exact_mod_cast hc
  rw [hQ] at hb
  have : (p : ℤ) ∣ 1 := ⟨(c : ℤ) * W.a - W.b, by linear_combination -hb⟩
  have hp1 : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos this
  have := (Fact.out : p.Prime).two_le
  omega

def alSLPart {Q : ℕ} (W : ModularForm.AtkinLehnerDatum M Q) : SL(2, ℤ) :=
  ⟨!![W.a, W.b; (W.R : ℤ), (Q : ℤ)], by
    rw [Matrix.det_fin_two_of]; linear_combination W.bezout⟩

theorem alGL_eq_mapGL_mul_heckeDiag {Q : ℕ} [NeZero Q] (W : ModularForm.AtkinLehnerDatum M Q) :
    W.alGL = Matrix.SpecialLinearGroup.mapGL ℝ (alSLPart W) * ModularForm.heckeDiagMatrix Q := by
  ext i j
  rw [Units.val_mul, ModularForm.AtkinLehnerDatum.alGL_coe, ModularForm.AtkinLehnerDatum.mat,
    ModularForm.val_heckeDiagMatrix (NeZero.ne Q)]
  have e00 : ((Matrix.SpecialLinearGroup.mapGL ℝ (alSLPart W) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (((alSLPart W : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.cast : ℤ → ℝ) := rfl
  rw [e00]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, alSLPart, mul_comm]

theorem levelOne_slash_alGL {Q : ℕ} [NeZero Q] (W : ModularForm.AtkinLehnerDatum M Q) {k : ℤ}
    (F : ModularForm 𝒮ℒ k) :
    (F : ℍ → ℂ) ∣[k] W.alGL = fun τ => (Q : ℂ) ^ (k - 1) * F (ModularForm.heckeDiagMatrix Q • τ) := by
  rw [alGL_eq_mapGL_mul_heckeDiag, SlashAction.slash_mul,
    SlashInvariantForm.slash_action_eqn F _ (MonoidHom.mem_range.mpr ⟨alSLPart W, rfl⟩)]
  funext τ
  exact ModularForm.slash_heckeDiagMatrix_apply k (NeZero.ne Q) F τ

variable {H : Subgroup (ZMod M)ˣ}

def resLevelOne (H : Subgroup (ZMod M)ˣ) {k : ℤ} (F : ModularForm 𝒮ℒ k) :
    ModularForm (ΓGL (CohCarrier.GammaH M H)) k :=
  restrictForm (Subgroup.map_le_range _ _) F

@[scoped simp]
theorem coe_resLevelOne (H : Subgroup (ZMod M)ˣ) {k : ℤ} (F : ModularForm 𝒮ℒ k) :
    ⇑(resLevelOne H F) = ⇑F := rfl

theorem qC_levelOne_slash_alGL [NeZero (M / p)]
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    {k : ℤ} (F : ModularForm 𝒮ℒ k) :
    HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 ((F : ℍ → ℂ) ∣[k] W.alGL)) =
      HahnSeries.C (((M / p : ℕ) : ℂ) ^ (k - 1)) *
        qExpand ℂ (M / p) (HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (F : ℍ → ℂ))) := by
  have hψ : ∃ ψ : ModularForm (ΓGL (CohCarrier.GammaH M H)) k, ⇑ψ = (F : ℍ → ℂ) ∣[k] W.alGL :=
    ⟨alForm p hpM hHp W.a W.b 1 1 (datum_rel p hpM W) W.alGL (datum_alGL_coe p hpM W) (resLevelOne H F),
      rfl⟩
  obtain ⟨ψ, hψcoe⟩ := hψ
  have hc : (((M / p : ℕ) : ℂ) ^ (k - 1)) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast NeZero.ne (M / p))
  have hslash : (F : ℍ → ℂ) ∣[k] W.alGL =
      (((M / p : ℕ) : ℂ) ^ (k - 1)) • fun τ => F (ModularForm.heckeDiagMatrix (M / p) • τ) := by
    rw [levelOne_slash_alGL]; rfl
  have hφψ : (fun τ => F (ModularForm.heckeDiagMatrix (M / p) • τ)) = (((M / p : ℕ) : ℂ) ^ (k - 1))⁻¹ • ⇑ψ := by
    rw [hψcoe, hslash, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have han : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 ⇑ψ) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero ψ one_pos (one_mem_strictPeriods_GammaH M H)
  have hqφ : qExpansion 1 (fun τ => F (ModularForm.heckeDiagMatrix (M / p) • τ)) =
      (((M / p : ℕ) : ℂ) ^ (k - 1))⁻¹ • qExpansion 1 ⇑ψ := by
    rw [hφψ]; exact qExpansion_smul han _
  have hqψ : qExpansion 1 ((F : ℍ → ℂ) ∣[k] W.alGL) =
      (((M / p : ℕ) : ℂ) ^ (k - 1)) • qExpansion 1 (fun τ => F (ModularForm.heckeDiagMatrix (M / p) • τ)) := by
    rw [← hψcoe, hqφ, smul_smul, mul_inv_cancel₀ hc, one_smul]
  rw [hqψ, ← ModularForm.qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne (M / p) F,
    PowerSeries.smul_eq_C_mul, map_mul, HahnSeries.ofPowerSeries_C]

end Datum

section Series

variable {R S : Type*} [CommRing R] [CommRing S]

theorem ofPowerSeries_coeff_of_neg (x : PowerSeries R) {n : ℤ} (hn : n < 0) :
    (HahnSeries.ofPowerSeries ℤ R x).coeff n = 0 := by
  rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range]
  intro h
  obtain ⟨m, hm⟩ := h
  have : (m : ℤ) = n := hm
  omega

theorem coeffMap_ofPowerSeries (φ : R →+* S) (x : PowerSeries R) :
    coeffMap φ (HahnSeries.ofPowerSeries ℤ R x) = HahnSeries.ofPowerSeries ℤ S (x.map φ) := by
  ext n
  simp only [coeffMap_coeff]
  by_cases hn : 0 ≤ n
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
  · push Not at hn
    rw [ofPowerSeries_coeff_of_neg x hn, ofPowerSeries_coeff_of_neg _ hn, map_zero]

theorem coeffMap_C (φ : R →+* S) (r : R) : coeffMap φ (HahnSeries.C r) = HahnSeries.C (φ r) := by
  rw [HahnSeries.C_apply, HahnSeries.C_apply, coeffMap_single]

def intSeriesR (R : Type*) [CommRing R] (p : PowerSeries ℤ) : LaurentSeries R :=
  HahnSeries.ofPowerSeries ℤ R (p.map (Int.castRingHom R))

theorem intSeriesR_eq_intSeriesC (K : Type*) [Field K] (p : PowerSeries ℤ) : intSeriesR K p = intSeriesC K p := rfl

theorem coeffMap_intSeriesR (φ : R →+* S) (p : PowerSeries ℤ) : coeffMap φ (intSeriesR R p) = intSeriesR S p := by
  rw [intSeriesR, coeffMap_ofPowerSeries, intSeriesR]
  congr 1
  ext n
  simp only [PowerSeries.coeff_map, eq_intCast, map_intCast]

theorem coeff_intSeriesR (p : PowerSeries ℤ) (n : ℕ) :
    (intSeriesR R p).coeff (n : ℤ) = ((PowerSeries.coeff n p : ℤ) : R) := by
  rw [intSeriesR, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, eq_intCast]

theorem intSeriesR_ne_zero_of_coeff [Nontrivial R] (p : PowerSeries ℤ) (n : ℕ) (h : PowerSeries.coeff n p = 1) :
    intSeriesR R p ≠ 0 := by
  intro h0
  have := congrArg (fun z : LaurentSeries R => z.coeff (n : ℤ)) h0
  simp only [coeff_intSeriesR, h, Int.cast_one, HahnSeries.coeff_zero] at this
  exact one_ne_zero this

end Series

section LaurentToPower

variable {K : Type*} [Field K] (A : ValuationSubring K)

theorem exists_powerSeries_datum (t : PowerSeries K) (Y X : LaurentSeries A)
    (hY : coeffMap (IsLocalRing.residue A) Y ≠ 0)
    (h : HahnSeries.ofPowerSeries ℤ K t * coeffMap A.subtype Y = coeffMap A.subtype X) :
    ∃ Yp Xp : PowerSeries A, (∃ j, IsUnit (PowerSeries.coeff j Yp)) ∧
      t * Yp.map A.subtype = Xp.map A.subtype := by
  set a := Y.order with ha
  set Yp := Y.powerSeriesPart with hYp
  have hYdec : HahnSeries.ofPowerSeries ℤ A Yp = HahnSeries.single (-a) 1 * Y :=
    LaurentSeries.ofPowerSeries_powerSeriesPart Y
  set Z : LaurentSeries A := HahnSeries.single (-a) 1 * X with hZ
  have hZ' : HahnSeries.ofPowerSeries ℤ K (t * Yp.map A.subtype) = coeffMap A.subtype Z := by
    have e1 : coeffMap A.subtype (HahnSeries.ofPowerSeries ℤ A Yp) =
        HahnSeries.single (-a) (1 : K) * coeffMap A.subtype Y := by
      rw [hYdec, map_mul, coeffMap_single, map_one]
    have e2 : coeffMap A.subtype Z = HahnSeries.single (-a) (1 : K) * coeffMap A.subtype X := by
      rw [hZ, map_mul, coeffMap_single, map_one]
    rw [map_mul, ← coeffMap_ofPowerSeries, e1, e2, ← mul_assoc,
      mul_comm (HahnSeries.ofPowerSeries ℤ K t), mul_assoc, h]
  refine ⟨Yp, PowerSeries.mk fun n => Z.coeff n, ?_, ?_⟩
  ·
    have : ∃ i, (coeffMap (IsLocalRing.residue A) Y).coeff i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hY (HahnSeries.ext (funext hcon))
    obtain ⟨i, hi⟩ := this
    rw [coeffMap_coeff] at hi
    have hci : Y.coeff i ≠ 0 := fun h0 => hi (by rw [h0, map_zero])
    have hai : a ≤ i := HahnSeries.order_le_of_coeff_ne_zero hci
    refine ⟨(i - a).toNat, ?_⟩
    have hidx : Y.order + ((i - a).toNat : ℤ) = i := by
      rw [← ha, Int.toNat_of_nonneg (sub_nonneg.mpr hai)]; ring
    rw [hYp, LaurentSeries.powerSeriesPart_coeff, hidx]
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hi
  · apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := K)
    rw [hZ']
    ext n
    simp only [coeffMap_coeff]
    by_cases hn : 0 ≤ n
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, PowerSeries.coeff_mk]
    · push Not at hn
      have h1 : (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map A.subtype (PowerSeries.mk fun n => Z.coeff ↑n))).coeff n = 0 :=
        ofPowerSeries_coeff_of_neg _ hn
      have h2 : (coeffMap A.subtype Z).coeff n = 0 := by
        rw [← hZ']; exact ofPowerSeries_coeff_of_neg _ hn
      rw [coeffMap_coeff] at h2
      rw [h1, h2]

end LaurentToPower

section Groups

variable {M : ℕ} [NeZero M] (p : ℕ) [Fact p.Prime] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)

theorem GammaH_eq_inf (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) :
    CohCarrier.GammaH M H = CohCarrier.GammaH (M / p) (infSubgroup p M H hpM) ⊓ Gamma0 (M / p * p) := by
  have hQp : M / p * p = M := Nat.div_mul_cancel hpM

  have h0 : ∀ A : SL(2, ℤ), A ∈ Gamma0 (M / p * p) ↔ A ∈ Gamma0 M := by
    intro A
    rw [Gamma0_mem, Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd, hQp]

  have hval : ∀ (A : SL(2, ℤ)) (hA : A ∈ Gamma0 M) (hA' : A ∈ Gamma0 (M / p)),
      ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) (CohCarrier.gamma0Units M ⟨A, hA⟩) =
        CohCarrier.gamma0Units (M / p) ⟨A, hA'⟩ := by
    intro A hA hA'
    apply Units.ext
    rw [ZMod.unitsMap_def, Units.coe_map]
    change ZMod.castHom (Nat.div_dvd_of_dvd hpM) (ZMod (M / p)) ((((A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod M)) =
      (((A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod (M / p))
    rw [map_intCast]
  have hle0 : ∀ A : SL(2, ℤ), A ∈ Gamma0 M → A ∈ Gamma0 (M / p) := by
    intro A hA
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hA ⊢
    exact dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.div_dvd_of_dvd hpM)) hA
  ext A
  rw [Subgroup.mem_inf, CohCarrier.mem_GammaH_iff, CohCarrier.mem_GammaH_iff, h0]
  constructor
  · rintro ⟨hA, hAH⟩
    refine ⟨⟨hle0 A hA, ?_⟩, hA⟩
    rw [mem_infSubgroup_iff]
    exact ⟨_, hAH, hval A hA (hle0 A hA)⟩
  · rintro ⟨⟨hA', hAH'⟩, hA⟩
    refine ⟨hA, ?_⟩
    rw [mem_infSubgroup_iff] at hAH'
    obtain ⟨d, hd, hdeq⟩ := hAH'
    have hker : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) (CohCarrier.gamma0Units M ⟨A, hA⟩ * d⁻¹) = 1 := by
      rw [map_mul, map_inv, hval A hA hA', ← hdeq, mul_inv_cancel]
    have := H.mul_mem (hHp _ hker) hd
    rwa [inv_mul_cancel_right] at this

theorem xHTopFunctionFieldC_eq (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) :
    xHTopFunctionFieldC ℚ (M / p) (infSubgroup p M H hpM) (M / p * p) = xHFunctionField M H := by
  show qExpFunctionFieldC ℚ _ = qExpFunctionFieldC ℚ _
  rw [← GammaH_eq_inf p H hpM hHp]

end Groups

section Weights

theorem exists_weights {k : ℤ} (hk : Even k) :
    ∃ a b r : ℕ, 1 ≤ r ∧ k + ((a : ℤ) * 4 + (b : ℤ) * 6) = (r : ℤ) * 12 := by
  obtain ⟨k', rfl⟩ := hk
  rcases lt_trichotomy k' 0 with h | h | h
  · refine ⟨2 * (-k').toNat, (-k').toNat, (-k').toNat, by omega, ?_⟩
    push_cast
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  · exact ⟨0, 2, 1, le_rfl, by rw [h]; norm_num⟩
  · refine ⟨k'.toNat, k'.toNat, k'.toNat, by omega, ?_⟩
    rw [Int.toNat_of_nonneg h.le]
    ring

end Weights

section LevelOneSeries

open EisensteinSeries ModularForm

def eisenstein6 : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5

theorem isIntegralQExp_E4 : IsIntegralQExp (E₄ : ℍ → ℂ) eisenstein4 := by
  rw [isIntegralQExp_iff]
  intro n
  rw [E_qExpansion_coeff (by norm_num) (by decide) n, eisenstein4, PowerSeries.coeff_mk]
  split_ifs with h
  · simp
  · rw [show _root_.bernoulli 4 = -1 / 30 by decide +kernel, ArithmeticFunction.sigma_apply]
    push_cast
    ring

theorem isIntegralQExp_E6 : IsIntegralQExp (E₆ : ℍ → ℂ) eisenstein6 := by
  rw [isIntegralQExp_iff]
  intro n
  rw [E_qExpansion_coeff (by norm_num) (by decide) n, eisenstein6, PowerSeries.coeff_mk]
  split_ifs with h
  · simp
  · rw [show _root_.bernoulli 6 = 1 / 42 by decide +kernel, ArithmeticFunction.sigma_apply]
    push_cast
    ring

theorem constantCoeff_eisenstein6 : PowerSeries.constantCoeff eisenstein6 = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]; simp [eisenstein6]

def eisProd (a b : ℕ) : ModularForm 𝒮ℒ ((a : ℤ) * 4 + (b : ℤ) * 6) :=
  (E₄.pow a).mul (E₆.pow b)

theorem isIntegralQExp_eisProd (a b : ℕ) :
    IsIntegralQExp (eisProd a b : ℍ → ℂ) (eisenstein4 ^ a * eisenstein6 ^ b) := by
  rw [IsIntegralQExp, eisProd, ModularForm.coe_mul, ModularForm.coe_pow, ModularForm.coe_pow, map_mul, map_pow, map_pow,
    isIntegralQExp_E4, isIntegralQExp_E6]
  have h4 := ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL E₄ a
  have h6 := ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL E₆ b
  rw [ModularForm.coe_pow] at h4 h6
  rw [← h4, ← h6]
  have h := (ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL (E₄.pow a) (E₆.pow b)).symm
  rw [ModularForm.coe_pow, ModularForm.coe_pow] at h
  exact h

theorem constantCoeff_eisProdSeries (a b : ℕ) :
    PowerSeries.constantCoeff (eisenstein4 ^ a * eisenstein6 ^ b) = 1 := by
  rw [map_mul, map_pow, map_pow, constantCoeff_eisenstein4, constantCoeff_eisenstein6, one_pow, one_pow, one_mul]

def deltaPow (r : ℕ) : ModularForm 𝒮ℒ ((r : ℤ) * 12) :=
  (CuspForm.discriminant : ModularForm 𝒮ℒ 12).pow r

theorem isIntegralQExp_deltaPow (r : ℕ) :
    IsIntegralQExp (deltaPow r : ℍ → ℂ) ((PowerSeries.X * dedekindEtaUnit) ^ r) := by
  rw [IsIntegralQExp, deltaPow, map_pow, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    show ⇑(CuspForm.discriminant : ModularForm 𝒮ℒ 12) = ModularForm.discriminant from rfl,
    ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit]

theorem coeff_deltaPowSeries (r : ℕ) : PowerSeries.coeff r ((PowerSeries.X * dedekindEtaUnit) ^ r) = 1 := by
  rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    map_pow, constantCoeff_dedekindEtaUnit, one_pow]

def e4cube : ModularForm 𝒮ℒ 12 := (E₄.pow 3).mcast (by norm_num)

theorem isIntegralQExp_e4cube : IsIntegralQExp (e4cube : ℍ → ℂ) (eisenstein4 ^ 3) := by
  rw [IsIntegralQExp, e4cube, ModularForm.coe_mcast, ModularForm.coe_pow, map_pow, isIntegralQExp_E4]
  have h4 := ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL E₄ 3
  rw [ModularForm.coe_pow] at h4
  exact h4.symm

theorem isIntegralQExp_delta :
    IsIntegralQExp ((CuspForm.discriminant : ModularForm 𝒮ℒ 12) : ℍ → ℂ) (PowerSeries.X * dedekindEtaUnit) := by
  rw [IsIntegralQExp, show ⇑(CuspForm.discriminant : ModularForm 𝒮ℒ 12) = ModularForm.discriminant from rfl]
  exact ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit.symm

theorem coeff_one_deltaSeries : PowerSeries.coeff 1 (PowerSeries.X * dedekindEtaUnit) = 1 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    constantCoeff_dedekindEtaUnit]

theorem jqModC_mul_delta (R : Type*) [CommRing R] :
    jqModC R * intSeriesR R (PowerSeries.X * dedekindEtaUnit) = intSeriesR R (eisenstein4 ^ 3) := by
  rw [jqModC, intSeriesR, intSeriesR, jNum, mul_assoc, ← map_mul, ← map_mul,
    show eisenstein4 ^ 3 * dedekindEtaUnitInv * (PowerSeries.X * dedekindEtaUnit) =
      PowerSeries.X * eisenstein4 ^ 3 by
        rw [mul_comm PowerSeries.X dedekindEtaUnit, ← mul_assoc, mul_assoc (eisenstein4 ^ 3),
          mul_comm dedekindEtaUnitInv, dedekindEtaUnit_mul_inv, mul_one, mul_comm],
    map_mul, PowerSeries.map_X, map_mul, HahnSeries.ofPowerSeries_X, ← mul_assoc,
    HahnSeries.single_mul_single]
  simp

end LevelOneSeries

section Ratios

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

local notation "Qb" => AlgebraicClosure ℚ

def qC (F : ℍ → ℂ) : LaurentSeries ℂ := HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 F)

theorem qC_eq_intSeriesR {F : ℍ → ℂ} {q : PowerSeries ℤ} (h : IsIntegralQExp F q) : qC F = intSeriesR ℂ q := by
  rw [qC, intSeriesR, ← h]

theorem coeffMap_ι_coeffEmb (ι : Qb →+* ℂ) (X : LaurentSeries ℚ) :
    coeffMap ι (coeffEmb Qb X) = coeffMap (algebraMap ℚ ℂ) X := by
  rw [coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (Subsingleton.elim _ _) X

theorem ratio_mem {k : ℤ} (F G : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) {p₁ p₂ : PowerSeries ℤ}
    (h₁ : IsIntegralQExp F p₁) (h₂ : IsIntegralQExp G p₂) (hne : intSeriesC ℚ p₂ ≠ 0) :
    coeffEmb Qb (intSeriesC ℚ p₁ / intSeriesC ℚ p₂) ∈ xHFunctionFieldBar M H :=
  coeffEmb_mem_laurentBaseChange Qb (F₀ := xHFunctionField M H)
    (show intSeriesC ℚ p₁ / intSeriesC ℚ p₂ ∈ qExpFunctionFieldC ℚ (CohCarrier.GammaH M H) from
      div_mem_qExpFunctionFieldC F G h₁ h₂ hne)

theorem coe_ratio (p₁ p₂ : PowerSeries ℤ) :
    coeffEmb Qb (intSeriesC ℚ p₁ / intSeriesC ℚ p₂) = intSeriesR Qb p₁ / intSeriesR Qb p₂ := by
  rw [map_div₀, coeffEmb, ← intSeriesR_eq_intSeriesC, ← intSeriesR_eq_intSeriesC, coeffMap_intSeriesR,
    coeffMap_intSeriesR]

theorem rep_ratio (ι : Qb →+* ℂ) {k : ℤ} (F G : ModularForm (ΓGL (CohCarrier.GammaH M H)) k)
    {p₁ p₂ : PowerSeries ℤ} (h₁ : IsIntegralQExp F p₁) (h₂ : IsIntegralQExp G p₂) (hne : intSeriesR ℂ p₂ ≠ 0) :
    coeffMap ι (coeffEmb Qb (intSeriesC ℚ p₁ / intSeriesC ℚ p₂)) * qC G = qC F := by
  rw [coe_ratio, map_div₀, coeffMap_intSeriesR, coeffMap_intSeriesR, qC_eq_intSeriesR h₁, qC_eq_intSeriesR h₂,
    div_mul_cancel₀ _ hne]

theorem coe_finset_sum_smul {k : ℤ} {ι' : Type*} (s : Finset ι') (c : ι' → ℂ)
    (g : ι' → ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    (⇑(∑ i ∈ s, c i • g i) : ℍ → ℂ) = ∑ i ∈ s, c i • (⇑(g i) : ℍ → ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj, ModularForm.coe_add, ModularForm.IsGLPos.coe_smul, ih]

theorem qExpansion_finset_sum_smul {k : ℤ} {ι' : Type*} (s : Finset ι') (c : ι' → ℂ)
    (g : ι' → ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    qExpansion 1 (∑ i ∈ s, c i • (⇑(g i) : ℍ → ℂ)) = ∑ i ∈ s, c i • qExpansion 1 (⇑(g i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [qExpansion_zero]
  | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj]
      have e1 : (c j • (⇑(g j) : ℍ → ℂ) + ∑ x ∈ s, c x • (⇑(g x) : ℍ → ℂ)) =
          ⇑(c j • g j) + ⇑(∑ i ∈ s, c i • g i) := by
        rw [ModularForm.IsGLPos.coe_smul, coe_finset_sum_smul]
      rw [e1, ModularForm.qExpansion_add one_pos (one_mem_strictPeriods_GammaH M H),
        ModularForm.IsGLPos.coe_smul,
        qExpansion_smul (ModularFormClass.analyticAt_cuspFunction_zero (g j) one_pos
          (one_mem_strictPeriods_GammaH M H)),
        coe_finset_sum_smul, ih]

end Ratios

section Main

local notation "Qb" => AlgebraicClosure ℚ

local instance isAlgebraicQbar_alpint : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ

theorem mem_of_isIntegral {K : Type*} [Field K] (A : ValuationSubring K) {x : K} (hx : IsIntegral ℤ x) : x ∈ A := by
  have hx' : IsIntegral A x := hx.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := K)).mp hx'
  rw [← hy]
  exact y.2

theorem isIntegral_intCast_Qb (z : ℤ) : IsIntegral ℤ ((z : Qb)) := by
  have := isIntegral_algebraMap (R := ℤ) (A := Qb) (x := z)
  rwa [eq_intCast] at this

theorem isIntegral_natCast_Qb (n : ℕ) : IsIntegral ℤ ((n : Qb)) := by
  have := isIntegral_intCast_Qb (n : ℤ)
  rwa [Int.cast_natCast] at this

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

theorem real_smul_fun (x : ℝ) (F : ℍ → ℂ) : (x • F) = ((x : ℂ) • F) := by
  funext τ; simp [Complex.real_smul]

theorem qC_mul_levelOne_slash (p : ℕ) [Fact p.Prime] (hpM : p ∣ M) [NeZero (M / p)]
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M (M / p)) {k m : ℤ}
    (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) (E : ModularForm 𝒮ℒ m) :
    qC ((⇑f * ⇑E) ∣[k + m] W.alGL) =
      HahnSeries.C ((M / p : ℕ) : ℂ) * qC (⇑f ∣[k] W.alGL) *
        (HahnSeries.C (((M / p : ℕ) : ℂ) ^ (m - 1)) *
          qExpand ℂ (M / p) (HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (E : ℍ → ℂ)))) := by
  have hdet : |((W.alGL.det : ℝˣ) : ℝ)| = ((M / p : ℕ) : ℝ) := by
    rw [ModularForm.AtkinLehnerDatum.val_det_alGL]; exact abs_of_nonneg (Nat.cast_nonneg _)
  rw [ModularForm.mul_slash, hdet, real_smul_fun]
  set f₁ := alForm p hpM hHp W.a W.b 1 1 (datum_rel p hpM W) W.alGL (datum_alGL_coe p hpM W) f with hf₁
  set E₁ := alForm p hpM hHp W.a W.b 1 1 (datum_rel p hpM W) W.alGL (datum_alGL_coe p hpM W) (resLevelOne H E) with hE₁
  have hf₁c : ⇑f₁ = ⇑f ∣[k] W.alGL := rfl
  have hE₁c : ⇑E₁ = ⇑E ∣[m] W.alGL := rfl
  have e1 : ((((M / p : ℕ) : ℝ) : ℂ) • (⇑f ∣[k] W.alGL * ⇑E ∣[m] W.alGL)) =
      ⇑((((M / p : ℕ) : ℝ) : ℂ) • f₁) * ⇑E₁ := by
    rw [ModularForm.IsGLPos.coe_smul, hf₁c, hE₁c, smul_mul_assoc]
  rw [qC, e1, ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods_GammaH M H),
    ModularForm.IsGLPos.coe_smul,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_GammaH M H), hE₁c,
    PowerSeries.smul_eq_C_mul, map_mul, map_mul, HahnSeries.ofPowerSeries_C,
    qC_levelOne_slash_alGL p hpM W hHp E, hf₁c, qC]
  push_cast
  ring

def SlashCompat (ι : Qb →+* ℂ) (A : GL (Fin 2) ℝ)
    (σ : xHFunctionFieldBar M H ≃ₐ[Qb] xHFunctionFieldBar M H) : Prop :=
  ∀ (u : xHFunctionFieldBar M H) (k : ℤ)
    (f g : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k),
    coeffMap ι (u : LaurentSeries Qb) * HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 ⇑g) =
      HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 ⇑f) →
    coeffMap ι ((σ u : xHFunctionFieldBar M H) : LaurentSeries Qb) *
        HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g ∣[k] A)) =
      HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f ∣[k] A))

theorem sigma_J_coe (p : ℕ) [Fact p.Prime] (hpM : p ∣ M) [NeZero (M / p)]
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M (M / p)) (ι : Qb →+* ℂ) (hcoeffinj : Function.Injective (coeffMap ι))
    (σ : xHFunctionFieldBar M H ≃ₐ[Qb] xHFunctionFieldBar M H) (hσ : SlashCompat ι W.alGL σ)
    (JE : xHFunctionFieldBar M H)
    (hJval : (JE : LaurentSeries Qb) =
      coeffEmb Qb (intSeriesC ℚ (eisenstein4 ^ 3) / intSeriesC ℚ (PowerSeries.X * dedekindEtaUnit))) :
    ((σ JE : xHFunctionFieldBar M H) : LaurentSeries Qb) = jqNModC Qb (M / p) := by
  have hΔneC : intSeriesR ℂ (PowerSeries.X * dedekindEtaUnit) ≠ 0 :=
    intSeriesR_ne_zero_of_coeff _ 1 coeff_one_deltaSeries
  have hrep := rep_ratio ι (resLevelOne H e4cube) (resLevelOne H (CuspForm.discriminant : ModularForm 𝒮ℒ 12))
    isIntegralQExp_e4cube isIntegralQExp_delta hΔneC
  rw [← hJval] at hrep
  have h1 := hσ JE 12 (resLevelOne H e4cube) (resLevelOne H (CuspForm.discriminant : ModularForm 𝒮ℒ 12)) hrep
  change coeffMap ι _ * qC (⇑(CuspForm.discriminant : ModularForm 𝒮ℒ 12) ∣[(12 : ℤ)] W.alGL) =
    qC (⇑e4cube ∣[(12 : ℤ)] W.alGL) at h1
  rw [qC, qC, qC_levelOne_slash_alGL p hpM W hHp, qC_levelOne_slash_alGL p hpM W hHp,
    ← qC, ← qC, qC_eq_intSeriesR isIntegralQExp_e4cube, qC_eq_intSeriesR isIntegralQExp_delta,
    ← jqModC_mul_delta ℂ, map_mul, ← mul_assoc, ← mul_assoc] at h1
  have hne : HahnSeries.C (((M / p : ℕ) : ℂ) ^ ((12 : ℤ) - 1)) *
      qExpand ℂ (M / p) (intSeriesR ℂ (PowerSeries.X * dedekindEtaUnit)) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · exact HahnSeries.C_ne_zero (zpow_ne_zero _ (by exact_mod_cast NeZero.ne (M / p)))
    · intro h0
      exact hΔneC (qExpand_injective (R := ℂ) (N := M / p) (by rw [h0, map_zero]))
  have h2 : coeffMap ι ((σ JE : xHFunctionFieldBar M H) : LaurentSeries Qb) = qExpand ℂ (M / p) (jqModC ℂ) := by
    apply mul_right_cancel₀ hne
    rw [← mul_assoc]
    calc _ = HahnSeries.C (((M / p : ℕ) : ℂ) ^ ((12 : ℤ) - 1)) * qExpand ℂ (M / p) (jqModC ℂ) *
          qExpand ℂ (M / p) (intSeriesR ℂ (PowerSeries.X * dedekindEtaUnit)) := h1
      _ = _ := by ring
  apply hcoeffinj
  rw [h2, jqNModC, coeffMap_qExpand]
  congr 1
  exact (map_jqModC ι).symm

theorem sigma_u_coe (p : ℕ) [Fact p.Prime] (hpM : p ∣ M) [NeZero (M / p)]
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M (M / p)) (ι : Qb →+* ℂ) (hcoeffinj : Function.Injective (coeffMap ι))
    (σ : xHFunctionFieldBar M H ≃ₐ[Qb] xHFunctionFieldBar M H) (hσ : SlashCompat ι W.alGL σ)
    {k : ℤ} (f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
    (pf : PowerSeries ℤ) (hpf : IsIntegralQExp (⇑f) pf) (a b r : ℕ) (hw : k + ((a : ℤ) * 4 + (b : ℤ) * 6) = (r : ℤ) * 12)
    (t : PowerSeries Qb) (hTmap : t.map ι = qExpansion 1 (⇑f ∣[k] W.alGL))
    (uE : xHFunctionFieldBar M H)
    (huval : (uE : LaurentSeries Qb) = coeffEmb Qb (intSeriesC ℚ (pf * (eisenstein4 ^ a * eisenstein6 ^ b)) /
      intSeriesC ℚ ((PowerSeries.X * dedekindEtaUnit) ^ r))) :
    ((σ uE : xHFunctionFieldBar M H) : LaurentSeries Qb) *
      (HahnSeries.C (((M / p : ℕ) : Qb) ^ ((r : ℤ) * 12 - 1)) *
        qExpand Qb (M / p) (intSeriesR Qb ((PowerSeries.X * dedekindEtaUnit) ^ r))) =
      HahnSeries.C (((M / p : ℕ) : Qb) ^ ((a : ℤ) * 4 + (b : ℤ) * 6)) *
        HahnSeries.ofPowerSeries ℤ Qb t * qExpand Qb (M / p) (intSeriesR Qb (eisenstein4 ^ a * eisenstein6 ^ b)) := by
  set pN : PowerSeries ℤ := eisenstein4 ^ a * eisenstein6 ^ b with hpN
  set pG : PowerSeries ℤ := (PowerSeries.X * dedekindEtaUnit) ^ r with hpG
  set NE : ModularForm (ΓGL (CohCarrier.GammaH M H)) ((a : ℤ) * 4 + (b : ℤ) * 6) := resLevelOne H (eisProd a b)
    with hNE
  set P : ModularForm (ΓGL (CohCarrier.GammaH M H)) ((r : ℤ) * 12) := (f.mul NE).mcast hw with hP
  set G : ModularForm (ΓGL (CohCarrier.GammaH M H)) ((r : ℤ) * 12) := resLevelOne H (deltaPow r) with hG
  have hPcoe : (⇑P : ℍ → ℂ) = ⇑f * ⇑(eisProd a b) := rfl
  have hGcoe : (⇑G : ℍ → ℂ) = ⇑(deltaPow r) := rfl
  have hPint : IsIntegralQExp (⇑P) (pf * pN) := by
    rw [IsIntegralQExp, hPcoe, map_mul, hpf, (isIntegralQExp_eisProd a b)]
    exact (ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods_GammaH M H) f NE).symm
  have hGint : IsIntegralQExp (⇑G) pG := by rw [hGcoe]; exact isIntegralQExp_deltaPow r
  have hGneC : intSeriesR ℂ pG ≠ 0 := intSeriesR_ne_zero_of_coeff pG r (coeff_deltaPowSeries r)
  have hrep := rep_ratio ι P G hPint hGint hGneC
  rw [← huval] at hrep
  have h1 := hσ uE _ P G hrep
  change coeffMap ι _ * qC (⇑G ∣[(r : ℤ) * 12] W.alGL) = qC (⇑P ∣[(r : ℤ) * 12] W.alGL) at h1
  have hPq : qC (⇑P ∣[(r : ℤ) * 12] W.alGL) =
      HahnSeries.C ((M / p : ℕ) : ℂ) * qC (⇑f ∣[k] W.alGL) *
        (HahnSeries.C (((M / p : ℕ) : ℂ) ^ (((a : ℤ) * 4 + (b : ℤ) * 6) - 1)) *
          qExpand ℂ (M / p) (intSeriesR ℂ pN)) := by
    rw [hPcoe, ← hw, qC_mul_levelOne_slash p hpM hHp W f (eisProd a b), ← qC,
      qC_eq_intSeriesR (isIntegralQExp_eisProd a b)]
  have hGq : qC (⇑G ∣[(r : ℤ) * 12] W.alGL) =
      HahnSeries.C (((M / p : ℕ) : ℂ) ^ ((r : ℤ) * 12 - 1)) * qExpand ℂ (M / p) (intSeriesR ℂ pG) := by
    rw [hGcoe, qC, qC_levelOne_slash_alGL p hpM W hHp (deltaPow r), ← qC, qC_eq_intSeriesR (isIntegralQExp_deltaPow r)]
  rw [hPq, hGq] at h1
  apply hcoeffinj
  rw [map_mul, map_mul, map_mul, map_mul, coeffMap_C, coeffMap_C, coeffMap_qExpand, coeffMap_qExpand,
    coeffMap_intSeriesR, coeffMap_intSeriesR, coeffMap_ofPowerSeries, hTmap, map_zpow₀ ι, map_zpow₀ ι, map_natCast,
    h1, qC]
  have hQC : ((M / p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne (M / p)
  rw [show (((M / p : ℕ) : ℂ) ^ ((a : ℤ) * 4 + (b : ℤ) * 6)) =
      ((M / p : ℕ) : ℂ) * ((M / p : ℕ) : ℂ) ^ ((a : ℤ) * 4 + (b : ℤ) * 6 - 1) by
    rw [zpow_sub_one₀ hQC, mul_left_comm, mul_inv_cancel₀ hQC, mul_one], map_mul]
  ring

theorem gauss_at_place (p : ℕ) [Fact p.Prime] (hpM : p ∣ M) [NeZero (M / p)]
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hpQ : ¬ p ∣ M / p)
    (σ : xHFunctionFieldBar M H ≃ₐ[Qb] xHFunctionFieldBar M H)
    (JE uE : xHFunctionFieldBar M H) (hJcoe : (JE : LaurentSeries Qb) = jqModC Qb)
    (hσJ : ((σ JE : xHFunctionFieldBar M H) : LaurentSeries Qb) = jqNModC Qb (M / p))
    (pP pG pN : PowerSeries ℤ) (r : ℕ) (hpGr : PowerSeries.coeff r pG = 1) (hpN0 : PowerSeries.constantCoeff pN = 1)
    (hucoe : (uE : LaurentSeries Qb) = intSeriesR Qb pP / intSeriesR Qb pG)
    (eG eN : ℕ) (t : PowerSeries Qb)
    (hσu : ((σ uE : xHFunctionFieldBar M H) : LaurentSeries Qb) *
      (HahnSeries.C (((M / p : ℕ) : Qb) ^ eG) * qExpand Qb (M / p) (intSeriesR Qb pG)) =
      HahnSeries.C (((M / p : ℕ) : Qb) ^ eN) * HahnSeries.ofPowerSeries ℤ Qb t * qExpand Qb (M / p) (intSeriesR Qb pN))
    (A : ValuationSubring Qb) (hA : (p : Qb) ∈ A.nonunits)
    (hatt : ∃ n₀, ∀ n, A.valuation (PowerSeries.coeff n t) ≤ A.valuation (PowerSeries.coeff n₀ t)) :
    ∀ n, PowerSeries.coeff n t ∈ A := by
  have hpp : p.Prime := Fact.out

  have K1 : ∀ (w : laurentBaseChange Qb (xHTopFunctionFieldC ℚ (M / p) (infSubgroup p M H hpM) (M / p * p)) ≃ₐ[Qb]
        laurentBaseChange Qb (xHTopFunctionFieldC ℚ (M / p) (infSubgroup p M H hpM) (M / p * p)))
      (J : laurentBaseChange Qb (xHTopFunctionFieldC ℚ (M / p) (infSubgroup p M H hpM) (M / p * p)))
      (_hJ : (J : LaurentSeries Qb) = jqModC Qb)
      (_hwJ : ((w J : laurentBaseChange Qb (xHTopFunctionFieldC ℚ (M / p) (infSubgroup p M H hpM) (M / p * p))) :
        LaurentSeries Qb) = jqNModC Qb (M / p))
      (u : laurentBaseChange Qb (xHTopFunctionFieldC ℚ (M / p) (infSubgroup p M H hpM) (M / p * p))),
      (∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
          (u : LaurentSeries Qb) * coeffMap A.subtype y = coeffMap A.subtype x) ↔
      (∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
          ((w u : laurentBaseChange Qb (xHTopFunctionFieldC ℚ (M / p) (infSubgroup p M H hpM) (M / p * p))) :
              LaurentSeries Qb) * coeffMap A.subtype y = coeffMap A.subtype x) :=
    fun w J hJ hwJ u => ModularCurve.exists_mul_coeffMap_eq_iff_of_algEquiv_apply_jq_eq_jqN_of_not_dvd
      (M / p) (infSubgroup p M H hpM) hpQ A hA (M / p) hpQ w J hJ hwJ u
  rw [xHTopFunctionFieldC_eq p H hpM hHp] at K1
  replace K1 := K1 σ JE hJcoe hσJ uE

  have hlhs : ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
      ((uE : xHFunctionFieldBar M H) : LaurentSeries Qb) * coeffMap A.subtype y = coeffMap A.subtype x := by
    refine ⟨intSeriesR A pP, intSeriesR A pG, ?_, ?_⟩
    · rw [coeffMap_intSeriesR]
      exact intSeriesR_ne_zero_of_coeff pG r hpGr
    · rw [coeffMap_intSeriesR, coeffMap_intSeriesR, hucoe,
        div_mul_cancel₀ _ (intSeriesR_ne_zero_of_coeff (R := Qb) pG r hpGr)]
  obtain ⟨x, y, hy, hxy⟩ := K1.mp hlhs

  have hQunit : A.valuation ((M / p : ℕ) : Qb) = 1 :=
    valuation_natCast_eq_one_of_coprime A hA ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hpQ).symm
  have hQres : IsLocalRing.residue A ((M / p : ℕ) : A) ≠ 0 := by
    rw [IsLocalRing.residue_ne_zero_iff_isUnit, A.valuation_eq_one_iff]
    exact hQunit

  set YA : LaurentSeries A := HahnSeries.C (((M / p : ℕ) : A) ^ eN) * qExpand A (M / p) (intSeriesR A pN) * y with hYA
  set XA : LaurentSeries A := HahnSeries.C (((M / p : ℕ) : A) ^ eG) * qExpand A (M / p) (intSeriesR A pG) * x with hXA
  have hmain : HahnSeries.ofPowerSeries ℤ Qb t * coeffMap A.subtype YA = coeffMap A.subtype XA := by
    rw [hYA, hXA, map_mul, map_mul, map_mul, map_mul, coeffMap_C, coeffMap_C, coeffMap_qExpand, coeffMap_qExpand,
      coeffMap_intSeriesR, coeffMap_intSeriesR, map_pow A.subtype, map_pow A.subtype, map_natCast A.subtype]
    calc HahnSeries.ofPowerSeries ℤ Qb t *
          (HahnSeries.C (((M / p : ℕ) : Qb) ^ eN) * qExpand Qb (M / p) (intSeriesR Qb pN) * coeffMap A.subtype y)
        = (HahnSeries.C (((M / p : ℕ) : Qb) ^ eN) * HahnSeries.ofPowerSeries ℤ Qb t *
            qExpand Qb (M / p) (intSeriesR Qb pN)) * coeffMap A.subtype y := by ring
      _ = ((σ uE : xHFunctionFieldBar M H) : LaurentSeries Qb) *
            (HahnSeries.C (((M / p : ℕ) : Qb) ^ eG) * qExpand Qb (M / p) (intSeriesR Qb pG)) *
            coeffMap A.subtype y := by rw [hσu]
      _ = HahnSeries.C (((M / p : ℕ) : Qb) ^ eG) * qExpand Qb (M / p) (intSeriesR Qb pG) *
            (((σ uE : xHFunctionFieldBar M H) : LaurentSeries Qb) * coeffMap A.subtype y) := by ring
      _ = _ := by rw [hxy]
  have hYA0 : coeffMap (IsLocalRing.residue A) YA ≠ 0 := by
    rw [hYA, map_mul, map_mul, coeffMap_C, coeffMap_qExpand, coeffMap_intSeriesR, map_pow (IsLocalRing.residue A)]
    refine mul_ne_zero (mul_ne_zero ?_ ?_) hy
    · exact HahnSeries.C_ne_zero (pow_ne_zero _ hQres)
    · intro h0
      have hN0 : intSeriesR (IsLocalRing.ResidueField A) pN ≠ 0 := by
        apply intSeriesR_ne_zero_of_coeff pN 0
        rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hpN0]
      exact hN0 (qExpand_injective (R := IsLocalRing.ResidueField A) (N := M / p) (by rw [h0, map_zero]))
  obtain ⟨Yp, Xp, hYp, htY⟩ := exists_powerSeries_datum A t YA XA hYA0 hmain
  exact forall_coeff_mem_of_mul_eq A t Yp Xp hYp htY hatt

theorem mainK2e
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M (M / p)) {k : ℤ} (hk : Even k)
    (f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
    (pf : PowerSeries ℤ) (hpf : ModularCurve.IsIntegralQExp (⇑f) pf) :
    ∃ D : ℕ, ¬ p ∣ D ∧ ∀ n : ℕ, IsIntegral ℤ
      ((D : ℂ) * (UpperHalfPlane.qExpansion 1 (ModularForm.alSlash W k ⇑f)).coeff n) := by
  haveI hQ : NeZero (M / p) := neZero_div p hpM
  have hpp : p.Prime := Fact.out
  have hpQ : ¬ p ∣ M / p := not_dvd_div p hpM W
  have hrel := datum_rel p hpM W
  have hWmat := datum_alGL_coe p hpM W

  set ιA : Qb →ₐ[ℚ] ℂ := IsAlgClosed.lift with hιA
  set ι : Qb →+* ℂ := ιA.toRingHom with hι
  have hιinj : Function.Injective ι := ιA.toRingHom.injective
  have hcoeffinj : Function.Injective (coeffMap ι) := fun x y h => by
    ext n; exact hιinj (by simpa using congrArg (fun z => HahnSeries.coeff z n) h)

  obtain ⟨a, b, r, hr, hw⟩ := exists_weights hk

  have hfrat : ∀ n, ∃ q : ℚ, (qExpansion 1 ⇑f).coeff n = (q : ℂ) := fun n =>
    ⟨(PowerSeries.coeff n pf : ℤ), by rw [← hpf.coeff n]; push_cast; rfl⟩
  obtain ⟨nn, c, g, pg, hg, hsum⟩ :=
    ModularCurve.exists_slash_atkinLehnerCofactor_eq_sum_smul_of_ratCast_qExpansion_of_even
      p M H hpM hpM2 hHp W.a W.b 1 1 hrel W.alGL hWmat hk f hfrat ι

  set t : PowerSeries Qb := ∑ i, PowerSeries.C (c i) * (pg i).map (Int.castRingHom Qb) with ht
  have hT : ∀ n, ι (PowerSeries.coeff n t) = (qExpansion 1 (⇑f ∣[k] W.alGL)).coeff n := by
    intro n
    rw [hsum, qExpansion_finset_sum_smul, ht, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_map, map_mul, PowerSeries.coeff_smul, smul_eq_mul,
      ← (hg i).coeff n, eq_intCast, map_intCast]
  have hTmap : t.map ι = qExpansion 1 (⇑f ∣[k] W.alGL) := by
    ext n; rw [PowerSeries.coeff_map]; exact hT n

  set L : IntermediateField ℚ Qb := IntermediateField.adjoin ℚ (Set.range c) with hL
  haveI : FiniteDimensional ℚ L :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  have htL : ∀ n, PowerSeries.coeff n t ∈ L := by
    intro n
    rw [ht, map_sum]
    refine sum_mem fun i _ => ?_
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_map, eq_intCast]
    exact mul_mem (IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩) (intCast_mem L _)

  have hden : ∀ i, ∃ d : ℕ, d ≠ 0 ∧ IsIntegral ℤ ((d : Qb) * c i) := by
    intro i
    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors ℤ) (Rₘ := ℚ)
      (c i) ((Algebra.IsAlgebraic.isAlgebraic (c i)).isIntegral)
    refine ⟨(m : ℤ).natAbs, Int.natAbs_ne_zero.mpr (nonZeroDivisors.coe_ne_zero m), ?_⟩
    have hm' : IsIntegral ℤ (((m : ℤ) : Qb) * c i) := by
      have : ((m : ℤ) : Qb) * c i = m • c i := by
        rw [Submonoid.smul_def, zsmul_eq_mul]
      rw [this]; exact hm
    have hcast : (((m : ℤ).natAbs : ℕ) : Qb) = ((m : ℤ) : Qb) ∨ (((m : ℤ).natAbs : ℕ) : Qb) = -((m : ℤ) : Qb) := by
      rcases Int.natAbs_eq (m : ℤ) with h | h
      · left; conv_rhs => rw [h]; rw [Int.cast_natCast]
      · right; conv_rhs => rw [h]; rw [Int.cast_neg, Int.cast_natCast, neg_neg]
    rcases hcast with h | h
    · rw [h]; exact hm'
    · rw [h, neg_mul]; exact hm'.neg
  choose d hd0 hdint using hden
  set B : ℕ := ∏ i, d i with hBdef
  have hB : B ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hd0 i
  have hBint : ∀ n, IsIntegral ℤ ((B : Qb) * PowerSeries.coeff n t) := by
    intro n
    rw [ht, map_sum, Finset.mul_sum]
    refine IsIntegral.sum _ fun i _ => ?_
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_map, eq_intCast, hBdef, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    push_cast
    rw [mul_assoc, ← mul_assoc ((d i : ℕ) : Qb)]
    refine IsIntegral.mul (IsIntegral.prod _ fun j _ => isIntegral_natCast_Qb _) ?_
    exact (hdint i).mul (isIntegral_intCast_Qb _)

  set pN : PowerSeries ℤ := eisenstein4 ^ a * eisenstein6 ^ b with hpN
  set pG : PowerSeries ℤ := (PowerSeries.X * dedekindEtaUnit) ^ r with hpG
  have hpGr : PowerSeries.coeff r pG = 1 := coeff_deltaPowSeries r
  have hpN0 : PowerSeries.constantCoeff pN = 1 := constantCoeff_eisProdSeries a b
  have hGneQ : intSeriesC ℚ pG ≠ 0 := intSeriesR_ne_zero_of_coeff (R := ℚ) pG r hpGr
  have hΔneQ : intSeriesC ℚ (PowerSeries.X * dedekindEtaUnit) ≠ 0 :=
    intSeriesR_ne_zero_of_coeff (R := ℚ) _ 1 coeff_one_deltaSeries
  have hPint : IsIntegralQExp (⇑((f.mul (resLevelOne H (eisProd a b))).mcast hw :
      ModularForm (ΓGL (CohCarrier.GammaH M H)) ((r : ℤ) * 12))) (pf * pN) := by
    rw [IsIntegralQExp, ModularForm.coe_mcast, ModularForm.coe_mul, map_mul, hpf, coe_resLevelOne,
      (isIntegralQExp_eisProd a b)]
    exact (ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods_GammaH M H) f
      (resLevelOne H (eisProd a b))).symm
  have hGint : IsIntegralQExp (⇑(resLevelOne H (deltaPow r))) pG := isIntegralQExp_deltaPow r
  set uE : xHFunctionFieldBar M H :=
    ⟨coeffEmb Qb (intSeriesC ℚ (pf * pN) / intSeriesC ℚ pG), ratio_mem _ _ hPint hGint hGneQ⟩ with huE
  set JE : xHFunctionFieldBar M H :=
    ⟨coeffEmb Qb (intSeriesC ℚ (eisenstein4 ^ 3) / intSeriesC ℚ (PowerSeries.X * dedekindEtaUnit)),
      ratio_mem (resLevelOne H e4cube) (resLevelOne H (CuspForm.discriminant : ModularForm 𝒮ℒ 12))
        isIntegralQExp_e4cube isIntegralQExp_delta hΔneQ⟩ with hJE
  have hJval : ((JE : xHFunctionFieldBar M H) : LaurentSeries Qb) =
      coeffEmb Qb (intSeriesC ℚ (eisenstein4 ^ 3) / intSeriesC ℚ (PowerSeries.X * dedekindEtaUnit)) := rfl
  have huval : ((uE : xHFunctionFieldBar M H) : LaurentSeries Qb) =
      coeffEmb Qb (intSeriesC ℚ (pf * pN) / intSeriesC ℚ pG) := rfl
  have hJcoe : ((JE : xHFunctionFieldBar M H) : LaurentSeries Qb) = jqModC Qb := by
    rw [hJval, coe_ratio, div_eq_iff (intSeriesR_ne_zero_of_coeff (R := Qb) _ 1 coeff_one_deltaSeries)]
    exact (jqModC_mul_delta Qb).symm
  have hucoe : ((uE : xHFunctionFieldBar M H) : LaurentSeries Qb) = intSeriesR Qb (pf * pN) / intSeriesR Qb pG := by
    rw [huval, coe_ratio]
  obtain ⟨σ, hσ⟩ := ModularCurve.exists_algEquiv_xHFunctionFieldBar_slash_atkinLehnerCofactor
    p M H hpM hpM2 hHp W.a W.b 1 1 hrel W.alGL hWmat ι
  have hσJ := sigma_J_coe p hpM hHp W ι hcoeffinj σ hσ JE hJval
  have hσu := sigma_u_coe p hpM hHp W ι hcoeffinj σ hσ f pf hpf a b r hw t hTmap uE huval

  have hcastG : (((r * 12 - 1 : ℕ) : ℤ)) = (r : ℤ) * 12 - 1 := by omega
  have hcastN : (((a * 4 + b * 6 : ℕ) : ℤ)) = (a : ℤ) * 4 + (b : ℤ) * 6 := by push_cast; ring
  rw [show (((M / p : ℕ) : Qb) ^ ((r : ℤ) * 12 - 1)) = ((M / p : ℕ) : Qb) ^ (r * 12 - 1) by
      rw [← zpow_natCast, hcastG],
    show (((M / p : ℕ) : Qb) ^ ((a : ℤ) * 4 + (b : ℤ) * 6)) = ((M / p : ℕ) : Qb) ^ (a * 4 + b * 6) by
      rw [← zpow_natCast, hcastN]] at hσu

  have hgauss : ∀ A : ValuationSubring Qb, (p : Qb) ∈ A.nonunits → ∀ n, PowerSeries.coeff n t ∈ A := by
    intro A hA
    have hatt := exists_forall_valuation_le A hpp hA L (fun n => PowerSeries.coeff n t) htL hB
      (fun n => mem_of_isIntegral A (hBint n))
    exact gauss_at_place p hpM hHp hpQ σ JE uE hJcoe hσJ (pf * pN) pG pN r hpGr hpN0 hucoe _ _ t hσu A hA hatt

  obtain ⟨e, D, hpD, hBD⟩ := Nat.exists_eq_pow_mul_and_not_dvd hB p hpp.ne_one
  refine ⟨D, hpD, fun n => ?_⟩
  have hz : IsIntegral ℤ ((D : Qb) * PowerSeries.coeff n t) := by
    refine isIntegral_of_pow_mul_of_forall_valuationSubring (K := Qb) hpp _ e ?_ ?_
    · have : (p : Qb) ^ e * ((D : Qb) * PowerSeries.coeff n t) = (B : Qb) * PowerSeries.coeff n t := by
        rw [hBD]; push_cast; ring
      rw [this]; exact hBint n
    · intro A hA
      exact A.mul_mem _ _ (natCast_mem A D) (hgauss A hA n)
  obtain ⟨Pz, hPzm, hPzx⟩ := hz
  refine ⟨Pz, hPzm, ?_⟩
  have heq : ι ((D : Qb) * PowerSeries.coeff n t) = (D : ℂ) * (qExpansion 1 (ModularForm.alSlash W k ⇑f)).coeff n := by
    rw [map_mul, map_natCast, hT n, ModularForm.alSlash_def]
  have h1 := Polynomial.hom_eval₂ Pz (algebraMap ℤ Qb) ι ((D : Qb) * PowerSeries.coeff n t)
  rw [hPzx, map_zero, heq, show ι.comp (algebraMap ℤ Qb) = algebraMap ℤ ℂ from Subsingleton.elim _ _] at h1
  exact h1.symm

end Main

end ALCofactorPIntegrality
p2m_reactivate "P2MW.S_ModularForm_exists_not_dvd_and_forall_isIntegral_mul_qExpansion_alSlash_of_isIntegralQExp_of_even.ALCofactorPIntegrality"

end
p2m_reactivate "P2MW.S_ModularForm_exists_not_dvd_and_forall_isIntegral_mul_qExpansion_alSlash_of_isIntegralQExp_of_even.ALCofactorPIntegrality"

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M (M / p)) {k : ℤ} (hk : Even k)
    (f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
    (pf : PowerSeries ℤ) (hpf : ModularCurve.IsIntegralQExp (⇑f) pf) :
    ∃ D : ℕ, ¬ p ∣ D ∧ ∀ n : ℕ, IsIntegral ℤ
      ((D : ℂ) * (UpperHalfPlane.qExpansion 1 (ModularForm.alSlash W k ⇑f)).coeff n) :=
  ALCofactorPIntegrality.mainK2e p M H hpM hpM2 hHp W hk f pf hpf

end S_ModularForm_exists_not_dvd_and_forall_isIntegral_mul_qExpansion_alSlash_of_isIntegralQExp_of_even
end P2MW
export P2MW.S_ModularForm_exists_not_dvd_and_forall_isIntegral_mul_qExpansion_alSlash_of_isIntegralQExp_of_even (solution)
