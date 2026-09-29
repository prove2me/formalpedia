-- Prove2me | solution 1 for ModularCurve.ord_coeffEmb_modularUnitSeries_eq_sub_of_ord_jqModC_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/dffaea25-de15-5946-a897-37a38e5326df

import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_ModularPolynomialData_weighted_support_le
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_modularUnitSeries
import Theorems.Thm_ModularCurve_ord_cuspZeroBar_coeffEmb_modularUnitSeries
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_jq
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_ord_cuspZeroBar_coeffEmb_jq
import Theorems.Thm_ModularCurve_ord_cuspZeroBar_coeffEmb_jqN
import Theorems.Thm_ModularCurve_isFrickeAutFull_frickeInvolutionFull_prime
import Theorems.Thm_ModularCurve_eq_cuspInftyBar_or_eq_cuspZeroBar
import Theorems.Thm_ModularCurve_isCusp_iff_ord_neg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_coeffEmb_modularUnitSeries_eq_sub_of_ord_jqModC_neg
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve ModularCurve~coeffEmb_jq~coeffEmb_qExpand Polynomial"

namespace ModularUnitOrder

private abbrev Kb : Type := AlgebraicClosure ℚ

section Series

private theorem coeffEmb_jq : coeffEmb Kb jq = jqModC Kb := by
  have hmap : jNumQ.map (algebraMap ℚ Kb) = jNum.map (Int.castRingHom Kb) := by
    ext n
    simp [jNumQ, PowerSeries.coeff_map]
  rw [jq, jqModC, map_mul]
  congr 1
  · ext k
    rw [coeffEmb_coeff]
    by_cases hk : k = (-1 : ℤ) <;> simp [hk]
  · ext k
    rw [coeffEmb_coeff]
    by_cases hk : 0 ≤ k
    · lift k to ℕ using hk
      rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
        ← hmap, PowerSeries.coeff_map]
    · rw [ofPowerSeries_coeff_of_neg _ (by omega), ofPowerSeries_coeff_of_neg _ (by omega),
        map_zero]

private theorem coeffEmb_qExpand (n : ℕ) [NeZero n] (x : LaurentSeries ℚ) :
    coeffEmb Kb (qExpand ℚ n x) = qExpand Kb n (coeffEmb Kb x) :=
  coeffMap_qExpand (algebraMap ℚ Kb) n x

private theorem coeffEmb_qExpand_jq (n : ℕ) [NeZero n] :
    coeffEmb Kb (qExpand ℚ n jq) = qExpand Kb n (jqModC Kb) := by
  rw [← coeffEmb_jq]
  exact coeffMap_qExpand (algebraMap ℚ Kb) n jq

private theorem algebraMap_eq_single (c : Kb) :
    algebraMap Kb (LaurentSeries Kb) c = HahnSeries.single 0 c := by
  have h1 : algebraMap Kb (PowerSeries Kb) c = PowerSeries.C c := by simp
  rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]
  rfl

private theorem coeffEmb_algebraMap (c : ℚ) :
    coeffEmb Kb (algebraMap ℚ (LaurentSeries ℚ) c) = algebraMap Kb (LaurentSeries Kb) (algebraMap ℚ Kb c) := by
  rw [algebraMap_apply_eq_single, algebraMap_eq_single]
  exact coeffMap_single _ _ _

variable (N : ℕ) [NeZero N]

omit [NeZero N] in
private theorem qExpand_jqModC_mem {n : ℕ} [NeZero n] (h : n ∣ N) :
    qExpand Kb n (jqModC Kb) ∈ modularFunctionFieldBar N := by
  rw [← coeffEmb_qExpand_jq]
  exact coeffEmb_mem_laurentBaseChange Kb (jqd_mem_full N h)

end Series

section Valued

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

private theorem valuation_eval₂_lt (hint : ∀ n : ℤ, v n ≤ 1) (Ψ : Polynomial (Polynomial ℤ)) {g : Γ₀} (hg : g ≠ 0)
    {x y : K} (h : ∀ b a : ℕ, (Ψ.coeff b).coeff a ≠ 0 → v x ^ a * v y ^ b < g) :
    v (Ψ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y) < g := by
  rw [Polynomial.eval₂_eq_sum_range]
  refine v.map_sum_lt hg fun b _ => ?_
  rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.aeval_eq_sum_range, Finset.sum_mul]
  refine v.map_sum_lt hg fun a _ => ?_
  by_cases hc : (Ψ.coeff b).coeff a = 0
  · rw [hc, zero_smul, zero_mul, Valuation.map_zero]; exact zero_lt_iff.mpr hg
  rw [zsmul_eq_mul, Valuation.map_mul, Valuation.map_mul, Valuation.map_pow, Valuation.map_pow]
  calc v ((Ψ.coeff b).coeff a : K) * v x ^ a * v y ^ b
      ≤ 1 * v x ^ a * v y ^ b := by gcongr; exact hint _
    _ = v x ^ a * v y ^ b := by rw [one_mul]
    _ < g := h b a hc

private theorem valuation_dichotomy (hint : ∀ n : ℤ, v n ≤ 1) (Φ : Polynomial (Polynomial ℤ)) (p : ℕ) (hp : 1 ≤ p)
    (hrest : ∀ b a : ℕ, ((Φ - (C (X ^ (p + 1)) + X ^ (p + 1) - C (X ^ p) * X ^ p)).coeff b).coeff a ≠ 0 →
      a ≤ p ∧ b ≤ p ∧ ¬ (a = p ∧ b = p))
    {x y : K} (hroot : Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y = 0) (hx : 1 < v x) :
    v y = v x ^ p ∨ v y ^ p = v x := by
  set Rest := Φ - (C (X ^ (p + 1)) + X ^ (p + 1) - C (X ^ p) * X ^ p) with hRest
  set R := v x with hR
  set T := v y with hT
  have hR0 : R ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hR1 : 1 ≤ R := le_of_lt hx

  set ρ := Rest.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y with hρ
  have hid : x ^ (p + 1) + y ^ (p + 1) - x ^ p * y ^ p + ρ = 0 := by
    have hΦ : Φ = (C (X ^ (p + 1)) + X ^ (p + 1) - C (X ^ p) * X ^ p) + Rest := by rw [hRest]; ring
    have h := hroot
    rw [hΦ, Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, Polynomial.eval₂_X_pow] at h
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_pow, Polynomial.aeval_X] at h
    rw [hρ, AlgHom.toRingHom_eq_coe]
    linear_combination h

  have hvx : ∀ n : ℕ, v (x ^ n) = R ^ n := fun n => by rw [Valuation.map_pow]
  have hvy : ∀ n : ℕ, v (y ^ n) = T ^ n := fun n => by rw [Valuation.map_pow]
  have hvxy : v (x ^ p * y ^ p) = R ^ p * T ^ p := by rw [Valuation.map_mul, hvx, hvy]

  have hrest_lt_mid : 1 < T → ∀ b a : ℕ, (Rest.coeff b).coeff a ≠ 0 → R ^ a * T ^ b < R ^ p * T ^ p := by
    intro hT1 b a hc
    obtain ⟨ha, hb, hne⟩ := hrest b a hc
    have hT0 : T ≠ 0 := ne_of_gt (lt_trans zero_lt_one hT1)
    rcases Nat.lt_or_ge a p with hap | hap
    · calc R ^ a * T ^ b ≤ R ^ a * T ^ p := by gcongr; exact le_of_lt hT1
        _ < R ^ p * T ^ p := by
          apply mul_lt_mul_of_pos_right (pow_lt_pow_right₀ hx hap) (pow_pos (zero_lt_iff.mpr hT0) _)
    · have hap' : a = p := le_antisymm ha hap
      have hbp : b < p := lt_of_le_of_ne hb fun h => hne ⟨hap', h⟩
      calc R ^ a * T ^ b ≤ R ^ p * T ^ b := by gcongr
        _ < R ^ p * T ^ p := by
          apply mul_lt_mul_of_pos_left (pow_lt_pow_right₀ hT1 hbp) (pow_pos (zero_lt_iff.mpr hR0) _)

  have hrest_le_low : T ≤ 1 → ∀ b a : ℕ, (Rest.coeff b).coeff a ≠ 0 → R ^ a * T ^ b ≤ R ^ p := by
    intro hT1 b a hc
    obtain ⟨ha, -, -⟩ := hrest b a hc
    calc R ^ a * T ^ b ≤ R ^ a * 1 := by gcongr; exact pow_le_one₀ zero_le' hT1
      _ = R ^ a := mul_one _
      _ ≤ R ^ p := pow_le_pow_right₀ hR1 ha
  rcases lt_trichotomy T (R ^ p) with hlt | heq | hgt
  · rcases lt_trichotomy (T ^ p) R with hlt' | heq' | hgt'
    ·
      exfalso
      have hg0 : R ^ (p + 1) ≠ 0 := pow_ne_zero _ hR0
      have hTR : T < R := by
        rcases le_or_gt T 1 with h1 | h1
        · exact lt_of_le_of_lt h1 hx
        · exact lt_of_le_of_lt (le_self_pow₀ (le_of_lt h1) (by omega)) hlt'
      have h1 : v (y ^ (p + 1)) < R ^ (p + 1) := by
        rw [hvy]; exact pow_lt_pow_left₀ hTR zero_le' (by omega)
      have h2' : R ^ p * T ^ p < R ^ (p + 1) := by
        rw [pow_succ]
        exact mul_lt_mul_of_pos_left hlt' (pow_pos (zero_lt_iff.mpr hR0) _)
      have h2 : v (x ^ p * y ^ p) < R ^ (p + 1) := by rw [hvxy]; exact h2'
      have hRp : R ^ p < R ^ (p + 1) := pow_lt_pow_right₀ hx (Nat.lt_succ_self p)
      have h3 : v ρ < R ^ (p + 1) := by
        refine valuation_eval₂_lt v hint Rest hg0 fun b a hc => ?_
        rcases le_or_gt T 1 with hT1 | hT1
        · exact lt_of_le_of_lt (hrest_le_low hT1 b a hc) hRp
        · exact lt_trans (hrest_lt_mid hT1 b a hc) h2'

      have heqn : x ^ (p + 1) = -(y ^ (p + 1) - x ^ p * y ^ p + ρ) := by linear_combination hid
      have hlt'' : v (x ^ (p + 1)) < R ^ (p + 1) := by
        rw [heqn, Valuation.map_neg]
        exact v.map_add_lt (v.map_sub_lt h1 h2) h3
      rw [hvx] at hlt''
      exact lt_irrefl _ hlt''
    · exact Or.inr heq'
    ·
      exfalso
      have hT1 : 1 < T := by
        by_contra h
        rw [not_lt] at h
        have : T ^ p ≤ 1 := pow_le_one₀ zero_le' h
        exact absurd (lt_of_lt_of_le (lt_trans hx hgt') this) (lt_irrefl _)
      have hT0 : T ≠ 0 := ne_of_gt (lt_trans zero_lt_one hT1)
      have hg0 : R ^ p * T ^ p ≠ 0 := mul_ne_zero (pow_ne_zero _ hR0) (pow_ne_zero _ hT0)
      have h1 : v (y ^ (p + 1)) < R ^ p * T ^ p := by
        rw [hvy, pow_succ, mul_comm]
        exact mul_lt_mul_of_pos_right hlt (pow_pos (zero_lt_iff.mpr hT0) _)
      have h2 : v (x ^ (p + 1)) < R ^ p * T ^ p := by
        rw [hvx, pow_succ]
        exact mul_lt_mul_of_pos_left hgt' (pow_pos (zero_lt_iff.mpr hR0) _)
      have h3 : v ρ < R ^ p * T ^ p := valuation_eval₂_lt v hint Rest hg0 (hrest_lt_mid hT1)
      have heqn : x ^ p * y ^ p = x ^ (p + 1) + y ^ (p + 1) + ρ := by linear_combination (-1 : K) * hid
      have hlt'' : v (x ^ p * y ^ p) < R ^ p * T ^ p := by
        rw [heqn]
        exact v.map_add_lt (v.map_add_lt h2 h1) h3
      rw [hvxy] at hlt''
      exact lt_irrefl _ hlt''
  · exact Or.inl heq
  ·
    exfalso
    have hT1 : 1 < T := lt_of_le_of_lt (one_le_pow₀ hR1) hgt
    have hT0 : T ≠ 0 := ne_of_gt (lt_trans zero_lt_one hT1)
    have hg0 : T ^ (p + 1) ≠ 0 := pow_ne_zero _ hT0
    have hRT : R < T := lt_of_le_of_lt (le_self_pow₀ hR1 (by omega)) hgt
    have h1 : v (x ^ (p + 1)) < T ^ (p + 1) := by
      rw [hvx]; exact pow_lt_pow_left₀ hRT zero_le' (by omega)
    have h2 : v (x ^ p * y ^ p) < T ^ (p + 1) := by
      rw [hvxy, pow_succ, mul_comm (T ^ p)]
      exact mul_lt_mul_of_pos_right hgt (pow_pos (zero_lt_iff.mpr hT0) _)
    have h3 : v ρ < T ^ (p + 1) := by
      refine valuation_eval₂_lt v hint Rest hg0 fun b a hc => lt_trans (hrest_lt_mid hT1 b a hc) ?_
      rw [pow_succ, mul_comm (T ^ p)]
      exact mul_lt_mul_of_pos_right hgt (pow_pos (zero_lt_iff.mpr hT0) _)
    have heqn : y ^ (p + 1) = -(x ^ (p + 1) - x ^ p * y ^ p + ρ) := by linear_combination hid
    have hlt'' : v (y ^ (p + 1)) < T ^ (p + 1) := by
      rw [heqn, Valuation.map_neg]
      exact v.map_add_lt (v.map_sub_lt h1 h2) h3
    rw [hvy] at hlt''
    exact lt_irrefl _ hlt''

end Valued

section Support

private theorem rest_support (Φ : Polynomial (Polynomial ℤ)) (p : ℕ) (hp : 1 ≤ p)
    (h₁ : ∀ b a : ℕ, ((Φ - (X ^ (p + 1) - C (X ^ p) * X ^ p)).coeff b).coeff a ≠ 0 → 1 * a + p * b ≤ p ^ 2 + p - 1)
    (h₂ : ∀ b a : ℕ, ((Φ - (C (X ^ (p + 1)) - C (X ^ p) * X ^ p)).coeff b).coeff a ≠ 0 → p * a + 1 * b ≤ p ^ 2 + p - 1) :
    ∀ b a : ℕ, ((Φ - (C (X ^ (p + 1)) + X ^ (p + 1) - C (X ^ p) * X ^ p)).coeff b).coeff a ≠ 0 →
      a ≤ p ∧ b ≤ p ∧ ¬ (a = p ∧ b = p) := by
  intro b a h
  have hsq : p ^ 2 = p * p := sq p

  have cY : ∀ b a : ℕ, ((X ^ (p + 1) : Polynomial (Polynomial ℤ)).coeff b).coeff a
      = if b = p + 1 ∧ a = 0 then 1 else 0 := fun b a => by
    rw [Polynomial.coeff_X_pow]
    by_cases hb : b = p + 1
    · rw [if_pos hb, Polynomial.coeff_one]
      by_cases ha : a = 0
      · rw [if_pos ha, if_pos ⟨hb, ha⟩]
      · rw [if_neg ha, if_neg (fun h => ha h.2)]
    · rw [if_neg hb, Polynomial.coeff_zero, if_neg (fun h => hb h.1)]
  have cX : ∀ b a : ℕ, ((C (X ^ (p + 1)) : Polynomial (Polynomial ℤ)).coeff b).coeff a
      = if b = 0 ∧ a = p + 1 then 1 else 0 := fun b a => by
    rw [Polynomial.coeff_C]
    by_cases hb : b = 0
    · rw [if_pos hb, Polynomial.coeff_X_pow]
      by_cases ha : a = p + 1
      · rw [if_pos ha, if_pos ⟨hb, ha⟩]
      · rw [if_neg ha, if_neg (fun h => ha h.2)]
    · rw [if_neg hb, Polynomial.coeff_zero, if_neg (fun h => hb h.1)]

  have e₁ : ((Φ - (C (X ^ (p + 1)) + X ^ (p + 1) - C (X ^ p) * X ^ p)).coeff b).coeff a
      = ((Φ - (X ^ (p + 1) - C (X ^ p) * X ^ p)).coeff b).coeff a - (if b = 0 ∧ a = p + 1 then 1 else 0) := by
    rw [show Φ - (C (X ^ (p + 1)) + X ^ (p + 1) - C (X ^ p) * X ^ p)
        = (Φ - (X ^ (p + 1) - C (X ^ p) * X ^ p)) - C (X ^ (p + 1)) by ring,
      Polynomial.coeff_sub, Polynomial.coeff_sub, cX]
  have e₂ : ((Φ - (C (X ^ (p + 1)) + X ^ (p + 1) - C (X ^ p) * X ^ p)).coeff b).coeff a
      = ((Φ - (C (X ^ (p + 1)) - C (X ^ p) * X ^ p)).coeff b).coeff a - (if b = p + 1 ∧ a = 0 then 1 else 0) := by
    rw [show Φ - (C (X ^ (p + 1)) + X ^ (p + 1) - C (X ^ p) * X ^ p)
        = (Φ - (C (X ^ (p + 1)) - C (X ^ p) * X ^ p)) - X ^ (p + 1) by ring,
      Polynomial.coeff_sub, Polynomial.coeff_sub, cY]
  have hpp1 : p * (p + 1) = p ^ 2 + p := by ring
  by_cases hXa : b = 0 ∧ a = p + 1
  ·
    exfalso
    obtain ⟨rfl, rfl⟩ := hXa
    rw [e₂, if_neg (by omega), sub_zero] at h
    have := h₂ 0 (p + 1) h
    rw [mul_zero, add_zero, hpp1] at this
    omega
  by_cases hYa : b = p + 1 ∧ a = 0
  · exfalso
    obtain ⟨rfl, rfl⟩ := hYa
    rw [e₁, if_neg (by omega), sub_zero] at h
    have := h₁ (p + 1) 0 h
    rw [mul_zero, zero_add, hpp1] at this
    omega

  have hb₁ : 1 * a + p * b ≤ p ^ 2 + p - 1 := by
    rw [e₁, if_neg hXa, sub_zero] at h; exact h₁ b a h
  have hb₂ : p * a + 1 * b ≤ p ^ 2 + p - 1 := by
    have h' := h
    rw [e₂, if_neg hYa, sub_zero] at h'; exact h₂ b a h'
  rw [one_mul] at hb₁ hb₂
  have hbp : b ≤ p := by
    by_contra hb
    have : p * (p + 1) ≤ p * b := Nat.mul_le_mul_left p (by omega)
    rw [hpp1] at this
    omega
  have hap : a ≤ p := by
    by_contra ha
    have : p * (p + 1) ≤ p * a := Nat.mul_le_mul_left p (by omega)
    rw [hpp1] at this
    omega
  refine ⟨hap, hbp, ?_⟩
  rintro ⟨rfl, rfl⟩
  rw [hsq] at hb₁
  omega

end Support

section Place

variable (K : Type*) [Field K]

private theorem mem_of_ord_nonneg' {F : Type*} [Field F] [Algebra K F] (u : Place K F) {g : F} (hg : g ≠ 0)
    (h : 0 ≤ u.ord g) : g ∈ u.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible u.toValuationSubring
  obtain ⟨w, hw⟩ := u.exists_unit_mul_zpow hg hπ
  rw [hw]
  refine mul_mem (SetLike.coe_mem _) ?_
  rw [show ((π : F) ^ (u.ord g)) = ((π : F) ^ ((u.ord g).toNat)) by
    rw [← zpow_natCast, Int.toNat_of_nonneg h]]
  exact pow_mem (SetLike.coe_mem π) _

private theorem ord_nonneg_of_mem' {F : Type*} [Field F] [Algebra K F] (u : Place K F) {g : F}
    (hg : g ∈ u.toValuationSubring) : 0 ≤ u.ord g := by
  by_cases hg0 : g = 0
  · rw [hg0, Place.ord_zero]
  by_contra hneg
  rw [not_le] at hneg
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible u.toValuationSubring

  obtain ⟨w, hw⟩ := u.exists_unit_mul_zpow hg0 hπ
  have hπ0 : (π : F) ≠ 0 := by
    intro h
    apply hπ.ne_zero
    exact Subtype.ext h
  have hmem : (π : F) ^ (u.ord g) ∈ u.toValuationSubring := by
    have : (π : F) ^ (u.ord g) = ((w⁻¹ : u.toValuationSubringˣ) : u.toValuationSubring) * g := by
      conv_rhs => rw [hw]
      rw [← mul_assoc, ← MulMemClass.coe_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, OneMemClass.coe_one,
        one_mul]
    rw [this]
    exact mul_mem (SetLike.coe_mem _) hg
  have hinv : (π : F)⁻¹ ∈ u.toValuationSubring := by
    have hk : ∃ k : ℕ, u.ord g = -((k : ℤ) + 1) := ⟨(-(u.ord g) - 1).toNat, by omega⟩
    obtain ⟨k, hk⟩ := hk
    rw [hk, zpow_neg, zpow_add₀ hπ0, zpow_one, zpow_natCast, mul_inv_rev] at hmem
    have : (π : F)⁻¹ = ((π : F)⁻¹ * ((π : F) ^ k)⁻¹) * (π : F) ^ k := by
      rw [mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hπ0), mul_one]
    rw [this]
    exact mul_mem hmem (pow_mem (SetLike.coe_mem π) k)
  have hunit : IsUnit π :=
    ⟨⟨π, ⟨(π : F)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hπ0), Subtype.ext (inv_mul_cancel₀ hπ0)⟩, rfl⟩
  exact hπ.not_isUnit hunit

private theorem ord_eq_of_valuation_eq {F : Type*} [Field F] [Algebra K F] (u : Place K F) {f g : F}
    (hf : f ≠ 0) (hg : g ≠ 0)
    (h : u.toValuationSubring.valuation f = u.toValuationSubring.valuation g) : u.ord f = u.ord g := by
  have hvg : u.toValuationSubring.valuation g ≠ 0 := (Valuation.ne_zero_iff _).mpr hg
  have hq : u.toValuationSubring.valuation (f / g) = 1 := by rw [map_div₀, h, div_self hvg]
  have hmem : f / g ∈ u.toValuationSubring := (u.toValuationSubring.valuation_le_one_iff _).mp hq.le
  have hunit : IsUnit (⟨f / g, hmem⟩ : u.toValuationSubring) :=
    (u.toValuationSubring.valuation_eq_one_iff _).mpr hq
  obtain ⟨w, hw⟩ := hunit
  have h0 : u.ord (f / g) = 0 := by
    have := u.ord_coe_unit w
    rw [hw] at this
    exact this
  rw [div_eq_mul_inv, u.ord_mul hf (inv_ne_zero hg), u.ord_inv] at h0
  omega

private theorem one_lt_valuation_of_ord_neg {F : Type*} [Field F] [Algebra K F] (u : Place K F) {g : F}
    (h : u.ord g < 0) : 1 < u.toValuationSubring.valuation g := by
  rw [← not_le, u.toValuationSubring.valuation_le_one_iff]
  exact fun hmem => absurd (ord_nonneg_of_mem' K u hmem) (not_le.mpr h)

end Place

section Chain

variable (N : ℕ) [NeZero N]

private def J (n : ℕ) [NeZero n] (h : n ∣ N) : modularFunctionFieldBar N :=
  ⟨qExpand Kb n (jqModC Kb), qExpand_jqModC_mem N h⟩

omit [NeZero N] in
private theorem coe_J (n : ℕ) [NeZero n] (h : n ∣ N) : (J N n h : LaurentSeries Kb) = qExpand Kb n (jqModC Kb) := rfl

omit [NeZero N] in
private theorem J_congr {n n' : ℕ} [NeZero n] [NeZero n'] (hn : n ∣ N) (hn' : n' ∣ N) (h : n = n') :
    J N n hn = J N n' hn' := by
  subst h; rfl

omit [NeZero N] in
private theorem J_ne_zero {n : ℕ} [NeZero n] (hn : n ∣ N) : J N n hn ≠ 0 := by
  intro h
  have h1 : qExpand Kb n (jqModC Kb) = 0 := by rw [← coe_J N n hn]; exact congrArg Subtype.val h
  exact jqModC_ne_zero_of_nontrivial Kb ((injective_iff_map_eq_zero _).mp (qExpand_injective n) _ h1)

omit [NeZero N] in

private theorem coe_eval₂_aeval (Φ : Polynomial (Polynomial ℤ)) (y z : modularFunctionFieldBar N) :
    ((Φ.eval₂ (Polynomial.aeval (R := ℤ) y).toRingHom z : modularFunctionFieldBar N) : LaurentSeries Kb)
      = Φ.eval₂ (Polynomial.aeval (R := ℤ) (y : LaurentSeries Kb)).toRingHom (z : LaurentSeries Kb) := by
  rw [show ((Φ.eval₂ (Polynomial.aeval (R := ℤ) y).toRingHom z : modularFunctionFieldBar N) : LaurentSeries Kb)
      = algebraMap (modularFunctionFieldBar N) (LaurentSeries Kb)
          (Φ.eval₂ (Polynomial.aeval (R := ℤ) y).toRingHom z) from rfl, Polynomial.hom_eval₂]
  congr 1
  · apply Polynomial.ringHom_ext
    · intro n
      simp only [AlgHom.toRingHom_eq_coe, eq_intCast, map_intCast]
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Polynomial.aeval_X]
      rfl

omit [NeZero N] in

private theorem eval₂_J {p m : ℕ} [NeZero p] [NeZero m] [NeZero (m * p)] (data : ModularPolynomialData p)
    (hm : m ∣ N) (hmp : m * p ∣ N) :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (J N m hm)).toRingHom (J N (m * p) hmp) = 0 := by
  apply Subtype.val_injective
  rw [coe_eval₂_aeval N, coe_J, coe_J]
  exact data.eval_jqNModC_mul_eq_zero Kb m

omit [NeZero N] in

private theorem step (u : Place Kb (modularFunctionFieldBar N)) {p m : ℕ} (hp : p.Prime) [NeZero m]
    [NeZero (m * p)] (hm : m ∣ N) (hmp : m * p ∣ N) (hneg : u.ord (J N m hm) < 0) :
    ((u.ord (J N (m * p) hmp) = p * u.ord (J N m hm)) ∨
        ((p : ℤ) * u.ord (J N (m * p) hmp) = u.ord (J N m hm))) ∧
      u.ord (J N (m * p) hmp) < 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨data⟩ := nonempty_modularPolynomialData p
  set x := J N m hm with hxdef
  set y := J N (m * p) hmp with hydef
  set v := u.toValuationSubring.valuation with hv
  have hint : ∀ n : ℤ, v n ≤ 1 := fun n =>
    (u.toValuationSubring.valuation_le_one_iff _).mpr (intCast_mem u.toValuationSubring n)
  have hx0 : x ≠ 0 := J_ne_zero N hm
  have hy0 : y ≠ 0 := J_ne_zero N hmp
  have hvx : 1 < v x := one_lt_valuation_of_ord_neg Kb u hneg
  have hsupp := data.weighted_support_le p
  have hroot := eval₂_J N data hm hmp
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hppos : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hdich := valuation_dichotomy v hint data.Φ p hp1 (rest_support data.Φ p hp1 hsupp.1 hsupp.2) hroot hvx
  have hrel : (u.ord y = p * u.ord x) ∨ ((p : ℤ) * u.ord y = u.ord x) := by
    rcases hdich with hbr | hbr
    · left
      rw [← Valuation.map_pow] at hbr
      rw [ord_eq_of_valuation_eq Kb u hy0 (pow_ne_zero _ hx0) hbr, ← zpow_natCast, u.ord_zpow]
    · right
      rw [← Valuation.map_pow] at hbr
      rw [← ord_eq_of_valuation_eq Kb u (pow_ne_zero _ hy0) hx0 hbr, ← zpow_natCast, u.ord_zpow]
  refine ⟨hrel, ?_⟩
  rcases hrel with h | h
  · rw [h]; exact mul_neg_of_pos_of_neg hppos hneg
  · by_contra hcon
    rw [not_lt] at hcon
    have : (0 : ℤ) ≤ p * u.ord y := mul_nonneg hppos.le hcon
    rw [h] at this
    exact absurd hneg (not_lt.mpr this)

private theorem chain (u : Place Kb (modularFunctionFieldBar N)) (k : ℕ) :
    ∀ (m : ℕ) [NeZero m] [NeZero (m * k)] (hm : m ∣ N) (hmk : m * k ∣ N), u.ord (J N m hm) < 0 →
      ∃ a b : ℕ, a * b = k ∧ (b : ℤ) * u.ord (J N (m * k) hmk) = a * u.ord (J N m hm) ∧
        u.ord (J N (m * k) hmk) < 0 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro m _ _ hm hmk hneg
    rcases Nat.lt_or_ge 1 k with hk | hk
    ·
      obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt hk)
      obtain ⟨k', rfl⟩ := hpk
      have hk'pos : 0 < k' := Nat.pos_of_ne_zero fun h => by
        subst h; simp at hk
      have hk'lt : k' < p * k' := lt_mul_of_one_lt_left hk'pos hp.one_lt
      have hmp : m * p ∣ N := Dvd.dvd.trans ⟨k', by ring⟩ hmk
      haveI : NeZero (m * p) := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne N) hmp⟩
      have hmpk : m * p * k' ∣ N := by rwa [mul_assoc]
      haveI : NeZero (m * p * k') := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne N) hmpk⟩
      obtain ⟨hst, hneg'⟩ := step N u hp hm hmp hneg
      obtain ⟨a', b', hab', hrel', hneg''⟩ := ih k' hk'lt (m * p) hmp hmpk hneg'
      have hJ : u.ord (J N (m * p * k') hmpk) = u.ord (J N (m * (p * k')) hmk) :=
        congrArg u.ord (J_congr N hmpk hmk (mul_assoc m p k'))
      rw [hJ] at hrel' hneg''
      rcases hst with h | h
      · refine ⟨a' * p, b', by rw [← hab']; ring, ?_, hneg''⟩
        push_cast
        linear_combination hrel' + (a' : ℤ) * h
      · refine ⟨a', b' * p, by rw [← hab']; ring, ?_, hneg''⟩
        push_cast
        linear_combination (p : ℤ) * hrel' + (a' : ℤ) * h
    ·
      have hk1 : k = 1 := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with h | h
        · exact absurd (by simp [h]) (NeZero.ne (m * k))
        · exact h
      subst hk1
      have hJ : J N (m * 1) hmk = J N m hm := J_congr N hmk hm (mul_one m)
      refine ⟨1, 1, rfl, ?_, ?_⟩
      · rw [hJ]
      · rw [hJ]; exact hneg

end Chain

section Literals

variable (N : ℕ) [NeZero N]

private theorem lit_j :
    (⟨coeffEmb Kb jq, coeffEmb_mem_laurentBaseChange Kb (modularFunctionField_le_full N (jq_mem N))⟩ :
        modularFunctionFieldBar N) = J N 1 (one_dvd N) :=
  Subtype.ext (by
    show coeffEmb Kb jq = qExpand Kb 1 (jqModC Kb)
    rw [coeffEmb_jq, qExpand_one_apply])

omit [NeZero N] in
private theorem lit_jd (n : ℕ) [NeZero n] (h : n ∣ N) :
    (⟨coeffEmb Kb (qExpand ℚ n jq), coeffEmb_mem_laurentBaseChange Kb (jqd_mem_full N h)⟩ :
        modularFunctionFieldBar N) = J N n h :=
  Subtype.ext (coeffEmb_qExpand_jq n)

end Literals

section PrimeLevel

private theorem prime_level (p : ℕ) [Fact p.Prime] (w : Place Kb (modularFunctionFieldBar p))
    (hw : w.ord ⟨coeffEmb Kb jq, coeffEmb_mem_laurentBaseChange Kb (jq_mem_full p)⟩ < 0) :
    w.ord ⟨coeffEmb Kb (modularUnitSeries p),
        coeffEmb_mem_laurentBaseChange Kb (modularUnitSeries_mem_modularFunctionFieldFull p)⟩
      = w.ord ⟨coeffEmb Kb (qExpand ℚ p jq), coeffEmb_mem_laurentBaseChange Kb (jqd_mem_full p (dvd_refl p))⟩
        - w.ord ⟨coeffEmb Kb jq, coeffEmb_mem_laurentBaseChange Kb (jq_mem_full p)⟩ := by
  have hc : IsCusp (⟨coeffEmb Kb jq, coeffEmb_mem_laurentBaseChange Kb (jq_mem_full p)⟩ :
      modularFunctionFieldBar p) w := (isCusp_iff_ord_neg _ w).mpr hw
  rcases eq_cuspInftyBar_or_eq_cuspZeroBar p w hc with rfl | rfl
  · rw [ord_cuspInftyBar_coeffEmb_modularUnitSeries p (modularUnitSeries_mem_modularFunctionFieldFull p),
      ord_cuspInftyBar_coeffEmb_qExpand p p (dvd_refl p),
      ord_cuspInftyBar_coeffEmb_jq p]
    ring
  · have hF := isFrickeAutFull_frickeInvolutionFull_prime p
    rw [ord_cuspZeroBar_coeffEmb_modularUnitSeries p (modularUnitSeries_mem_modularFunctionFieldFull p),
      ord_cuspZeroBar_coeffEmb_jqN p hF,
      ord_cuspZeroBar_coeffEmb_jq p hF]
    ring

end PrimeLevel

section Degeneracy

variable (N : ℕ) [NeZero N]

private theorem qExpand_mem_bar {d p : ℕ} [NeZero d] [NeZero p] (hdp : d * p ∣ N) (x : LaurentSeries Kb)
    (hx : x ∈ modularFunctionFieldBar p) : qExpand Kb d x ∈ modularFunctionFieldBar N := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem x hx =>
    rcases hx with ⟨c, rfl⟩ | ⟨y, hy, rfl⟩
    · rw [algebraMap_eq_single, qExpand_single, mul_zero, ← algebraMap_eq_single]
      exact (modularFunctionFieldBar N).algebraMap_mem c
    · rw [← coeffEmb_qExpand]
      refine coeffEmb_mem_laurentBaseChange Kb ?_
      have hmap : qExpandₐ d y ∈ (modularFunctionFieldFull p).map (qExpandₐ d) := by
        rw [← SetLike.mem_coe, IntermediateField.coe_map]
        exact Set.mem_image_of_mem _ hy
      have h1 : qExpand ℚ d y ∈ modularFunctionFieldFull (p * d) := full_degeneracy_map_le p d hmap
      exact full_degeneracy_le (by rw [mul_comm]; exact hdp) h1
  | one => rw [map_one]; exact one_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

private def phi (d p : ℕ) [NeZero d] [NeZero p] (hdp : d * p ∣ N) :
    modularFunctionFieldBar p →ₐ[Kb] modularFunctionFieldBar N where
  toFun x := ⟨qExpand Kb d x, qExpand_mem_bar N hdp x x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)
  commutes' c := Subtype.ext (by
    show qExpand Kb d (algebraMap Kb (LaurentSeries Kb) c) = algebraMap Kb (LaurentSeries Kb) c
    rw [algebraMap_eq_single, qExpand_single, mul_zero])

private theorem coe_phi {d p : ℕ} [NeZero d] [NeZero p] (hdp : d * p ∣ N) (x : modularFunctionFieldBar p) :
    ((phi N d p hdp x : modularFunctionFieldBar N) : LaurentSeries Kb) = qExpand Kb d x := rfl

end Degeneracy

section Integral

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

private theorem mem_algebraicClosure_of_root_up {x y : E} (hx : x ∈ algebraicClosure F E)
    (Φ : Polynomial (Polynomial ℤ)) (hmon : Φ.Monic)
    (hroot : Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y = 0) : y ∈ algebraicClosure F E := by
  set A := algebraicClosure F E
  set x' : A := ⟨x, hx⟩ with hx'
  set Q : Polynomial A := Φ.map (Polynomial.aeval (R := ℤ) x').toRingHom with hQdef
  have hQ0 : Q ≠ 0 := (hmon.map _).ne_zero
  have hcomp : (algebraMap A E).comp (Polynomial.aeval (R := ℤ) x').toRingHom
      = (Polynomial.aeval (R := ℤ) x).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro n; simp
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Polynomial.aeval_X]
      rfl
  have hval : Polynomial.aeval y Q = 0 := by
    rw [Polynomial.aeval_def, hQdef, Polynomial.eval₂_map, hcomp]
    exact hroot
  have halg : IsAlgebraic A y := ⟨Q, hQ0, hval⟩
  exact mem_algebraicClosure_iff.mpr (halg.restrictScalars F)

private theorem coeff_coeff_succ (Φ : Polynomial (Polynomial ℤ)) (p : ℕ) (hp : 1 ≤ p)
    (hsupp : ∀ b a : ℕ, ((Φ - (C (X ^ (p + 1)) - C (X ^ p) * X ^ p)).coeff b).coeff a ≠ 0 →
      p * a + 1 * b ≤ p ^ 2 + p - 1)
    (b : ℕ) : (Φ.coeff b).coeff (p + 1) = if b = 0 then 1 else 0 := by

  have h0 : ((Φ - (C (X ^ (p + 1)) - C (X ^ p) * X ^ p)).coeff b).coeff (p + 1) = 0 := by
    by_contra h
    have h1 := hsupp b (p + 1) h
    have h2 : p ^ 2 + p - 1 < p * (p + 1) + 1 * b := by
      rw [sq, mul_add, mul_one, one_mul]
      have : 1 ≤ p * p + p := le_add_left hp
      omega
    omega

  have hR : ((C (X ^ (p + 1)) - C (X ^ p) * X ^ p : Polynomial (Polynomial ℤ)).coeff b).coeff (p + 1)
      = if b = 0 then 1 else 0 := by
    rw [Polynomial.coeff_sub, Polynomial.coeff_C, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_sub]
    by_cases hb : b = 0
    · subst hb
      rw [if_pos rfl, if_pos rfl, if_neg (by omega : ¬ (0 : ℕ) = p), mul_zero, Polynomial.coeff_zero, sub_zero,
        Polynomial.coeff_X_pow, if_pos rfl]
    · rw [if_neg hb, if_neg hb, Polynomial.coeff_zero, zero_sub, neg_eq_zero]
      by_cases hbp : b = p
      · rw [if_pos hbp, mul_one, Polynomial.coeff_X_pow, if_neg (by omega : ¬ p + 1 = p)]
      · rw [if_neg hbp, mul_zero, Polynomial.coeff_zero]
  rw [Polynomial.coeff_sub, Polynomial.coeff_sub, hR] at h0
  linear_combination h0

private theorem mem_algebraicClosure_of_root_down {x y : E} (hy : y ∈ algebraicClosure F E)
    (Φ : Polynomial (Polynomial ℤ)) (p : ℕ) (hp : 1 ≤ p)
    (hsupp : ∀ b a : ℕ, ((Φ - (C (X ^ (p + 1)) - C (X ^ p) * X ^ p)).coeff b).coeff a ≠ 0 →
      p * a + 1 * b ≤ p ^ 2 + p - 1)
    (hroot : Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y = 0) : x ∈ algebraicClosure F E := by
  set A := algebraicClosure F E
  set y' : A := ⟨y, hy⟩ with hy'
  set Q : Polynomial A := Φ.sum fun b c => Polynomial.C (y' ^ b) * c.map (Int.castRingHom A) with hQdef
  have hcoef := coeff_coeff_succ Φ p hp hsupp
  have h0mem : 0 ∈ Φ.support := by
    rw [Polynomial.mem_support_iff]
    intro h
    have := hcoef 0
    rw [h, Polynomial.coeff_zero, if_pos rfl] at this
    exact zero_ne_one this
  have hQc : Q.coeff (p + 1) = 1 := by
    rw [hQdef, Polynomial.sum_def, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single_of_mem 0 h0mem]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_map, hcoef 0, if_pos rfl, pow_zero, one_mul, map_one]
    · intro b _ hb
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_map, hcoef b, if_neg hb, map_zero, mul_zero]
  have hQ0 : Q ≠ 0 := fun h => by
    rw [h, Polynomial.coeff_zero] at hQc
    exact zero_ne_one hQc
  have hval : Polynomial.aeval x Q = 0 := by
    rw [Polynomial.eval₂_eq_sum] at hroot
    rw [hQdef, Polynomial.sum_def, map_sum]
    rw [Polynomial.sum_def] at hroot
    rw [← hroot]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, Polynomial.aeval_C, show Int.castRingHom A = algebraMap ℤ A from rfl, Polynomial.aeval_map_algebraMap,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, mul_comm, map_pow]
    rfl
  have halg : IsAlgebraic A x := ⟨Q, hQ0, hval⟩
  exact mem_algebraicClosure_iff.mpr (halg.restrictScalars F)

end Integral

section Along

variable (N : ℕ) [NeZero N]

private theorem mem_up {F : Type*} [Field F] [Algebra F (modularFunctionFieldBar N)] (k : ℕ) :
    ∀ (m n : ℕ) [NeZero m] [NeZero n] (hm : m ∣ N) (hn : n ∣ N), n = m * k →
      J N m hm ∈ algebraicClosure F (modularFunctionFieldBar N) →
        J N n hn ∈ algebraicClosure F (modularFunctionFieldBar N) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro m n _ _ hm hn hnmk hmem
    rcases Nat.lt_or_ge 1 k with hk | hk
    · obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt hk)
      obtain ⟨k', rfl⟩ := hpk
      have hk'pos : 0 < k' := Nat.pos_of_ne_zero fun h => by
        subst h; simp at hk
      have hk'lt : k' < p * k' := lt_mul_of_one_lt_left hk'pos hp.one_lt
      haveI : Fact p.Prime := ⟨hp⟩
      have hmp : m * p ∣ N := Dvd.dvd.trans ⟨k', by rw [hnmk]; ring⟩ hn
      haveI : NeZero (m * p) := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne N) hmp⟩
      obtain ⟨data⟩ := nonempty_modularPolynomialData p
      have hstep : J N (m * p) hmp ∈ algebraicClosure F (modularFunctionFieldBar N) :=
        mem_algebraicClosure_of_root_up hmem data.Φ data.monic (eval₂_J N data hm hmp)
      exact ih k' hk'lt (m * p) n hmp hn (by rw [hnmk]; ring) hstep
    · have hk1 : k = 1 := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with h | h
        · exact absurd (by rw [hnmk, h, mul_zero]) (NeZero.ne n)
        · exact h
      subst hk1
      rw [mul_one] at hnmk
      subst hnmk
      exact hmem

private theorem mem_down {F : Type*} [Field F] [Algebra F (modularFunctionFieldBar N)] (k : ℕ) :
    ∀ (m n : ℕ) [NeZero m] [NeZero n] (hm : m ∣ N) (hn : n ∣ N), n = m * k →
      J N n hn ∈ algebraicClosure F (modularFunctionFieldBar N) →
        J N m hm ∈ algebraicClosure F (modularFunctionFieldBar N) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro m n _ _ hm hn hnmk hmem
    rcases Nat.lt_or_ge 1 k with hk | hk
    · obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt hk)
      obtain ⟨k', rfl⟩ := hpk
      have hk'pos : 0 < k' := Nat.pos_of_ne_zero fun h => by
        subst h; simp at hk
      have hk'lt : k' < p * k' := lt_mul_of_one_lt_left hk'pos hp.one_lt
      haveI : Fact p.Prime := ⟨hp⟩
      have hmp : m * p ∣ N := Dvd.dvd.trans ⟨k', by rw [hnmk]; ring⟩ hn
      haveI : NeZero (m * p) := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne N) hmp⟩
      obtain ⟨data⟩ := nonempty_modularPolynomialData p
      have h := ih k' hk'lt (m * p) n hmp hn (by rw [hnmk]; ring) hmem
      exact mem_algebraicClosure_of_root_down h data.Φ p hp.one_lt.le (data.weighted_support_le p).2
        (eval₂_J N data hm hmp)
    · have hk1 : k = 1 := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with h | h
        · exact absurd (by rw [hnmk, h, mul_zero]) (NeZero.ne n)
        · exact h
      subst hk1
      rw [mul_one] at hnmk
      subst hnmk
      exact hmem

private theorem phi_isIntegral {d p : ℕ} [NeZero d] [NeZero p] (hdp : d * p ∣ N) :
    (phi N d p hdp).toRingHom.IsIntegral := by
  letI := algebraAlong (phi N d p hdp)
  set A := algebraicClosure (modularFunctionFieldBar p) (modularFunctionFieldBar N) with hA
  have hd : d ∣ N := (Dvd.intro p rfl).trans hdp

  have hJd : J N d hd ∈ A := by
    have h1 : J N d hd = algebraMap (modularFunctionFieldBar p) (modularFunctionFieldBar N) (J p 1 (one_dvd p)) := by
      apply Subtype.ext
      show qExpand Kb d (jqModC Kb) = qExpand Kb d (qExpand Kb 1 (jqModC Kb))
      rw [qExpand_one_apply]
    rw [h1]
    exact A.algebraMap_mem _

  have hJ1 : J N 1 (one_dvd N) ∈ A := mem_down N d 1 d (one_dvd N) hd (one_mul d).symm hJd
  have hJm : ∀ (m : ℕ) [NeZero m] (hm : m ∣ N), J N m hm ∈ A := fun m _ hm =>
    mem_up N m 1 m (one_dvd N) hm (one_mul m).symm hJ1

  have hrat : ∀ (z : LaurentSeries ℚ) (hz : z ∈ modularFunctionFieldFull N)
      (hz' : coeffEmb Kb z ∈ modularFunctionFieldBar N), (⟨coeffEmb Kb z, hz'⟩ : modularFunctionFieldBar N) ∈ A := by
    intro z hz
    change z ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ divisorExpansions N) at hz
    induction hz using Subfield.closure_induction with
    | mem z hz =>
      intro hz'
      rcases hz with ⟨c, rfl⟩ | ⟨m, hne, hmN, rfl⟩
      · have h1 : (⟨coeffEmb Kb (algebraMap ℚ (LaurentSeries ℚ) c), hz'⟩ : modularFunctionFieldBar N)
            = algebraMap Kb (modularFunctionFieldBar N) (algebraMap ℚ Kb c) :=
          Subtype.ext (coeffEmb_algebraMap c)
        rw [h1, ← (phi N d p hdp).commutes (algebraMap ℚ Kb c)]
        exact A.algebraMap_mem _
      · haveI := hne
        rw [lit_jd N m hmN]
        exact hJm m hmN
    | one =>
      intro hz'
      rw [show (⟨coeffEmb Kb 1, hz'⟩ : modularFunctionFieldBar N) = 1 from Subtype.ext (map_one _)]
      exact one_mem _
    | add x y hx hy ihx ihy =>
      intro hz'
      have hx' := coeffEmb_mem_laurentBaseChange Kb (F₀ := modularFunctionFieldFull N) hx
      have hy' := coeffEmb_mem_laurentBaseChange Kb (F₀ := modularFunctionFieldFull N) hy
      rw [show (⟨coeffEmb Kb (x + y), hz'⟩ : modularFunctionFieldBar N) = ⟨_, hx'⟩ + ⟨_, hy'⟩ from
        Subtype.ext (map_add _ _ _)]
      exact add_mem (ihx hx') (ihy hy')
    | neg x hx ihx =>
      intro hz'
      have hx' := coeffEmb_mem_laurentBaseChange Kb (F₀ := modularFunctionFieldFull N) hx
      rw [show (⟨coeffEmb Kb (-x), hz'⟩ : modularFunctionFieldBar N) = -⟨_, hx'⟩ from Subtype.ext (map_neg _ _)]
      exact neg_mem (ihx hx')
    | inv x hx ihx =>
      intro hz'
      have hx' := coeffEmb_mem_laurentBaseChange Kb (F₀ := modularFunctionFieldFull N) hx
      rw [show (⟨coeffEmb Kb x⁻¹, hz'⟩ : modularFunctionFieldBar N) = (⟨_, hx'⟩)⁻¹ from Subtype.ext (map_inv₀ _ _)]
      exact inv_mem (ihx hx')
    | mul x y hx hy ihx ihy =>
      intro hz'
      have hx' := coeffEmb_mem_laurentBaseChange Kb (F₀ := modularFunctionFieldFull N) hx
      have hy' := coeffEmb_mem_laurentBaseChange Kb (F₀ := modularFunctionFieldFull N) hy
      rw [show (⟨coeffEmb Kb (x * y), hz'⟩ : modularFunctionFieldBar N) = ⟨_, hx'⟩ * ⟨_, hy'⟩ from
        Subtype.ext (map_mul _ _ _)]
      exact mul_mem (ihx hx') (ihy hy')

  have hall : ∀ y : modularFunctionFieldBar N, y ∈ A := by
    intro y
    obtain ⟨x₀, hx₀⟩ := y
    have hy : x₀ ∈ modularFunctionFieldBar N := hx₀
    rw [mem_laurentBaseChange_iff] at hy
    suffices h : ∀ hy' : x₀ ∈ modularFunctionFieldBar N, (⟨x₀, hy'⟩ : modularFunctionFieldBar N) ∈ A from h hx₀
    clear hx₀
    induction hy using Subfield.closure_induction with
    | mem x hx =>
      intro hx'
      rcases hx with ⟨c, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [show (⟨algebraMap Kb (LaurentSeries Kb) c, hx'⟩ : modularFunctionFieldBar N)
          = algebraMap Kb (modularFunctionFieldBar N) c from Subtype.ext rfl, ← (phi N d p hdp).commutes c]
        exact A.algebraMap_mem _
      · exact hrat z hz hx'
    | one =>
      intro hx'
      exact one_mem _
    | add x y hx hy ihx ihy =>
      intro hz'
      rw [show (⟨x + y, hz'⟩ : modularFunctionFieldBar N) = ⟨x, hx⟩ + ⟨y, hy⟩ from rfl]
      exact add_mem (ihx hx) (ihy hy)
    | neg x hx ihx =>
      intro hz'
      rw [show (⟨-x, hz'⟩ : modularFunctionFieldBar N) = -⟨x, hx⟩ from rfl]
      exact neg_mem (ihx hx)
    | inv x hx ihx =>
      intro hz'
      rw [show (⟨x⁻¹, hz'⟩ : modularFunctionFieldBar N) = (⟨x, hx⟩)⁻¹ from rfl]
      exact inv_mem (ihx hx)
    | mul x y hx hy ihx ihy =>
      intro hz'
      rw [show (⟨x * y, hz'⟩ : modularFunctionFieldBar N) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl]
      exact mul_mem (ihx hx) (ihy hy)
  exact fun y => mem_algebraicClosure_iff'.mp (hall y)

private theorem ord_factor (u : Place Kb (modularFunctionFieldBar N)) {d p : ℕ} [NeZero d] [Fact p.Prime]
    (hdp : d * p ∣ N) (hd : d ∣ N) (hneg : u.ord (J N d hd) < 0)
    (hmq : qExpand Kb d (coeffEmb Kb (modularUnitSeries p)) ∈ modularFunctionFieldBar N) :
    u.ord ⟨qExpand Kb d (coeffEmb Kb (modularUnitSeries p)), hmq⟩ = u.ord (J N (d * p) hdp) - u.ord (J N d hd) := by
  set φ := phi N d p hdp with hφdef
  have hφ := phi_isIntegral N hdp
  set w := u.restrictAlong φ hφ with hw
  set e := Place.ramificationIndexAlong φ u with he
  have e1 := Place.ord_restrictAlong φ hφ u
    ⟨coeffEmb Kb (modularUnitSeries p), coeffEmb_mem_laurentBaseChange Kb (modularUnitSeries_mem_modularFunctionFieldFull p)⟩
  have e2 := Place.ord_restrictAlong φ hφ u ⟨coeffEmb Kb jq, coeffEmb_mem_laurentBaseChange Kb (jq_mem_full p)⟩
  have e3 := Place.ord_restrictAlong φ hφ u
    ⟨coeffEmb Kb (qExpand ℚ p jq), coeffEmb_mem_laurentBaseChange Kb (jqd_mem_full p (dvd_refl p))⟩

  have i1 : φ ⟨coeffEmb Kb (modularUnitSeries p),
      coeffEmb_mem_laurentBaseChange Kb (modularUnitSeries_mem_modularFunctionFieldFull p)⟩
        = ⟨qExpand Kb d (coeffEmb Kb (modularUnitSeries p)), hmq⟩ := Subtype.ext rfl
  have i2 : φ ⟨coeffEmb Kb jq, coeffEmb_mem_laurentBaseChange Kb (jq_mem_full p)⟩ = J N d hd :=
    Subtype.ext (by show qExpand Kb d (coeffEmb Kb jq) = qExpand Kb d (jqModC Kb); rw [coeffEmb_jq])
  have i3 : φ ⟨coeffEmb Kb (qExpand ℚ p jq), coeffEmb_mem_laurentBaseChange Kb (jqd_mem_full p (dvd_refl p))⟩
      = J N (d * p) hdp :=
    Subtype.ext (by
      show qExpand Kb d (coeffEmb Kb (qExpand ℚ p jq)) = qExpand Kb (d * p) (jqModC Kb)
      rw [coeffEmb_qExpand_jq, qExpand_qExpand p d])
  rw [i1] at e1
  rw [i2] at e2
  rw [i3] at e3

  have hwneg : w.ord ⟨coeffEmb Kb jq, coeffEmb_mem_laurentBaseChange Kb (jq_mem_full p)⟩ < 0 := by
    by_contra h
    rw [not_lt] at h
    have : (0 : ℤ) ≤ (e : ℤ) * w.ord ⟨coeffEmb Kb jq, coeffEmb_mem_laurentBaseChange Kb (jq_mem_full p)⟩ :=
      mul_nonneg (Nat.cast_nonneg _) h
    rw [← e2] at this
    exact absurd hneg (not_lt.mpr this)
  have hprime := prime_level p w hwneg
  rw [e1, e2, e3, hprime]
  ring

end Along

section Telescope

variable (N : ℕ) [NeZero N]

private theorem modularUnitSeries_mul (d p : ℕ) [NeZero d] [NeZero p] [NeZero (d * p)] :
    modularUnitSeries (d * p) = modularUnitSeries d * qExpand ℚ d (modularUnitSeries p) := by
  have h0 : qExpand ℚ d deltaSeries ≠ 0 := fun h =>
    deltaSeries_ne_zero ((injective_iff_map_eq_zero _).mp (qExpand_injective d) _ h)
  unfold modularUnitSeries deltaSeriesN
  rw [map_mul, map_inv₀, qExpand_qExpand p d, mul_assoc, ← mul_assoc (qExpand ℚ d deltaSeries)⁻¹,
    inv_mul_cancel₀ h0, one_mul]

private theorem main (u : Place Kb (modularFunctionFieldBar N)) (hpole : u.ord (J N 1 (one_dvd N)) < 0) (δ : ℕ) :
    ∀ [NeZero δ] (hδ : δ ∣ N) (hmem : coeffEmb Kb (modularUnitSeries δ) ∈ modularFunctionFieldBar N),
      u.ord ⟨coeffEmb Kb (modularUnitSeries δ), hmem⟩ = u.ord (J N δ hδ) - u.ord (J N 1 (one_dvd N)) := by
  induction δ using Nat.strong_induction_on with
  | _ δ ih =>
    intro _ hδ hmem
    rcases Nat.lt_or_ge 1 δ with hδ1 | hδ1
    · obtain ⟨p, hp, d, hdp⟩ : ∃ p : ℕ, p.Prime ∧ ∃ d : ℕ, δ = d * p := by
        obtain ⟨p, hp, k, hk⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt hδ1)
        exact ⟨p, hp, k, by rw [hk, mul_comm]⟩
      subst hdp
      haveI : Fact p.Prime := ⟨hp⟩
      haveI : NeZero d := ⟨fun h => NeZero.ne (d * p) (by rw [h, zero_mul])⟩
      have hdlt : d < d * p := lt_mul_of_one_lt_right (Nat.pos_of_ne_zero (NeZero.ne d)) hp.one_lt
      have hd : d ∣ N := (Dvd.intro p rfl).trans hδ

      have hm1 : coeffEmb Kb (modularUnitSeries d) ∈ modularFunctionFieldBar N :=
        coeffEmb_mem_laurentBaseChange Kb (full_degeneracy_le hd (modularUnitSeries_mem_modularFunctionFieldFull d))
      have hm2q : qExpand ℚ d (modularUnitSeries p) ∈ modularFunctionFieldFull N := by
        have hmap : qExpandₐ d (modularUnitSeries p) ∈ (modularFunctionFieldFull p).map (qExpandₐ d) := by
          rw [← SetLike.mem_coe, IntermediateField.coe_map]
          exact Set.mem_image_of_mem _ (modularUnitSeries_mem_modularFunctionFieldFull p)
        have h1 : qExpand ℚ d (modularUnitSeries p) ∈ modularFunctionFieldFull (p * d) := full_degeneracy_map_le p d hmap
        exact full_degeneracy_le (by rw [mul_comm]; exact hδ) h1
      have hm2 : qExpand Kb d (coeffEmb Kb (modularUnitSeries p)) ∈ modularFunctionFieldBar N := by
        rw [← coeffEmb_qExpand]
        exact coeffEmb_mem_laurentBaseChange Kb hm2q
      have hsplit : (⟨coeffEmb Kb (modularUnitSeries (d * p)), hmem⟩ : modularFunctionFieldBar N)
          = ⟨coeffEmb Kb (modularUnitSeries d), hm1⟩ * ⟨qExpand Kb d (coeffEmb Kb (modularUnitSeries p)), hm2⟩ := by
        apply Subtype.ext
        show coeffEmb Kb (modularUnitSeries (d * p)) = coeffEmb Kb (modularUnitSeries d) * qExpand Kb d (coeffEmb Kb _)
        rw [modularUnitSeries_mul d p, map_mul, coeffEmb_qExpand]
      have hz1 : (⟨coeffEmb Kb (modularUnitSeries d), hm1⟩ : modularFunctionFieldBar N) ≠ 0 := fun h =>
        modularUnitSeries_ne_zero d
          ((map_eq_zero_iff (coeffEmb Kb) (coeffEmb Kb).injective).mp (congrArg Subtype.val h))
      have hz2 : (⟨qExpand Kb d (coeffEmb Kb (modularUnitSeries p)), hm2⟩ : modularFunctionFieldBar N) ≠ 0 := fun h =>
        modularUnitSeries_ne_zero p
          ((map_eq_zero_iff (coeffEmb Kb) (coeffEmb Kb).injective).mp
            ((map_eq_zero_iff (qExpand Kb d) (qExpand_injective d)).mp (congrArg Subtype.val h)))

      haveI : NeZero (1 * d) := ⟨by rw [one_mul]; exact NeZero.ne d⟩
      obtain ⟨-, -, -, -, hneg⟩ := chain N u d 1 (one_dvd N) (by rw [one_mul]; exact hd) hpole
      rw [J_congr N _ hd (one_mul d)] at hneg
      rw [hsplit, u.ord_mul hz1 hz2, ih d hdlt hd hm1, ord_factor N u hδ hd hneg hm2]
      ring
    · have hδ0 : δ = 1 := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hδ1 with h | h
        · exact absurd h (NeZero.ne δ)
        · exact h
      subst hδ0
      have h1 : modularUnitSeries 1 = 1 := by
        unfold modularUnitSeries deltaSeriesN
        rw [qExpand_one_apply, mul_inv_cancel₀ deltaSeries_ne_zero]
      have h2 : (⟨coeffEmb Kb (modularUnitSeries 1), hmem⟩ : modularFunctionFieldBar N) = 1 :=
        Subtype.ext (by show coeffEmb Kb (modularUnitSeries 1) = 1; rw [h1, map_one])
      rw [h2, u.ord_one, sub_self]

end Telescope

end ModularUnitOrder

open ModularUnitOrder in
theorem solution
    (N : ℕ) [NeZero N]
    (u : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hpole : u.ord ⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full N (jq_mem N))⟩ < 0) :
    ∀ (δ : ℕ) [NeZero δ] (hδ : δ ∣ N)
      (hmem : modularUnitSeries δ ∈ modularFunctionFieldFull N),
      u.ord ⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries δ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hmem⟩
        = u.ord ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ δ jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N hδ)⟩
          - u.ord ⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ := by
  intro δ _ hδ hmem
  rw [ModularUnitOrder.lit_j N] at hpole
  rw [ModularUnitOrder.lit_j N, ModularUnitOrder.lit_jd N δ hδ]
  exact ModularUnitOrder.main N u hpole δ hδ (coeffEmb_mem_laurentBaseChange _ hmem)

end

end S_ModularCurve_ord_coeffEmb_modularUnitSeries_eq_sub_of_ord_jqModC_neg
end P2MW
export P2MW.S_ModularCurve_ord_coeffEmb_modularUnitSeries_eq_sub_of_ord_jqModC_neg (solution)
