-- Prove2me | solution 1 for GlobalTheory.NearZeroDeriv.exists_large_derSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:02:26.82746+00:00
-- url     : https://prove2.me/submissions/6272a139-54a9-46d7-a407-9853ba47a84e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsBoundRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZerosStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TuranSecondMainTheoremPowerSumsUnitCoefficientsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsLargeVonMangoldtLogPowerSeriesNearZero
import Theorems.Thm_GlobalTheory_NearZeroDeriv_power_sum_large
import Theorems.Thm_GlobalTheory_NearZeroDeriv_re_lt_one
import Theorems.Thm_GlobalTheory_NearZeroDeriv_inv_sq_le_re
import Theorems.Thm_GlobalTheory_NearZeroDeriv_norm_derSeries_zero_le
import Theorems.Thm_GlobalTheory_GoodHeight_one_le_order
import Theorems.Thm_GlobalTheory_T_iteratedDeriv_logDeriv_dirichletL_via_nearby_zeros
import Theorems.Thm_GlobalTheory_T_turan_second_main_theorem_power_sums_unit_coefficients


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.NearZeroDeriv
namespace GlobalTheory.NearZeroDeriv
theorem _root_.solution : ∃ A C r₀ : ℝ, 1 ≤ A ∧ 0 < C ∧ 0 < r₀ ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (τ r L : ℝ) (K : ℕ) (ρ : ℂ), (χ ≠ 1 ∨ 2 ≤ |τ|) → Real.log (q * (|τ| + 2)) ≤ L → 1 / L ≤ r → r ≤ r₀ → C * r * L ≤ K → LFunction χ ρ = 0 → ‖ρ - (1 + τ * I)‖ ≤ r → ∃ k : ℕ, K ≤ k ∧ k ≤ 2 * K ∧ 1 / (A * r) ^ (k + 1) ≤ ‖derSeries (fun n : ℕ => χ (n : ZMod q)) k ((1 + r : ℝ) + τ * I)‖ := by
  obtain ⟨C₁, hC₁, H⟩ := GlobalTheory.T.iteratedDeriv_logDeriv_dirichletL_via_nearby_zeros
  obtain ⟨T, hT1, hT⟩ := GlobalTheory.T.turan_second_main_theorem_power_sums_unit_coefficients
  refine ⟨8 * T, 4 * (8 * T) ^ 2 * (2 * C₁ + 2), 1 / (8 * T), by linarith, by positivity,
    by positivity, ?_⟩
  intro q _ χ τ r L K ρ hχ hL hLr hr0 hK hρ hd
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have hlog : 0 < Real.log (q * (|τ| + 2)) := Real.log_pos (by nlinarith [abs_nonneg τ])
  have hLp : 0 < L := hlog.trans_le hL
  have hr : 0 < r := lt_of_lt_of_le (by positivity) hLr
  have hTr : 8 * T * r ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hr0; linarith
  have hr8 : r ≤ 1 / 8 := by nlinarith
  have hrL : 1 ≤ r * L := by rwa [div_le_iff₀ hLp] at hLr
  have hL1 : 1 ≤ L := by nlinarith
  have hrL' : 1 / r ≤ L := by rw [div_le_iff₀ hr]; linarith
  set s : ℂ := ((1 + r : ℝ) : ℂ) + τ * I with hs
  have hfin := (H q χ (1 + r) τ 0 (by linarith) (by linarith)).1
  set Z := hfin.toFinset with hZ
  have hre : ∀ w ∈ Z, r ≤ (s - w).re := fun w hw => by
    have := re_lt_one ((Set.Finite.mem_toFinset _).1 hw)
    simp [hs]; linarith
  have hne : ∀ w ∈ Z, s - w ≠ 0 := fun w hw h => by
    have := hre w hw
    rw [h] at this; simp at this; linarith
  have key : ∀ k : ℕ, ‖∑ w ∈ Z, (ord χ w : ℂ) / (s - w) ^ (k + 1)‖ ≤
      ‖derSeries (fun n : ℕ => χ (n : ZMod q)) k s‖ + (1 + C₁) * L := fun k => by
    have h := (H q χ (1 + r) τ k (by linarith) (by linarith)).2.2
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, ← hs, ← hZ] at h
    have h1 : C₁ * Real.log (q * (|τ| + 2)) / (1 + r) ^ k ≤ C₁ * L :=
      (div_le_self (by positivity) (one_le_pow₀ (by linarith))).trans (by gcongr)
    have h2 : ‖(if χ = 1 then 1 / (s - 1) ^ (k + 1) else 0 : ℂ)‖ ≤ 1 := by
      split_ifs with h1
      · have h3 : 2 ≤ |τ| := hχ.resolve_left (not_not.2 h1)
        have h4 : |τ| ≤ ‖s - 1‖ := by simpa [hs] using Complex.abs_im_le_norm (s - 1)
        rw [norm_div, norm_one, norm_pow]
        exact div_le_one_of_le₀ (one_le_pow₀ (by linarith)) (by positivity)
      · simp
    generalize (if χ = 1 then 1 / (s - 1) ^ (k + 1) else 0 : ℂ) = P at h h2
    generalize (∑ w ∈ Z, (ord χ w : ℂ) / (s - w) ^ (k + 1)) = S at h ⊢
    generalize derSeries (fun n : ℕ => χ (n : ZMod q)) k s = D at h ⊢
    have e : S = (D - P + S) - D + P := by ring
    have := norm_add_le ((D - P + S) - D) P
    have := norm_sub_le (D - P + S) D
    rw [e]; nlinarith
  have hD0 : ‖derSeries (fun n : ℕ => χ (n : ZMod q)) 0 s‖ ≤ 1 / r + C₁ := by
    refine (norm_derSeries_zero_le _ (fun n => χ.norm_le_one _) (1 + r) τ (by linarith)).trans ?_
    obtain ⟨hf, -, h⟩ := H 1 1 (1 + r) 0 0 (by linarith) (by linarith)
    rw [finsum_mem_eq_finite_toFinset_sum _ hf, if_pos rfl] at h
    have h1 := (Complex.re_le_norm _).trans h
    rw [Complex.add_re, Complex.sub_re, Complex.re_sum] at h1
    have h2 : 0 ≤ ∑ w ∈ hf.toFinset, ((ord (1 : DirichletCharacter ℂ 1) w : ℂ) /
        (((1 + r : ℝ) : ℂ) + (0 : ℝ) * I - w) ^ (0 + 1)).re := by
      refine Finset.sum_nonneg fun w hw => ?_
      have := re_lt_one ((Set.Finite.mem_toFinset _).1 hw)
      rw [zero_add, pow_one]
      refine le_trans (by simp) (inv_sq_le_re (r := 0) _ ?_)
      simp; linarith
    have h3 : (1 / (((1 + r : ℝ) : ℂ) + (0 : ℝ) * I - 1) ^ (0 + 1)).re = 1 / r := by
      have : (1 / (((1 + r : ℝ) : ℂ) + (0 : ℝ) * I - 1) ^ (0 + 1)) = ((1 / r : ℝ) : ℂ) := by
        simp
      rw [this, Complex.ofReal_re]
    have h4 : C₁ * Real.log (((1 : ℕ) : ℝ) * (|(0 : ℝ)| + 2)) / (1 + r) ^ 0 ≤ C₁ := by
      have := Real.log_two_lt_d9
      simp only [Nat.cast_one, abs_zero, zero_add, one_mul, pow_zero, div_one]
      nlinarith
    linarith
  have hB : ∑ w ∈ Z, (ord χ w : ℝ) / ‖s - w‖ ^ 2 ≤ (2 * C₁ + 2) * r * L / r ^ 2 := by
    have h1 : r * ∑ w ∈ Z, (ord χ w : ℝ) / ‖s - w‖ ^ 2 ≤ (2 * C₁ + 2) * L := by
      have h := key 0
      simp only [zero_add, pow_one] at h
      have h2 := (Complex.re_le_norm _).trans h
      rw [Complex.re_sum] at h2
      rw [Finset.mul_sum]
      refine (Finset.sum_le_sum fun w hw => inv_sq_le_re _ (hre w hw)).trans (h2.trans ?_)
      nlinarith
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hρ1 : ρ ≠ 1 := by
    rintro rfl
    rcases hχ with h | h
    · exact LFunction_apply_one_ne_zero h hρ
    · have : |τ| ≤ r := by simpa using hd
      linarith
  have hρZ : ρ ∈ Z := by
    refine (Set.Finite.mem_toFinset _).2 ⟨?_, Or.inr hρ1, hρ⟩
    have e : ρ - (2 + τ * I) = (ρ - (1 + τ * I)) - 1 := by ring
    have := norm_sub_le (ρ - (1 + τ * I)) 1
    rw [e]; rw [norm_one] at this; linarith
  have hd' : ‖s - ρ‖ ≤ 2 * r := by
    have e : s - ρ = (r : ℂ) - (ρ - (1 + τ * I)) := by rw [hs]; push_cast; ring
    have := norm_sub_le (r : ℂ) (ρ - (1 + τ * I))
    rw [Complex.norm_real, Real.norm_of_nonneg hr.le] at this
    rw [e]; linarith
  obtain ⟨j, h1, h2, h3⟩ := power_sum_large hT1 hT Z (ord χ) s r _ K hr hne hB
    (by linarith) ρ hρZ (GlobalTheory.GoodHeight.one_le_order χ hρ1 hρ) hd'
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  refine ⟨k, by omega, by omega, ?_⟩
  have h4 := key k
  set x := 1 / (4 * T * r) with hx
  have hx2 : 2 ≤ x := by rw [hx, le_div_iff₀ (by positivity)]; linarith
  have h5 : (1 + C₁) * L ≤ 1 / 4 * x ^ (k + 1) := by
    have a : (K : ℝ) ≤ x ^ k := by
      have : K ≤ 2 ^ k := le_trans (by omega) (Nat.lt_two_pow_self (n := k)).le
      have : (K : ℝ) ≤ 2 ^ k := by exact_mod_cast this
      exact this.trans (by gcongr)
    have b : 4 * (8 * T) ^ 2 * (2 * C₁ + 2) * r * L * x = 128 * T * ((1 + C₁) * L) := by
      rw [hx]; field_simp; ring
    have c : 4 * (8 * T) ^ 2 * (2 * C₁ + 2) * r * L * x ≤ x ^ k * x :=
      mul_le_mul_of_nonneg_right (hK.trans a) (by linarith)
    have d : 0 ≤ (1 + C₁) * L := by positivity
    rw [pow_succ]
    nlinarith
  have h6 : 1 / (8 * T * r) ^ (k + 1) ≤ 1 / 2 * x ^ (k + 1) := by
    have e : 1 / (8 * T * r) = 1 / 2 * x := by rw [hx]; field_simp; ring
    rw [← one_div_pow, e, mul_pow]
    gcongr
    exact pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
  linarith
end GlobalTheory.NearZeroDeriv
