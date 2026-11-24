-- Prove2me | solution 1 for OAI.OddGoldbach.odd_sum_le_25_primes
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-24T11:02:57.78598+00:00
-- url     : https://prove2.me/submissions/2e9b3af7-c5c8-4ec8-bcfa-87ed00efecd0

import Mathlib
import Definitions.Def_Schnir_defs
import Theorems.Thm_PrimePairSieve_sieve_constants_certificate
import Theorems.Thm_TaoFivePrimes_siebert_prime_pair_bound
import Definitions.Def_TaoFivePrimes_SingularSeries
import Theorems.Thm_RV27_interval_goldbach_bound
import Theorems.Thm_RV27_interval_pair_weight_lower
import Theorems.Thm_Schnir_basis_of_density

namespace Chebyshev
open Real

theorem Ioc_eq_Icc {n : ℕ} : Finset.Ioc 0 n = Finset.Icc 1 n := by
  ext; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega

theorem log3_bounds : 1.0986 ≤ Real.log 3 ∧ Real.log 3 ≤ 1.0987 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (1/4 : ℝ)) (by norm_num [abs_of_pos]) 8
  have e : Real.log (1 - 1/4 : ℝ) = Real.log 3 - 2 * Real.log 2 := by
    rw [show (1 - 1/4 : ℝ) = 3 / 2 ^ 2 by norm_num, Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring
  rw [e] at h
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_two_lt_d9
  norm_num [Finset.sum_range_succ, abs_le] at h
  constructor <;> nlinarith [h.1, h.2]

theorem log5_bounds : 1.60943 ≤ Real.log 5 ∧ Real.log 5 ≤ 1.60944 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (1/5 : ℝ)) (by norm_num [abs_of_pos]) 8
  have e : Real.log (1 - 1/5 : ℝ) = 2 * Real.log 2 - Real.log 5 := by
    rw [show (1 - 1/5 : ℝ) = 2 ^ 2 / 5 by norm_num, Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring
  rw [e] at h
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_two_lt_d9
  norm_num [Finset.sum_range_succ, abs_le] at h
  constructor <;> nlinarith [h.1, h.2]


open Real Finsupp Finset
open ArithmeticFunction hiding log

attribute [local fun_prop] DifferentiableAt.differentiableWithinAt

noncomputable def T (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, log n

theorem T.le (x : ℝ) (hx : 1 ≤ x) : T x ≤ x * log x - x + 1 + log x := by
  rw [T, ← Ico_insert_right <| Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr hx).ne',
    sum_insert right_notMem_Ico]
  have : MonotoneOn log (Set.Icc (1 : ℕ) ⌊x⌋₊) :=
    fun a ha _ _ hab ↦ log_le_log (lt_of_lt_of_le one_pos (by grind)) hab
  have : ∑ n ∈ Finset.Ico 1 ⌊x⌋₊, log n ≤ ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 :=
    calc ∑ n ∈ Finset.Ico 1 ⌊x⌋₊, log n
        ≤ ∫ t in (1 : ℕ)..(⌊x⌋₊ : ℕ), log t := this.sum_le_integral_Ico <|
          Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr hx).ne'
      _ = ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by simp
  have h1 : (1 : ℝ) ≤ ⌊x⌋₊ := by simp_all
  have h3 : ∀ t ∈ interior (Set.Ici 1), DifferentiableWithinAt ℝ (_root_.id * log - _root_.id) (interior (Set.Ici 1)) t := by
    intro t ht
    simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at ht
    fun_prop ( disch := positivity )
  have h4 : ∀ t ∈ interior (Set.Ici 1), 0 ≤ deriv (fun t ↦ t * log t - t) t := by
    intro t ht
    simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at ht
    have : DifferentiableAt ℝ (fun t ↦ t * log t) t := by fun_prop ( disch := positivity )
    have hderiv : deriv (fun t ↦ t * log t - t) t = log t := by
      simp [show (fun t ↦ t * log t - t) = (fun t ↦ t * log t) - _root_.id by rfl,
        deriv_sub this differentiableAt_id, deriv_mul_log (by linarith)]
    exact hderiv ▸ log_nonneg (le_of_lt ht)
  have h5 : ContinuousOn (fun t ↦ t * log t - t) (Set.Ici 1) := by fun_prop
  have h2 : MonotoneOn (fun t ↦ t * log t - t) (Set.Ici 1) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 1) h5 h3 h4
  have : (⌊x⌋₊ : ℝ) * log ⌊x⌋₊ - ⌊x⌋₊ ≤ x * log x - x := by
    exact h2 (Set.mem_Ici.mpr h1) (Set.mem_Ici.mpr hx) <| Nat.floor_le (by grind)
  linarith [log_le_log (by positivity) <| Nat.floor_le (by linarith)]

theorem T.ge (x : ℝ) (hx : 1 ≤ x) : T x ≥ x * log x - x + 1 - log x := by
  have hone_le_floor : 1 ≤ ⌊x⌋₊ := Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr hx).ne'
  simp only [T, ← Ico_insert_right hone_le_floor, sum_insert right_notMem_Ico]
  have mono_log : MonotoneOn log (Set.Icc (1 : ℕ) ⌊x⌋₊) := fun a ha _ _ hab ↦
    log_le_log (lt_of_lt_of_le one_pos (by simpa using ha.1)) hab
  have h1 : ∀ n ≥ 1, ∑ i ∈ Ico 1 n, log (i + 1 : ℕ) = log n + ∑ i ∈ Ico 1 n, log i := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih => grind [Nat.Ico_succ_right_eq_insert_Ico]
  have sum_shift : ∑ i ∈ Ico 1 ⌊x⌋₊, log (i + 1 : ℕ) = log ⌊x⌋₊ + ∑ i ∈ Ico 1 ⌊x⌋₊, log i := by
    exact h1 ⌊x⌋₊ hone_le_floor
  have int_le_T : ∫ t in (1 : ℕ)..(⌊x⌋₊ : ℕ), log t ≤ log ⌊x⌋₊ + ∑ n ∈ Ico 1 ⌊x⌋₊, log n := by
    linarith [mono_log.integral_le_sum_Ico hone_le_floor]
  have int_eq : ∫ t in (1 : ℕ)..(⌊x⌋₊ : ℕ), log t = ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by simp
  have h2 : ∫ t in (⌊x⌋₊ : ℝ)..x, log t ≤ (x - ⌊x⌋₊) * log x := by
    calc ∫ t in (⌊x⌋₊ : ℝ)..x, log t
      ≤ ∫ _ in (⌊x⌋₊ : ℝ)..x, log x := (intervalIntegral.integral_mono_on (Nat.floor_le <| by linarith) intervalIntegral.intervalIntegrable_log'
            intervalIntegrable_const fun t ht ↦ log_le_log (lt_of_lt_of_le (by positivity) ht.1) ht.2)
      _ = (x - ⌊x⌋₊) * log x := by simp
  have target_le_int : x * log x - x + 1 - log x ≤ ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by
    calc x * log x - x + 1 - log x
        ≤ (x * log x - x + 1) - (x - ⌊x⌋₊) * log x := by nlinarith [log_nonneg hx, Nat.lt_floor_add_one x]
      _ ≤ (x * log x - x + 1) - ∫ t in (⌊x⌋₊ : ℝ)..x, log t := by grind
      _ = ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by grind [integral_log]
  linarith

theorem T.eq_sum_Lambda (x : ℝ) : T x = ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * ⌊x / n⌋₊ := by
  unfold T
  simp_rw [← log_apply, ← vonMangoldt_mul_zeta]
  rw [← Ioc_eq_Icc, sum_Ioc_mul_zeta_eq_sum]
  simp [Nat.floor_div_natCast]

noncomputable def E (ν : ℕ →₀ ℝ) (x : ℝ) : ℝ := ν.sum (fun m w ↦ w * ⌊ x / m ⌋₊)

theorem T.weighted_eq_sum (ν : ℕ →₀ ℝ) (x : ℝ) : ν.sum (fun m w ↦ w * T (x/m)) = ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * E ν (x/n) := by
  simp_rw [T.eq_sum_Lambda, E, Finsupp.mul_sum]
  rw [← sum_finsetSum_comm]
  apply Finsupp.sum_congr fun y hy ↦ ?_
  rw [Finset.mul_sum]
  by_cases hy : y = 0
  · simp [hy]
  have one_le_y : 1 ≤ (y : ℝ) := by grind [Nat.one_le_cast]
  by_cases hx : x < 1
  · simp [hx, show x / y < 1 from div_lt_one (by linarith)|>.mpr (by linarith)]
  apply sum_subset_zero_on_sdiff
  · apply Icc_subset_Icc_right
    gcongr
    exact div_le_self (by linarith) one_le_y
  · intro t ht
    simp only [mem_sdiff, mem_Icc, not_and, not_le] at ht
    simp only [mul_eq_zero, Nat.cast_eq_zero, Nat.floor_eq_zero]
    right
    right
    apply div_lt_one (by linarith)|>.mpr
    have := ht.2 ht.1.1
    apply div_lt_iff₀ (by simp; grind)|>.mpr
    rw [Nat.floor_lt <| div_nonneg (by linarith) (by linarith)] at this
    have := div_lt_iff₀ (by linarith)|>.mp this
    rwa [mul_comm] at this
  · grind

open Finsupp in
noncomputable def ν : ℕ →₀ ℝ := single 1 1 - single 2 1 - single 3 1 - single 5 1 + single 30 1

/-- The support of `ν` is `{1, 2, 3, 5, 30}`. Used whenever we need to unfold `ν.sum`. -/
private lemma ν_support : ν.support = {1, 2, 3, 5, 30} := by
  norm_num [ν, Finset.ext_iff]; grind

/-- Unfold `ν.sum (fun m w ↦ w * f m)` into its five-term expansion.
This avoids repeating the `sum_add_index` / `sum_sub_index` chain every time
we need to compute a `ν`-weighted sum. -/
private lemma ν_sum_mul (f : ℕ → ℝ) :
    ν.sum (fun m w ↦ w * f m) = f 1 - f 2 - f 3 - f 5 + f 30 := by
  rw [ν, sum_add_index (by simp) (by intros; ring)]
  grind only [sum_single_index, sum_sub_index]

/-- Unfold `E ν y` into an explicit expression in terms of floors of `y / k`.
This is the key formula repeatedly used to analyse `E ν`. -/
private lemma E_nu_expand (y : ℝ) :
    E ν y = ⌊y⌋₊ - ⌊y / 2⌋₊ - ⌊y / 3⌋₊ - ⌊y / 5⌋₊ + ⌊y / 30⌋₊ := by
  rw [E, ν, sum_add_index' (by grind) (by grind)]
  grind [sum_single_index, sum_sub_index]

/-- The classical sandwich `k * ⌊y/k⌋₊ ≤ ⌊y⌋₊ < k * ⌊y/k⌋₊ + k` for `k ≥ 1` and `y ≥ 0`. -/
private lemma floor_div_bounds {y : ℝ} (hy : 0 ≤ y) {k : ℕ} (hk : 1 ≤ k) :
    k * ⌊y / k⌋₊ ≤ ⌊y⌋₊ ∧ ⌊y⌋₊ < k * ⌊y / k⌋₊ + k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hdivnn : 0 ≤ y / k := div_nonneg hy hk'.le
  refine ⟨Nat.le_floor ?_, ?_⟩
  · push_cast
    have := Nat.floor_le hdivnn
    calc ((k : ℝ) * ⌊y / k⌋₊) = k * (y / k) - k * (y / k - ⌊y / k⌋₊) := by ring
      _ ≤ k * (y / k) := by nlinarith [Nat.floor_le hdivnn]
      _ = y := mul_div_cancel₀ _ hk'.ne'
  · have hlt : y / k < ⌊y / k⌋₊ + 1 := Nat.lt_floor_add_one (y / k)
    have hy_lt : y < (k : ℝ) * (⌊y / k⌋₊ + 1) := by linarith [(div_lt_iff₀ hk').mp hlt]
    have : (⌊y⌋₊ : ℝ) < (k : ℝ) * (⌊y / k⌋₊ + 1) := (Nat.floor_le hy).trans_lt hy_lt
    exact_mod_cast this

theorem nu_sum_div_eq_zero : ν.sum (fun n w ↦ w / n) = 0 := by
  norm_num [ν, add_div, sum_add_index', sub_div, sum_sub_index]

theorem E_nu_eq_one (x : ℝ) (hx : x ∈ Set.Ico 1 6) : E ν x = 1 := by
  obtain ⟨h1, h6⟩ := hx
  have hx0 : (0 : ℝ) ≤ x := by linarith
  simp only [E_nu_expand, Nat.floor_eq_zero.mpr (by linarith : x / 30 < 1)]
  have hflb : 1 ≤ ⌊x⌋₊ := by rwa [Nat.one_le_floor_iff]
  have hfub : ⌊x⌋₊ ≤ 5 := Nat.lt_succ_iff.mp (Nat.floor_lt' (by grind) |>.mpr h6)
  have h2 := floor_div_bounds hx0 (k := 2) (by norm_num)
  have h3 := floor_div_bounds hx0 (k := 3) (by norm_num)
  have h5 := floor_div_bounds hx0 (k := 5) (by norm_num)
  push_cast at h2 h3 h5
  rw [show ⌊x⌋₊ = ⌊x / 2⌋₊ + ⌊x / 3⌋₊ + ⌊x / 5⌋₊ + 1 by omega]
  grind

theorem E_nu_period (x : ℝ) (hx : x ≥ 0) : E ν (x + 30) = E ν x := by
  have h (k : ℝ) : (x + 30) / k = x / k + (30 / k) := by ring
  simp_rw [E_nu_expand, h 2, h 3, h 5, h 30]
  norm_num
  repeat rw [Nat.floor_add_ofNat (by positivity)]
  rw [Nat.floor_add_one (by positivity)]
  grind

theorem E_nu_bound (x : ℝ) (hx : x ≥ 0) : 0 ≤ E ν x ∧ E ν x ≤ 1 := by
  have : ∀ y, 0 ≤ y → y < 30 → 0 ≤ E ν y ∧ E ν y ≤ 1 := fun y hy0 hy30 ↦ by
    simp only [E_nu_expand, Nat.floor_eq_zero.mpr (by linarith : y / 30 < 1), Nat.cast_zero, add_zero]
    have h2 := floor_div_bounds hy0 (k := 2) (by norm_num)
    have h3 := floor_div_bounds hy0 (k := 3) (by norm_num)
    have h5 := floor_div_bounds hy0 (k := 5) (by norm_num)
    push_cast at h2 h3 h5
    have hfy : ⌊y⌋₊ < 30 := Nat.floor_lt' (by norm_num) |>.mpr (by exact_mod_cast hy30)
    have hlb : ⌊y/2⌋₊ + ⌊y/3⌋₊ + ⌊y/5⌋₊ ≤ ⌊y⌋₊ := by omega
    have hub : ⌊y⌋₊ ≤ ⌊y/2⌋₊ + ⌊y/3⌋₊ + ⌊y/5⌋₊ + 1 := by omega
    have hlb' : ((⌊y/2⌋₊ + ⌊y/3⌋₊ + ⌊y/5⌋₊ : ℕ) : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hlb
    have hub' : ((⌊y⌋₊ : ℕ) : ℝ) ≤ ((⌊y/2⌋₊ + ⌊y/3⌋₊ + ⌊y/5⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hub
    push_cast at hlb' hub'
    refine ⟨by linarith, by linarith⟩
  let y := x - ⌊x / 30⌋₊ * 30
  have hy : 0 ≤ y ∧ y < 30 := ⟨by linarith [Nat.floor_le (by positivity : 0 ≤ x/30)], by
    linarith [Nat.lt_floor_add_one (x/30)]⟩
  have hxy : E ν x = E ν y := by
    have : x = y + ⌊x/30⌋₊ * 30 := by ring
    rw [this]; induction ⌊x/30⌋₊ with
    | zero => simp
    | succ n ih => simp [add_mul, ← add_assoc, E_nu_period _ (by linarith : y + n * 30 ≥ 0), ih]
  exact hxy ▸ this y hy.1 hy.2

noncomputable def U (x : ℝ) : ℝ := ν.sum (fun m w ↦ w * T (x/m))

theorem psi_ge_weighted (x : ℝ) (hx : x > 0) : ψ x ≥ U x := by
  unfold U psi
  rw [T.weighted_eq_sum, ← Ioc_eq_Icc]
  gcongr with i
  have := E_nu_bound (x / i) (div_nonneg hx.le (by simp))
  grw [this.2, mul_one]

theorem psi_diff_le_weighted (x : ℝ) (hx : x > 0) : ψ x - ψ (x / 6) ≤ U x := by
  unfold U psi
  rw [T.weighted_eq_sum, ← Ioc_eq_Icc]
  have subset : Ioc 0 ⌊x / 6⌋₊ ⊆ Ioc 0 ⌊x⌋₊ := by
    apply Ioc_subset_Ioc_right
    gcongr
    exact div_le_self hx.le (by norm_num)
  rw [← sum_sdiff_eq_sub subset, ← sum_sdiff subset]
  refine le_add_of_le_of_nonneg (sum_le_sum fun n hn ↦ ?_) (sum_nonneg fun n hn ↦ mul_nonneg vonMangoldt_nonneg ?_)
  · rw [E_nu_eq_one, mul_one]
    simp_all only [gt_iff_lt, Finset.mem_sdiff, Finset.mem_Ioc, not_and, not_le, Set.mem_Ico]
    refine ⟨one_le_div (by simp; grind)|>.mpr <| Nat.le_floor_iff hx.le |>.mp hn.1.2, ?_⟩
    have := hn.2 hn.1.1
    apply div_lt_iff₀ (by simp; grind)|>.mpr
    rw [Nat.floor_lt <| div_nonneg (by linarith) (by linarith)] at this
    have := div_lt_iff₀ (by linarith)|>.mp this
    rwa [mul_comm] at this
  · exact E_nu_bound _ (div_nonneg hx.le (by simp))|>.1

noncomputable def a : ℝ := - ν.sum (fun m w ↦ w * log m / m)

lemma a_simpl : a = (7/15) * Real.log 2 + (3/10) * Real.log 3 + (1/6) * Real.log 5 := by
  norm_num [a, Finsupp.sum, single_apply, ν_support]
  norm_num [Finset.sum, ν]
  grind [show (30 : ℝ) = 2 * 3 * 5 by ring, log_mul, log_mul]

theorem a_bound : a ∈ Set.Icc 0.9212 0.9214 := by
  norm_num [Chebyshev.a_simpl]
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, log3_bounds.1, log3_bounds.2, log5_bounds.1, log5_bounds.2]

noncomputable def e (x : ℝ) : ℝ :=
  (T x - (x * log x - x + 1))

lemma U_bound.lemma_1 (x : ℝ) : T x = x * log x - x + 1 + (e x) := by
  unfold e
  ring

lemma U_bound.lemma_2 (x : ℝ) (hx : 1 ≤ x) : |e x| ≤ log x := by
  rw [abs_le]
  unfold e
  constructor <;> linarith [T.ge x hx, T.le x hx]

lemma U_bound.lemma_3 (x : ℝ) :
    U x = ν.sum (fun m w ↦ w * ((x / m) * (log (x / m))))
          - ν.sum (fun m w ↦ w * (x / m))
          + ν.sum (fun _m w ↦ w)
          + ν.sum (fun m w ↦ w * e (x / m)) := by
  simp [U, Finsupp.sum, U_bound.lemma_1, sub_eq_add_neg, add_mul, mul_comm, sum_add_distrib]

lemma U_bound.lemma_4 (x : ℝ) (hx : 0 < x) :
    ν.sum (fun m w ↦ w * ((x / m) * log (x / m))) = a * x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have ha : a = -(log 1 / 1 - log 2 / 2 - log 3 / 3 - log 5 / 5 + log 30 / 30) := by
    simp_rw [a, mul_div_assoc]; rw [ν_sum_mul (fun m ↦ log m / m)]; push_cast; rfl
  rw [ν_sum_mul (fun m ↦ (x / m) * log (x / m)), ha]
  simp [Real.log_div hx0]
  ring

lemma U_bound.lemma_5 (x : ℝ) : ν.sum (fun m w ↦ w * (x / m)) = 0 := by
  rw [ν_sum_mul (fun m ↦ x / m)]; push_cast; ring

lemma U_bound.lemma_6 : ν.sum (fun _ w ↦ w) = (-1 : ℝ) := by
  have := ν_sum_mul (fun _ ↦ (1 : ℝ)); simp at this; linarith

lemma Finsupp.abs_sum_le (A : Type*) (ν : A →₀ ℝ) (g : A → ℝ → ℝ) : |ν.sum g| ≤ ν.sum |g| := by
  simp_rw [Finsupp.sum.eq_1]
  exact abs_sum_le_sum_abs (fun i ↦ g i (ν i)) ν.support

theorem U_bound (x : ℝ) (hx : 30 ≤ x) : |U x - a * x| ≤ 5 * log x - 5 := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  rw [U_bound.lemma_3, U_bound.lemma_4 x hxpos]
  ring_nf
  have hlin : ν.sum (fun m w ↦ x * w * (↑m)⁻¹) = 0 :=
    by simpa [div_eq_mul_inv, mul_assoc, mul_left_comm] using U_bound.lemma_5 x
  rw [hlin]; ring_nf; rw [U_bound.lemma_6]
  grw [abs_add_le, Finsupp.abs_sum_le]
  norm_num
  have hsupp_eq : ν.support = {1, 2, 3, 5, 30} := ν_support
  have hmem_of_supp : ∀ i ∈ ν.support, 0 < i ∧ i ≤ 30 := fun i hi ↦ by
    have : i ∈ ({1, 2, 3, 5, 30} : Finset ℕ) := hsupp_eq ▸ hi
    simp only [mem_insert, mem_singleton] at this
    constructor <;> omega
  have h : ν.sum |fun m w ↦ w * e (x * (↑m)⁻¹)| ≤ ν.sum (fun m w ↦ |w| * log (x * (↑m)⁻¹)) := by
    apply Finsupp.sum_le_sum
    intro i hi
    simp only [Pi.abs_apply, abs_mul]
    obtain ⟨hi_pos, hi_le⟩ := hmem_of_supp i hi
    have hxi : 1 ≤ x * (↑i)⁻¹ := by
      rw [le_mul_inv_iff₀ (by exact_mod_cast hi_pos)]
      linarith [show (i : ℝ) ≤ 30 from by exact_mod_cast hi_le]
    gcongr; exact U_bound.lemma_2 _ hxi
  grw [h]
  have hlog_split : ν.sum (fun m w ↦ |w| * log (x * (m : ℝ)⁻¹)) =
      log x * ν.sum (fun m w ↦ |w|) - ν.sum (fun m w ↦ |w| * log (↑m : ℝ)) := by
    simp only [Finsupp.sum]
    conv_rhs => rw [Finset.mul_sum, ← sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    have hm_pos : (0 : ℝ) < m := by exact_mod_cast (hmem_of_supp m hm).1
    rw [← div_eq_mul_inv, Real.log_div (ne_of_gt hxpos) (ne_of_gt hm_pos)]; ring
  rw [hlog_split]
  -- Once the support of `ν` is known explicitly, both `habs` and `hsum_eq`
  -- reduce to concrete arithmetic over a five-element finset.
  have expand_sum : ∀ f : ℕ → ℝ → ℝ, (∀ n, f n 0 = 0) →
      ν.sum f = f 1 1 + f 2 (-1) + f 3 (-1) + f 5 (-1) + f 30 1 := by
    intro f hf
    rw [Finsupp.sum_of_support_subset _ hsupp_eq.le _ (by intros; simp [hf])]
    simp only [sum_insert (by decide : (1:ℕ) ∉ ({2,3,5,30} : Finset ℕ)),
               sum_insert (by decide : (2:ℕ) ∉ ({3,5,30} : Finset ℕ)),
               sum_insert (by decide : (3:ℕ) ∉ ({5,30} : Finset ℕ)),
               sum_insert (by decide : (5:ℕ) ∉ ({30} : Finset ℕ)),
               sum_singleton, ν, Finsupp.sub_apply, Finsupp.add_apply, Finsupp.single_apply]
    norm_num
    ring
  have habs : ν.sum (fun m w ↦ |w|) = 5 := by
    rw [expand_sum _ (by intros; simp)]; norm_num
  have hgeq6 : ν.sum (fun m w ↦ |w| * log m) ≥ 6 := by
    have hsum_eq : ν.sum (fun m w ↦ |w| * log (m : ℝ)) = log 2 + log 3 + log 5 + log 30 := by
      rw [expand_sum _ (by intros; simp)]
      simp [log_one]
    have h30 : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
      rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_two_gt_d9, log3_bounds.1, log5_bounds.1]
  grw [hgeq6]; rw [habs]; linarith

theorem psi_lower (x : ℝ) (hx : 30 ≤ x) : ψ x ≥ a * x - 5 * log x + 5 := by
  have h2 := abs_sub_le_iff.mp (U_bound x hx)
  linarith [psi_ge_weighted x (by linarith), h2.1]

end Chebyshev

-- ===== Base =====
/-! The singular-series weight `K(s) = ∏_{p ∣ s, p > 2} (p-1)/(p-2)`. -/

namespace P27

noncomputable def Kf (s : ℕ) : ℝ :=
  ∏ p ∈ s.primeFactors, if 2 < p then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1

end P27

-- ===== TSum =====
/-! The small primes `Q` (the first 150 odd primes) and the weight sum `∑_{b<a} K(a-b)`. -/

open Finset Real

namespace P27
def Qc0 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
def Qc1 : List ℕ := [37, 41, 43, 47, 53, 59, 61, 67, 71, 73]
def Qc2 : List ℕ := [79, 83, 89, 97, 101, 103, 107, 109, 113, 127]
def Qc3 : List ℕ := [131, 137, 139, 149, 151, 157, 163, 167, 173, 179]
def Qc4 : List ℕ := [181, 191, 193, 197, 199, 211, 223, 227, 229, 233]
def Qc5 : List ℕ := [239, 241, 251, 257, 263, 269, 271, 277, 281, 283]
def Qc6 : List ℕ := [293, 307, 311, 313, 317, 331, 337, 347, 349, 353]
def Qc7 : List ℕ := [359, 367, 373, 379, 383, 389, 397, 401, 409, 419]
def Qc8 : List ℕ := [421, 431, 433, 439, 443, 449, 457, 461, 463, 467]
def Qc9 : List ℕ := [479, 487, 491, 499, 503, 509, 521, 523, 541, 547]
def Qc10 : List ℕ := [557, 563, 569, 571, 577, 587, 593, 599, 601, 607]
def Qc11 : List ℕ := [613, 617, 619, 631, 641, 643, 647, 653, 659, 661]
def Qc12 : List ℕ := [673, 677, 683, 691, 701, 709, 719, 727, 733, 739]
def Qc13 : List ℕ := [743, 751, 757, 761, 769, 773, 787, 797, 809, 811]
def Qc14 : List ℕ := [821, 823, 827, 829, 839, 853, 857, 859, 863, 877]
def Qlist : List ℕ := Qc0 ++ Qc1 ++ Qc2 ++ Qc3 ++ Qc4 ++ Qc5 ++ Qc6 ++ Qc7 ++ Qc8 ++ Qc9 ++ Qc10 ++ Qc11 ++ Qc12 ++ Qc13 ++ Qc14
theorem Qlist_nodup : Qlist.Nodup := by decide +kernel

def Qs : Finset ℕ := ⟨(Qlist : Multiset ℕ), Multiset.coe_nodup.2 Qlist_nodup⟩

theorem Qc0_prime : ∀ p ∈ Qc0, p.Prime := by
  simp only [Qc0, List.forall_mem_cons]
  norm_num

theorem Qc1_prime : ∀ p ∈ Qc1, p.Prime := by
  simp only [Qc1, List.forall_mem_cons]
  norm_num

theorem Qc2_prime : ∀ p ∈ Qc2, p.Prime := by
  simp only [Qc2, List.forall_mem_cons]
  norm_num

theorem Qc3_prime : ∀ p ∈ Qc3, p.Prime := by
  simp only [Qc3, List.forall_mem_cons]
  norm_num

theorem Qc4_prime : ∀ p ∈ Qc4, p.Prime := by
  simp only [Qc4, List.forall_mem_cons]
  norm_num

theorem Qc5_prime : ∀ p ∈ Qc5, p.Prime := by
  simp only [Qc5, List.forall_mem_cons]
  norm_num

theorem Qc6_prime : ∀ p ∈ Qc6, p.Prime := by
  simp only [Qc6, List.forall_mem_cons]
  norm_num

theorem Qc7_prime : ∀ p ∈ Qc7, p.Prime := by
  simp only [Qc7, List.forall_mem_cons]
  norm_num

theorem Qc8_prime : ∀ p ∈ Qc8, p.Prime := by
  simp only [Qc8, List.forall_mem_cons]
  norm_num

theorem Qc9_prime : ∀ p ∈ Qc9, p.Prime := by
  simp only [Qc9, List.forall_mem_cons]
  norm_num

theorem Qc10_prime : ∀ p ∈ Qc10, p.Prime := by
  simp only [Qc10, List.forall_mem_cons]
  norm_num

theorem Qc11_prime : ∀ p ∈ Qc11, p.Prime := by
  simp only [Qc11, List.forall_mem_cons]
  norm_num

theorem Qc12_prime : ∀ p ∈ Qc12, p.Prime := by
  simp only [Qc12, List.forall_mem_cons]
  norm_num

theorem Qc13_prime : ∀ p ∈ Qc13, p.Prime := by
  simp only [Qc13, List.forall_mem_cons]
  norm_num

theorem Qc14_prime : ∀ p ∈ Qc14, p.Prime := by
  simp only [Qc14, List.forall_mem_cons]
  norm_num

theorem Qlist_prime : ∀ p ∈ Qlist, p.Prime :=
  List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨Qc0_prime, Qc1_prime⟩, Qc2_prime⟩, Qc3_prime⟩, Qc4_prime⟩, Qc5_prime⟩, Qc6_prime⟩, Qc7_prime⟩, Qc8_prime⟩, Qc9_prime⟩, Qc10_prime⟩, Qc11_prime⟩, Qc12_prime⟩, Qc13_prime⟩, Qc14_prime⟩

theorem Qs_prop (p : ℕ) (hp : p ∈ Qs) : p.Prime ∧ p ≠ 2 ∧ p ≤ 877 := by
  have hp' : p ∈ Qlist := Multiset.mem_coe.1 (Finset.mem_def.1 hp)
  refine ⟨Qlist_prime p hp', ?_, ?_⟩
  · have : ∀ q ∈ Qlist, q ≠ 2 := by decide +kernel
    exact this p hp'
  · have : ∀ q ∈ Qlist, q ≤ 877 := by decide +kernel
    exact this p hp'

theorem Qs_card : Qs.card = 150 := by decide +kernel

def Sset : Finset ℕ := {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43}

def Wk (d : ℕ) : ℕ := ∏ p ∈ Sset, (if p ∣ d then p - 1 else p - 2)

def Dk : ℕ := ∏ p ∈ Sset, (p - 2)

theorem Sset_prime : ∀ p ∈ Sset, p.Prime ∧ 3 ≤ p := by
  intro p hp
  simp only [Sset, mem_insert, mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num

noncomputable def fK (p : ℕ) : ℝ := ((p : ℝ) - 1) / ((p : ℝ) - 2)

theorem one_le_fK (p : ℕ) (hp : 3 ≤ p) : 1 ≤ fK p := by
  unfold fK
  have : (3 : ℝ) ≤ p := by exact_mod_cast hp
  rw [le_div_iff₀ (by linarith)]; linarith

theorem fK_le_47 (p : ℕ) (hp : 47 ≤ p) : fK p ≤ 46 / 45 := by
  unfold fK
  have h : (47 : ℝ) ≤ p := by exact_mod_cast hp
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

theorem fK_term (p d : ℕ) (hp : 3 ≤ p) :
    (if p ∣ d then fK p else 1) =
      (((if p ∣ d then p - 1 else p - 2 : ℕ) : ℝ) / (((p - 2 : ℕ)) : ℝ)) := by
  have hc1 : (((p - 1 : ℕ)) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hc2 : (((p - 2 : ℕ)) : ℝ) = (p : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hne : (p : ℝ) - 2 ≠ 0 := by
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  split_ifs
  · unfold fK; push_cast [hc1, hc2]; rfl
  · push_cast [hc2]; rw [div_self hne]

theorem prod_S_eq (d : ℕ) :
    ∏ p ∈ Sset, (if p ∣ d then fK p else 1) = (Wk d : ℝ) / Dk := by
  rw [prod_congr rfl (fun p hp => fK_term p d (Sset_prime p hp).2), prod_div_distrib]
  unfold Wk Dk
  rw [Nat.cast_prod, Nat.cast_prod]

set_option maxHeartbeats 1000000 in
theorem Kf_le_Wk (d : ℕ) (hd0 : 0 < d) (hdl : d < 2209) :
    Kf d ≤ 46 / 45 * (Wk d : ℝ) / Dk := by
  have hKf : Kf d = ∏ p ∈ d.primeFactors, (if 2 < p then fK p else 1) := rfl
  rw [hKf, ← prod_filter_mul_prod_filter_not d.primeFactors (fun p => p < 47)]
  have hsmall : d.primeFactors.filter (fun p => p < 47) = (insert 2 Sset).filter (fun p => p ∣ d) := by
    ext p
    simp only [mem_filter, Nat.mem_primeFactors, mem_insert]
    constructor
    · rintro ⟨⟨hpp, hpd, -⟩, hp47⟩
      refine ⟨?_, hpd⟩
      have := hpp.two_le
      interval_cases p <;> first | (left; rfl) | (right; decide) | (exfalso; norm_num at hpp)
    · rintro ⟨hp, hpd⟩
      rcases hp with rfl | hp
      · exact ⟨⟨Nat.prime_two, hpd, by omega⟩, by norm_num⟩
      · refine ⟨⟨(Sset_prime p hp).1, hpd, by omega⟩, ?_⟩
        simp only [Sset, mem_insert, mem_singleton] at hp
        omega
  have h2S : (2 : ℕ) ∉ Sset := by decide
  rw [hsmall, prod_filter, prod_insert h2S]
  have hS : ∏ p ∈ Sset, (if p ∣ d then (if 2 < p then fK p else 1) else 1) =
      ∏ p ∈ Sset, (if p ∣ d then fK p else 1) := by
    refine prod_congr rfl fun p hp => ?_
    have := (Sset_prime p hp).2
    rw [if_pos (show 2 < p by omega)]
  rw [hS, prod_S_eq]
  have h2 : (if 2 ∣ d then (if 2 < 2 then fK 2 else 1) else 1) = (1 : ℝ) := by simp
  rw [h2, one_mul]
  set Bf := d.primeFactors.filter (fun p => ¬ p < 47) with hBf
  have hcard : Bf.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [hBf, mem_filter, Nat.mem_primeFactors] at ha hb
    by_contra hab
    have hcop : Nat.Coprime a b := (Nat.coprime_primes ha.1.1 hb.1.1).2 hab
    have hdiv : a * b ∣ d := hcop.mul_dvd_of_dvd_of_dvd ha.1.2.1 hb.1.2.1
    have hle := Nat.le_of_dvd hd0 hdiv
    have ha47 : 47 ≤ a := by omega
    have hb47 : 47 ≤ b := by omega
    have : 47 * 47 ≤ a * b := Nat.mul_le_mul ha47 hb47
    omega
  have hB : ∏ p ∈ Bf, (if 2 < p then fK p else 1) ≤ 46 / 45 := by
    calc ∏ p ∈ Bf, (if 2 < p then fK p else 1) ≤ ∏ p ∈ Bf, (46 / 45 : ℝ) := by
          apply prod_le_prod
          · intro p hp
            simp only [hBf, mem_filter] at hp
            rw [if_pos (by omega)]; linarith [one_le_fK p (by omega)]
          · intro p hp
            simp only [hBf, mem_filter] at hp
            rw [if_pos (by omega)]; exact fK_le_47 p (by omega)
      _ = (46 / 45) ^ Bf.card := by rw [prod_const]
      _ ≤ (46 / 45) ^ 1 := pow_le_pow_right₀ (by norm_num) hcard
      _ = 46 / 45 := pow_one _
  have hW : (0 : ℝ) ≤ (Wk d : ℝ) / Dk := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  calc ((Wk d : ℝ) / Dk) * ∏ p ∈ Bf, (if 2 < p then fK p else 1) ≤ ((Wk d : ℝ) / Dk) * (46 / 45) :=
        mul_le_mul_of_nonneg_left hB hW
    _ = 46 / 45 * (Wk d : ℝ) / Dk := by ring

def Wk2 (d : ℕ) : ℕ := (if d % 3 = 0 then 2 else 1) * (if d % 5 = 0 then 4 else 3) * (if d % 7 = 0 then 6 else 5) * (if d % 11 = 0 then 10 else 9) * (if d % 13 = 0 then 12 else 11) * (if d % 17 = 0 then 16 else 15) * (if d % 19 = 0 then 18 else 17) * (if d % 23 = 0 then 22 else 21) * (if d % 29 = 0 then 28 else 27) * (if d % 31 = 0 then 30 else 29) * (if d % 37 = 0 then 36 else 35) * (if d % 41 = 0 then 40 else 39) * (if d % 43 = 0 then 42 else 41)

theorem Wk_eq (d : ℕ) : Wk d = Wk2 d := by
  simp only [Wk, Sset, Wk2]
  rw [prod_insert (by decide), prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
    prod_insert (by decide), prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
    prod_insert (by decide), prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
    prod_singleton]
  simp only [Nat.dvd_iff_mod_eq_zero]
  norm_num only [mul_assoc]

def rowW (a : ℕ) : ℕ := (Qlist.map fun b => if b < a then Wk2 (a - b) else 0).sum
theorem chunk0 : (Qc0.map rowW).sum ≤ 22334401544323050 := by decide +kernel
theorem chunk1 : (Qc1.map rowW).sum ≤ 81184428911190150 := by decide +kernel
theorem chunk2 : (Qc2.map rowW).sum ≤ 140965406992975950 := by decide +kernel
theorem chunk3 : (Qc3.map rowW).sum ≤ 201870775876366800 := by decide +kernel
theorem chunk4 : (Qc4.map rowW).sum ≤ 260284136341434975 := by decide +kernel
theorem chunk5 : (Qc5.map rowW).sum ≤ 323231843728747800 := by decide +kernel
theorem chunk6 : (Qc6.map rowW).sum ≤ 383210746492869540 := by decide +kernel
theorem chunk7 : (Qc7.map rowW).sum ≤ 441685524908464515 := by decide +kernel
theorem chunk8 : (Qc8.map rowW).sum ≤ 502604899649725320 := by decide +kernel
theorem chunk9 : (Qc9.map rowW).sum ≤ 563874701075903070 := by decide +kernel
theorem chunk10 : (Qc10.map rowW).sum ≤ 626127811285855725 := by decide +kernel
theorem chunk11 : (Qc11.map rowW).sum ≤ 683907388954790490 := by decide +kernel
theorem chunk12 : (Qc12.map rowW).sum ≤ 742991985680191380 := by decide +kernel
theorem chunk13 : (Qc13.map rowW).sum ≤ 805695899866849530 := by decide +kernel
theorem chunk14 : (Qc14.map rowW).sum ≤ 865807107315140655 := by decide +kernel

theorem sum_Qs {M : Type*} [AddCommMonoid M] (f : ℕ → M) : ∑ a ∈ Qs, f a = (Qlist.map f).sum := by
  show Multiset.sum (Multiset.map f (Qlist : Multiset ℕ)) = _
  rw [Multiset.map_coe, Multiset.sum_coe]

theorem Qlist_eq : Qlist = Qc0 ++ Qc1 ++ Qc2 ++ Qc3 ++ Qc4 ++ Qc5 ++ Qc6 ++ Qc7 ++ Qc8 ++ Qc9 ++ Qc10 ++ Qc11 ++ Qc12 ++ Qc13 ++ Qc14 := rfl

theorem row_eq (a : ℕ) : (∑ b ∈ Qs, if b < a then Wk (a - b) else 0) = rowW a := by
  rw [sum_Qs]
  simp only [Wk_eq, rowW]

theorem half_le : (∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then Wk (a - b) else 0) ≤ 6645777058624828950 := by
  have h1 : (∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then Wk (a - b) else 0) = (Qlist.map rowW).sum := by
    rw [sum_Qs]
    simp only [row_eq]
  rw [h1, Qlist_eq]
  simp only [List.map_append, List.sum_append]
  exact (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (chunk0) chunk1) chunk2) chunk3) chunk4) chunk5) chunk6) chunk7) chunk8) chunk9) chunk10) chunk11) chunk12) chunk13) chunk14).trans_eq (by norm_num)

theorem Dk_eq : Dk = 348469040044125 := by
  simp [Dk, Sset]

theorem T_bound :
    ∑ a ∈ Qs, ∑ b ∈ Qs, (if b < a then Kf (a - b) else 0) ≤ 19496 := by
  have hterm : ∀ a ∈ Qs, ∀ b ∈ Qs, (if b < a then Kf (a - b) else 0) ≤
      46 / 45 / Dk * ((if b < a then Wk (a - b) else 0 : ℕ) : ℝ) := by
    intro a ha b hb
    obtain ⟨-, -, ha1⟩ := Qs_prop a ha
    split_ifs with hab
    · have := Kf_le_Wk (a - b) (by omega) (by omega)
      exact this.trans_eq (by ring)
    · simp
  have hD : (0 : ℝ) < Dk := by
    rw [Dk_eq]; norm_num
  have hk : 0 ≤ 46 / 45 / (Dk : ℝ) := div_nonneg (by norm_num) hD.le
  set H := (∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then Wk (a - b) else 0 : ℕ) with hH
  have hHle : (H : ℝ) ≤ 6645777058624828950 := by exact_mod_cast half_le
  have hcast : ((H : ℕ) : ℝ) = ∑ a ∈ Qs, ∑ b ∈ Qs, ((if b < a then Wk (a - b) else 0 : ℕ) : ℝ) := by
    rw [hH, Nat.cast_sum]; exact sum_congr rfl fun a _ => Nat.cast_sum _ _
  calc ∑ a ∈ Qs, ∑ b ∈ Qs, (if b < a then Kf (a - b) else 0)
      ≤ ∑ a ∈ Qs, ∑ b ∈ Qs, 46 / 45 / Dk * ((if b < a then Wk (a - b) else 0 : ℕ) : ℝ) :=
        sum_le_sum fun a ha => sum_le_sum fun b hb => hterm a ha b hb
    _ = 46 / 45 / Dk * (H : ℝ) := by
        rw [hcast, mul_sum]; exact sum_congr rfl fun a _ => (mul_sum _ _ _).symm
    _ ≤ 46 / 45 / Dk * (6645777058624828950 : ℝ) := mul_le_mul_of_nonneg_left hHle hk
    _ ≤ 19496 := by
        rw [Dk_eq]; norm_num

theorem pairs_card : (∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then 1 else 0 : ℕ) = 11175 := by
  decide +kernel

end P27

-- ===== RV =====
/-! Riesel–Vaughan small shifts: representations `s = a + q` with `a ∈ Q`, `q` an odd prime. -/

open Finset Real

namespace P27
open Schnir

/-- odd primes `≤ t`. -/
def oddP (t : ℕ) : Finset ℕ := (range (t + 1)).filter (fun p => p.Prime ∧ p ≠ 2)

theorem oddP_card (M : ℕ) (hM : 2 ≤ M) : (oddP M).card + 1 = Nat.primeCounting M := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have : oddP M = ((Finset.range (M + 1)).filter Nat.Prime).erase 2 := by
    ext p; simp [oddP, Finset.mem_erase]; tauto
  rw [this, Finset.card_erase_add_one]
  simp [Nat.prime_two]; omega

/-- `[s = a + q]` with `q` an odd prime. -/
noncomputable def ind (a s : ℕ) : ℕ := if a ≤ s ∧ (s - a).Prime ∧ s - a ≠ 2 then 1 else 0

/-- number of `a ∈ Q` with `s - a` an odd prime. -/
noncomputable def Rr (s : ℕ) : ℕ := #{a ∈ Qs | a ≤ s ∧ (s - a).Prime ∧ s - a ≠ 2}

theorem Rr_eq (s : ℕ) : Rr s = ∑ a ∈ Qs, ind a s := by
  rw [Rr, card_filter]; rfl

theorem ind_sq (a s : ℕ) : ind a s * ind a s = ind a s := by
  unfold ind; split_ifs <;> simp

theorem ind_mul (a b s : ℕ) : ind a s * ind b s =
    if (a ≤ s ∧ (s - a).Prime ∧ s - a ≠ 2) ∧ (b ≤ s ∧ (s - b).Prime ∧ s - b ≠ 2) then 1 else 0 := by
  unfold ind; rw [ite_zero_mul_ite_zero, one_mul]

/-- prime pairs `m, m + d` with `m + d ≤ x` (the count in Siebert's bound). -/
noncomputable def PPs (d x : ℕ) : ℕ := #{m ∈ range (x + 1) | m.Prime ∧ (m + d).Prime ∧ m + d ≤ x}

/-- first moment: each `a ∈ Q` contributes at least the odd primes up to `n - 877`. -/
theorem sumR_lower (n : ℕ) (hn : 879 ≤ n) :
    150 * (oddP (n - 877)).card ≤ ∑ s ∈ range (n + 1), Rr s := by
  simp_rw [Rr_eq]
  rw [sum_comm]
  have h : ∀ a ∈ Qs, (oddP (n - 877)).card ≤ ∑ s ∈ range (n + 1), ind a s := by
    intro a ha
    obtain ⟨-, -, ha877⟩ := Qs_prop a ha
    unfold ind
    rw [← card_filter]
    apply card_le_card_of_injOn (fun q => q + a)
    · intro q hq
      simp only [oddP, coe_filter, mem_range, Set.mem_ofPred_eq] at hq
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq, Nat.add_sub_cancel]
      exact ⟨by omega, by omega, hq.2.1, hq.2.2⟩
    · intro q _ q' _ h
      simp only at h
      omega
  calc 150 * (oddP (n - 877)).card = ∑ _a ∈ Qs, (oddP (n - 877)).card := by
        rw [sum_const, Qs_card, smul_eq_mul]
    _ ≤ _ := sum_le_sum h

/-- a pair `b < a` of shifts hits a prime pair `(s - a, s - b)`. -/
theorem pair_le (a b n : ℕ) (hba : b < a) :
    ∑ s ∈ range (n + 1), ind a s * ind b s ≤ PPs (a - b) n := by
  simp_rw [ind_mul]
  rw [← card_filter, PPs]
  apply card_le_card_of_injOn (fun s => s - a)
  · intro s hs
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hs
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq]
    obtain ⟨hs, ⟨has, hpa, -⟩, ⟨hbs, hpb, -⟩⟩ := hs
    refine ⟨by omega, hpa, ?_, by omega⟩
    rwa [show s - a + (a - b) = s - b by omega]
  · intro s hs t ht h
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hs ht
    simp only at h
    omega

/-- pointwise square expansion. -/
theorem Rr_sq (s : ℕ) : Rr s ^ 2 = Rr s +
    2 * ∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then ind a s * ind b s else 0 := by
  have hsplit : ∀ a b : ℕ, ind a s * ind b s = (if b < a then ind a s * ind b s else 0) +
      (if a = b then ind a s else 0) + (if a < b then ind a s * ind b s else 0) := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · subst h; simp [ind_sq]
    · simp [h, h.ne', not_lt.2 h.le]
  have hsym : (∑ a ∈ Qs, ∑ b ∈ Qs, if a < b then ind a s * ind b s else 0) =
      ∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then ind a s * ind b s else 0 := by
    rw [sum_comm]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    rw [mul_comm]
  have hdiag : (∑ a ∈ Qs, ∑ b ∈ Qs, if a = b then ind a s else 0) = ∑ a ∈ Qs, ind a s :=
    sum_congr rfl fun a ha => by simp [ha]
  rw [Rr_eq, sq, sum_mul_sum]
  rw [sum_congr rfl fun a _ => sum_congr rfl fun b _ => hsplit a b]
  simp only [sum_add_distrib]
  rw [hsym, hdiag]
  ring

/-- second moment: diagonal plus prime pairs. -/
theorem sumR2_le (n : ℕ) : ∑ s ∈ range (n + 1), Rr s ^ 2 ≤ ∑ s ∈ range (n + 1), Rr s +
    2 * ∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then PPs (a - b) n else 0 := by
  simp_rw [Rr_sq]
  rw [sum_add_distrib, ← mul_sum]
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  rw [sum_comm]
  refine sum_le_sum fun a _ => ?_
  rw [sum_comm]
  refine sum_le_sum fun b _ => ?_
  split_ifs with h
  · exact pair_le a b n h
  · simp

theorem r_pos_of_Rr (s : ℕ) (h : Rr s ≠ 0) : 0 < r s := by
  rw [Rr] at h
  obtain ⟨a, ha⟩ := card_pos.1 (Nat.pos_of_ne_zero h)
  rw [mem_filter] at ha
  obtain ⟨haQ, has, hp, h2⟩ := ha
  obtain ⟨hap, ha2, -⟩ := Qs_prop a haQ
  unfold r
  exact card_pos.2 ⟨a, mem_filter.2 ⟨mem_range.2 (by omega), hap, ha2, hp, h2⟩⟩

/-- Cauchy–Schwarz. -/
theorem rv_cs (n : ℕ) : (∑ s ∈ range (n + 1), Rr s) ^ 2 ≤
    #{s ∈ range (n + 1) | 0 < r s} * ∑ s ∈ range (n + 1), Rr s ^ 2 := by
  set F := (range (n + 1)).filter (fun s => Rr s ≠ 0) with hF
  have h1 : ∑ s ∈ range (n + 1), Rr s = ∑ s ∈ F, Rr s := (sum_filter_ne_zero _).symm
  have h2 : ∑ s ∈ F, Rr s ^ 2 ≤ ∑ s ∈ range (n + 1), Rr s ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
  have h3 : #F ≤ #{s ∈ range (n + 1) | 0 < r s} := by
    apply card_le_card
    intro s hs
    rw [hF, mem_filter] at hs
    exact mem_filter.2 ⟨hs.1, r_pos_of_Rr s hs.2⟩
  rw [h1]
  calc (∑ s ∈ F, Rr s) ^ 2 ≤ #F * ∑ s ∈ F, Rr s ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ _ := Nat.mul_le_mul h3 h2


end P27

-- ===== RVPiece =====
/-! The analytic inequalities for one piece `La ≤ log n ≤ Lb` of the middle range. -/

open Finset Real

namespace P27
open Schnir

theorem exp99_ge (x : ℝ) (hx : 70 ≤ x) : (10 : ℝ) ^ 9 ≤ exp x := by
  have h3 : (3 : ℝ) ≤ exp 2 := by linarith [add_one_le_exp (2 : ℝ)]
  have h : exp 70 = exp 2 ^ 35 := by rw [← exp_nat_mul]; norm_num
  calc (10 : ℝ) ^ 9 ≤ 3 ^ 35 := by norm_num
    _ ≤ exp 2 ^ 35 := pow_le_pow_left₀ (by norm_num) h3 35
    _ = exp 70 := h.symm
    _ ≤ exp x := exp_le_exp.2 hx

/-- first moment, from Chebyshev's `ψ(m) ≥ a m - 5 log m + 5` (`a ≥ 0.9212`). -/
theorem X_lower (n : ℕ) (Lb : ℝ) (hn : (10 : ℝ) ^ 9 ≤ n) (hLb : log n ≤ Lb) (hLb12 : Lb ≤ 12000) :
    150 * 0.9211 / Lb * n ≤ ((∑ s ∈ range (n + 1), Rr s : ℕ) : ℝ) := by
  have hn879 : 879 ≤ n := by exact_mod_cast (show (879 : ℝ) ≤ n by linarith)
  set m := n - 877 with hm
  have hmR : (m : ℝ) = n - 877 := by rw [hm, Nat.cast_sub (by omega)]; norm_num
  have hX := sumR_lower n hn879
  have hP := oddP_card m (by omega)
  have hpsi1 := Chebyshev.psi_le_primeCounting_mul_log m
  have hpsi2 := Chebyshev.psi_lower (m : ℝ) (by rw [hmR]; linarith)
  have ha := Chebyshev.a_bound.1
  have hm0 : (0 : ℝ) < m := by rw [hmR]; linarith
  have hlogm : log m ≤ log n := log_le_log hm0 (by rw [hmR]; linarith)
  have hlogm0 : 0 < log (m : ℝ) := log_pos (by rw [hmR]; linarith)
  have hc : ((oddP m).card : ℝ) + 1 = Nat.primeCounting m := by exact_mod_cast hP
  have e1 : ((oddP m).card : ℝ) * log m = (Nat.primeCounting m : ℝ) * log m - log m := by
    rw [← hc]; ring
  have key : Chebyshev.a * (m : ℝ) - 6 * log m + 5 ≤ ((oddP m).card : ℝ) * log m := by
    rw [e1]; linarith
  have hcard0 : (0 : ℝ) ≤ (oddP m).card := Nat.cast_nonneg _
  have hk2 : ((oddP m).card : ℝ) * log m ≤ ((oddP m).card : ℝ) * Lb :=
    mul_le_mul_of_nonneg_left (hlogm.trans hLb) hcard0
  have hlogm12 : log (m : ℝ) ≤ 12000 := hlogm.trans (hLb.trans hLb12)
  have hma : Chebyshev.a * (m : ℝ) ≥ 0.9212 * m := mul_le_mul_of_nonneg_right ha hm0.le
  have hmain : 0.9211 * (n : ℝ) ≤ ((oddP m).card : ℝ) * Lb := by
    linarith
  have hLbpos : 0 < Lb := lt_of_lt_of_le (log_pos (by linarith)) hLb
  have hXc : (150 : ℝ) * (oddP m).card ≤ ((∑ s ∈ range (n + 1), Rr s : ℕ) : ℝ) := by
    exact_mod_cast hX
  rw [div_mul_eq_mul_div, div_le_iff₀ hLbpos]
  have := mul_le_mul_of_nonneg_right hXc hLbpos.le
  linarith

/-- Siebert's bound for one shift. -/
theorem PPs_le (d n : ℕ) (hn : 2 ≤ n) (hd0 : 0 < d) (hd2 : 2 ∣ d) :
    (PPs d n : ℝ) ≤ 8 * TaoFivePrimes.twinPrimeConstant * n / (log n) ^ 2 * Kf d := by
  have h := TaoFivePrimes.siebert_prime_pair_bound n d hn hd0 hd2
  have e : (PPs d n : ℝ) = ∑ m ∈ range (n + 1),
      if Nat.Prime m ∧ Nat.Prime (m + d) ∧ m + d ≤ n then (1 : ℝ) else 0 := by
    rw [PPs, Finset.natCast_card_filter]
  rw [e]
  exact h

/-- the off-diagonal (prime pair) part of the second moment. -/
theorem off_le (n : ℕ) (La : ℝ) (hLa : 22 ≤ La) (h1 : La ≤ log n) :
    ((2 * ∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then PPs (a - b) n else 0 : ℕ) : ℝ) ≤
      n * (16 * 1.3217 * 19496 / La ^ 2) := by
  obtain ⟨-, hCup, -, -⟩ := PrimePairSieve.sieve_constants_certificate
  have hC0 : 0 ≤ TaoFivePrimes.twinPrimeConstant := by
    obtain ⟨h, -⟩ := PrimePairSieve.sieve_constants_certificate; linarith
  have hL : 22 ≤ log (n : ℝ) := hLa.trans h1
  have hnpos : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h] at hL; simp at hL; linarith
    · exact_mod_cast h
  have hn2 : 2 ≤ n := by
    by_contra h
    push Not at h
    have : (n : ℝ) ≤ 1 := by exact_mod_cast (show n ≤ 1 by omega)
    have := log_le_log hnpos this
    rw [log_one] at this; linarith
  set w := 8 * TaoFivePrimes.twinPrimeConstant * n / (log n) ^ 2 with hw
  have hw0 : 0 ≤ w := by positivity
  have hterm : ∀ a ∈ Qs, ∀ b ∈ Qs, ((if b < a then PPs (a - b) n else 0 : ℕ) : ℝ) ≤
      w * (if b < a then Kf (a - b) else 0) := by
    intro a ha b hb
    obtain ⟨hap, ha2, -⟩ := Qs_prop a ha
    obtain ⟨hbp, hb2, -⟩ := Qs_prop b hb
    split_ifs with hab
    · have hao := hap.odd_of_ne_two ha2
      have hbo := hbp.odd_of_ne_two hb2
      have hev : 2 ∣ a - b := by
        obtain ⟨i, hi⟩ := hao; obtain ⟨j, hj⟩ := hbo
        exact ⟨i - j, by omega⟩
      exact PPs_le (a - b) n hn2 (by omega) hev
    · simp
  have hsum : ((∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then PPs (a - b) n else 0 : ℕ) : ℝ) ≤
      w * 19496 := by
    have hcast : ((∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then PPs (a - b) n else 0 : ℕ) : ℝ) =
        ∑ a ∈ Qs, ∑ b ∈ Qs, ((if b < a then PPs (a - b) n else 0 : ℕ) : ℝ) := by
      rw [Nat.cast_sum]; exact sum_congr rfl fun a _ => Nat.cast_sum _ _
    rw [hcast]
    calc ∑ a ∈ Qs, ∑ b ∈ Qs, ((if b < a then PPs (a - b) n else 0 : ℕ) : ℝ)
        ≤ ∑ a ∈ Qs, ∑ b ∈ Qs, w * (if b < a then Kf (a - b) else 0) :=
          sum_le_sum fun a ha => sum_le_sum fun b hb => hterm a ha b hb
      _ = w * ∑ a ∈ Qs, ∑ b ∈ Qs, (if b < a then Kf (a - b) else 0) := by
          rw [mul_sum]; exact sum_congr rfl fun a _ => (mul_sum _ _ _).symm
      _ ≤ w * 19496 := mul_le_mul_of_nonneg_left T_bound hw0
  have hwle : w ≤ 8 * 1.3217 * n / La ^ 2 := by
    rw [hw]
    have hLa2 : La ^ 2 ≤ (log n) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
    calc 8 * TaoFivePrimes.twinPrimeConstant * n / (log n) ^ 2 ≤ 8 * 1.3217 * n / (log n) ^ 2 := by
          gcongr
      _ ≤ 8 * 1.3217 * n / La ^ 2 := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity) hLa2
  push_cast at hsum ⊢
  have : 2 * (w * 19496) ≤ n * (16 * 1.3217 * 19496 / La ^ 2) := by
    have e : (n : ℝ) * (16 * 1.3217 * 19496 / La ^ 2) = 2 * (8 * 1.3217 * n / La ^ 2 * 19496) := by ring
    rw [e]; nlinarith
  linarith

/-- one piece of the middle range: `#{s ≤ n : r(s) > 0} ≥ n * (100 / 2399)`. -/
theorem rv_piece (n : ℕ) (La Lb : ℝ) (hLa : 22 ≤ La) (hLb12 : Lb ≤ 12000)
    (h1 : La ≤ log n) (h2 : log n ≤ Lb) (hxb : 1 * (50 / 2399) ≤ 150 * 0.9211 / Lb)
    (hnum : 150 * 0.9211 / Lb + 16 * 1.3217 * 19496 / La ^ 2 ≤ 23.99 * (150 * 0.9211 / Lb) ^ 2) :
    (n : ℝ) * (100 / 2399) ≤ (#{s ∈ range (n + 1) | 0 < r s} : ℝ) := by
  have hn12 : (10 : ℝ) ^ 9 ≤ n := by
    have hnpos : (0 : ℝ) < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · rw [h] at h1; simp at h1; linarith
      · exact_mod_cast h
    rw [← exp_log hnpos]
    have h3 : (2.7 : ℝ) ≤ exp 1 := by linarith [exp_one_gt_d9]
    have : (10 : ℝ) ^ 9 ≤ exp 22 := by
      have e : exp 22 = exp 1 ^ 22 := by rw [← exp_nat_mul]; norm_num
      rw [e]
      calc (10 : ℝ) ^ 9 ≤ 2.7 ^ 22 := by norm_num
        _ ≤ exp 1 ^ 22 := pow_le_pow_left₀ (by norm_num) h3 22
    exact this.trans (exp_le_exp.2 (by linarith))
  set x := 150 * 0.9211 / Lb with hx
  set k := 16 * 1.3217 * 19496 / La ^ 2 with hk
  have hX := X_lower n Lb hn12 h2 hLb12
  have hoff := off_le n La hLa h1
  have hcs := rv_cs n
  have h2m := sumR2_le n
  set X := ∑ s ∈ range (n + 1), Rr s with hXdef
  set off := 2 * ∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then PPs (a - b) n else 0 with hoffdef
  set cnt := #{s ∈ range (n + 1) | 0 < r s} with hcnt
  have hcsN : X ^ 2 ≤ cnt * (X + off) := hcs.trans (Nat.mul_le_mul_left _ h2m)
  have hcsR : (X : ℝ) ^ 2 ≤ cnt * (X + off) := by exact_mod_cast hcsN
  have hX' : (n : ℝ) * x ≤ X := by rw [hx, mul_comm]; exact hX
  have hoff' : (off : ℝ) ≤ n * k := by rw [hk]; exact hoff
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hc0 : (0 : ℝ) ≤ cnt := Nat.cast_nonneg _
  have hk0 : 0 ≤ k := by rw [hk]; positivity
  by_contra hcon
  push Not at hcon
  have hnpos : (0 : ℝ) < n := by linarith
  have hxpos : 0 < x := by linarith
  have hXpos : 0 < (X : ℝ) := lt_of_lt_of_le (mul_pos hnpos hxpos) hX'
  have hnk : 0 ≤ (n : ℝ) * k := mul_nonneg hn0 hk0
  have h3 : (cnt : ℝ) * (X + off) ≤ cnt * (X + n * k) :=
    mul_le_mul_of_nonneg_left (by linarith) hc0
  have h4 : (cnt : ℝ) * (X + n * k) < n * (100 / 2399) * (X + n * k) :=
    mul_lt_mul_of_pos_right hcon (by linarith)
  have p1 : 0 ≤ ((X : ℝ) - n * x) * (X + n * x - n * (100 / 2399)) := by
    apply mul_nonneg (by linarith)
    have : 0 ≤ (n : ℝ) * (2 * x - 1 * (100 / 2399)) := mul_nonneg hn0 (by linarith)
    linarith
  have p2 : 0 ≤ (n : ℝ) ^ 2 * (23.99 * x ^ 2 - x - k) := mul_nonneg (sq_nonneg _) (by linarith)
  have e : (X : ℝ) ^ 2 - n * (100 / 2399) * (X + n * k) =
      ((X : ℝ) - n * x) * (X + n * x - n * (100 / 2399)) + (n : ℝ) ^ 2 * (23.99 * x ^ 2 - x - k) * (100 / 2399) := by
    ring
  linarith

end P27

-- ===== RVRange =====
/-! The middle range `22 ≤ log n ≤ 300`, split into pieces. -/

open Finset Real

namespace P27
open Schnir

theorem rv_range (n : ℕ) (h1 : 22 ≤ log n) (h2 : log n ≤ 300) :
    (n : ℝ) * (100 / 2399) ≤ (#{s ∈ range (n + 1) | 0 < r s} : ℝ) := by
  rcases le_or_gt (log (n : ℝ)) 23 with hb22 | ha22
  · exact rv_piece n 22 23 (by norm_num) (by norm_num) h1 hb22 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 24 with hb23 | ha23
  · exact rv_piece n 23 24 (by norm_num) (by norm_num) ha22.le hb23 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 25 with hb24 | ha24
  · exact rv_piece n 24 25 (by norm_num) (by norm_num) ha23.le hb24 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 26 with hb25 | ha25
  · exact rv_piece n 25 26 (by norm_num) (by norm_num) ha24.le hb25 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 27 with hb26 | ha26
  · exact rv_piece n 26 27 (by norm_num) (by norm_num) ha25.le hb26 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 28 with hb27 | ha27
  · exact rv_piece n 27 28 (by norm_num) (by norm_num) ha26.le hb27 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 29 with hb28 | ha28
  · exact rv_piece n 28 29 (by norm_num) (by norm_num) ha27.le hb28 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 30 with hb29 | ha29
  · exact rv_piece n 29 30 (by norm_num) (by norm_num) ha28.le hb29 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 31 with hb30 | ha30
  · exact rv_piece n 30 31 (by norm_num) (by norm_num) ha29.le hb30 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 32 with hb31 | ha31
  · exact rv_piece n 31 32 (by norm_num) (by norm_num) ha30.le hb31 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 33 with hb32 | ha32
  · exact rv_piece n 32 33 (by norm_num) (by norm_num) ha31.le hb32 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 34 with hb33 | ha33
  · exact rv_piece n 33 34 (by norm_num) (by norm_num) ha32.le hb33 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 35 with hb34 | ha34
  · exact rv_piece n 34 35 (by norm_num) (by norm_num) ha33.le hb34 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 36 with hb35 | ha35
  · exact rv_piece n 35 36 (by norm_num) (by norm_num) ha34.le hb35 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 37 with hb36 | ha36
  · exact rv_piece n 36 37 (by norm_num) (by norm_num) ha35.le hb36 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 38 with hb37 | ha37
  · exact rv_piece n 37 38 (by norm_num) (by norm_num) ha36.le hb37 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 39 with hb38 | ha38
  · exact rv_piece n 38 39 (by norm_num) (by norm_num) ha37.le hb38 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 40 with hb39 | ha39
  · exact rv_piece n 39 40 (by norm_num) (by norm_num) ha38.le hb39 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 41 with hb40 | ha40
  · exact rv_piece n 40 41 (by norm_num) (by norm_num) ha39.le hb40 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 42 with hb41 | ha41
  · exact rv_piece n 41 42 (by norm_num) (by norm_num) ha40.le hb41 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 43 with hb42 | ha42
  · exact rv_piece n 42 43 (by norm_num) (by norm_num) ha41.le hb42 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 44 with hb43 | ha43
  · exact rv_piece n 43 44 (by norm_num) (by norm_num) ha42.le hb43 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 45 with hb44 | ha44
  · exact rv_piece n 44 45 (by norm_num) (by norm_num) ha43.le hb44 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 46 with hb45 | ha45
  · exact rv_piece n 45 46 (by norm_num) (by norm_num) ha44.le hb45 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 47 with hb46 | ha46
  · exact rv_piece n 46 47 (by norm_num) (by norm_num) ha45.le hb46 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 48 with hb47 | ha47
  · exact rv_piece n 47 48 (by norm_num) (by norm_num) ha46.le hb47 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 49 with hb48 | ha48
  · exact rv_piece n 48 49 (by norm_num) (by norm_num) ha47.le hb48 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 50 with hb49 | ha49
  · exact rv_piece n 49 50 (by norm_num) (by norm_num) ha48.le hb49 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 51 with hb50 | ha50
  · exact rv_piece n 50 51 (by norm_num) (by norm_num) ha49.le hb50 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 52 with hb51 | ha51
  · exact rv_piece n 51 52 (by norm_num) (by norm_num) ha50.le hb51 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 53 with hb52 | ha52
  · exact rv_piece n 52 53 (by norm_num) (by norm_num) ha51.le hb52 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 54 with hb53 | ha53
  · exact rv_piece n 53 54 (by norm_num) (by norm_num) ha52.le hb53 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 55 with hb54 | ha54
  · exact rv_piece n 54 55 (by norm_num) (by norm_num) ha53.le hb54 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 56 with hb55 | ha55
  · exact rv_piece n 55 56 (by norm_num) (by norm_num) ha54.le hb55 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 57 with hb56 | ha56
  · exact rv_piece n 56 57 (by norm_num) (by norm_num) ha55.le hb56 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 58 with hb57 | ha57
  · exact rv_piece n 57 58 (by norm_num) (by norm_num) ha56.le hb57 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 59 with hb58 | ha58
  · exact rv_piece n 58 59 (by norm_num) (by norm_num) ha57.le hb58 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 60 with hb59 | ha59
  · exact rv_piece n 59 60 (by norm_num) (by norm_num) ha58.le hb59 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 61 with hb60 | ha60
  · exact rv_piece n 60 61 (by norm_num) (by norm_num) ha59.le hb60 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 62 with hb61 | ha61
  · exact rv_piece n 61 62 (by norm_num) (by norm_num) ha60.le hb61 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 63 with hb62 | ha62
  · exact rv_piece n 62 63 (by norm_num) (by norm_num) ha61.le hb62 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 64 with hb63 | ha63
  · exact rv_piece n 63 64 (by norm_num) (by norm_num) ha62.le hb63 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 65 with hb64 | ha64
  · exact rv_piece n 64 65 (by norm_num) (by norm_num) ha63.le hb64 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 66 with hb65 | ha65
  · exact rv_piece n 65 66 (by norm_num) (by norm_num) ha64.le hb65 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 67 with hb66 | ha66
  · exact rv_piece n 66 67 (by norm_num) (by norm_num) ha65.le hb66 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 68 with hb67 | ha67
  · exact rv_piece n 67 68 (by norm_num) (by norm_num) ha66.le hb67 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 69 with hb68 | ha68
  · exact rv_piece n 68 69 (by norm_num) (by norm_num) ha67.le hb68 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 70 with hb69 | ha69
  · exact rv_piece n 69 70 (by norm_num) (by norm_num) ha68.le hb69 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 71 with hb70 | ha70
  · exact rv_piece n 70 71 (by norm_num) (by norm_num) ha69.le hb70 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 72 with hb71 | ha71
  · exact rv_piece n 71 72 (by norm_num) (by norm_num) ha70.le hb71 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 73 with hb72 | ha72
  · exact rv_piece n 72 73 (by norm_num) (by norm_num) ha71.le hb72 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 74 with hb73 | ha73
  · exact rv_piece n 73 74 (by norm_num) (by norm_num) ha72.le hb73 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 75 with hb74 | ha74
  · exact rv_piece n 74 75 (by norm_num) (by norm_num) ha73.le hb74 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 76 with hb75 | ha75
  · exact rv_piece n 75 76 (by norm_num) (by norm_num) ha74.le hb75 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 77 with hb76 | ha76
  · exact rv_piece n 76 77 (by norm_num) (by norm_num) ha75.le hb76 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 78 with hb77 | ha77
  · exact rv_piece n 77 78 (by norm_num) (by norm_num) ha76.le hb77 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 79 with hb78 | ha78
  · exact rv_piece n 78 79 (by norm_num) (by norm_num) ha77.le hb78 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 80 with hb79 | ha79
  · exact rv_piece n 79 80 (by norm_num) (by norm_num) ha78.le hb79 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 81 with hb80 | ha80
  · exact rv_piece n 80 81 (by norm_num) (by norm_num) ha79.le hb80 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 82 with hb81 | ha81
  · exact rv_piece n 81 82 (by norm_num) (by norm_num) ha80.le hb81 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 83 with hb82 | ha82
  · exact rv_piece n 82 83 (by norm_num) (by norm_num) ha81.le hb82 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 84 with hb83 | ha83
  · exact rv_piece n 83 84 (by norm_num) (by norm_num) ha82.le hb83 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 85 with hb84 | ha84
  · exact rv_piece n 84 85 (by norm_num) (by norm_num) ha83.le hb84 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 86 with hb85 | ha85
  · exact rv_piece n 85 86 (by norm_num) (by norm_num) ha84.le hb85 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 87 with hb86 | ha86
  · exact rv_piece n 86 87 (by norm_num) (by norm_num) ha85.le hb86 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 88 with hb87 | ha87
  · exact rv_piece n 87 88 (by norm_num) (by norm_num) ha86.le hb87 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 89 with hb88 | ha88
  · exact rv_piece n 88 89 (by norm_num) (by norm_num) ha87.le hb88 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 90 with hb89 | ha89
  · exact rv_piece n 89 90 (by norm_num) (by norm_num) ha88.le hb89 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 91 with hb90 | ha90
  · exact rv_piece n 90 91 (by norm_num) (by norm_num) ha89.le hb90 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 92 with hb91 | ha91
  · exact rv_piece n 91 92 (by norm_num) (by norm_num) ha90.le hb91 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 93 with hb92 | ha92
  · exact rv_piece n 92 93 (by norm_num) (by norm_num) ha91.le hb92 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 94 with hb93 | ha93
  · exact rv_piece n 93 94 (by norm_num) (by norm_num) ha92.le hb93 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 95 with hb94 | ha94
  · exact rv_piece n 94 95 (by norm_num) (by norm_num) ha93.le hb94 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 96 with hb95 | ha95
  · exact rv_piece n 95 96 (by norm_num) (by norm_num) ha94.le hb95 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 97 with hb96 | ha96
  · exact rv_piece n 96 97 (by norm_num) (by norm_num) ha95.le hb96 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 98 with hb97 | ha97
  · exact rv_piece n 97 98 (by norm_num) (by norm_num) ha96.le hb97 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 99 with hb98 | ha98
  · exact rv_piece n 98 99 (by norm_num) (by norm_num) ha97.le hb98 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 100 with hb99 | ha99
  · exact rv_piece n 99 100 (by norm_num) (by norm_num) ha98.le hb99 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 101 with hb100 | ha100
  · exact rv_piece n 100 101 (by norm_num) (by norm_num) ha99.le hb100 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 102 with hb101 | ha101
  · exact rv_piece n 101 102 (by norm_num) (by norm_num) ha100.le hb101 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 103 with hb102 | ha102
  · exact rv_piece n 102 103 (by norm_num) (by norm_num) ha101.le hb102 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 104 with hb103 | ha103
  · exact rv_piece n 103 104 (by norm_num) (by norm_num) ha102.le hb103 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 105 with hb104 | ha104
  · exact rv_piece n 104 105 (by norm_num) (by norm_num) ha103.le hb104 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 106 with hb105 | ha105
  · exact rv_piece n 105 106 (by norm_num) (by norm_num) ha104.le hb105 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 107 with hb106 | ha106
  · exact rv_piece n 106 107 (by norm_num) (by norm_num) ha105.le hb106 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 108 with hb107 | ha107
  · exact rv_piece n 107 108 (by norm_num) (by norm_num) ha106.le hb107 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 109 with hb108 | ha108
  · exact rv_piece n 108 109 (by norm_num) (by norm_num) ha107.le hb108 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 110 with hb109 | ha109
  · exact rv_piece n 109 110 (by norm_num) (by norm_num) ha108.le hb109 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 111 with hb110 | ha110
  · exact rv_piece n 110 111 (by norm_num) (by norm_num) ha109.le hb110 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 112 with hb111 | ha111
  · exact rv_piece n 111 112 (by norm_num) (by norm_num) ha110.le hb111 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 113 with hb112 | ha112
  · exact rv_piece n 112 113 (by norm_num) (by norm_num) ha111.le hb112 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 114 with hb113 | ha113
  · exact rv_piece n 113 114 (by norm_num) (by norm_num) ha112.le hb113 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 115 with hb114 | ha114
  · exact rv_piece n 114 115 (by norm_num) (by norm_num) ha113.le hb114 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 116 with hb115 | ha115
  · exact rv_piece n 115 116 (by norm_num) (by norm_num) ha114.le hb115 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 117 with hb116 | ha116
  · exact rv_piece n 116 117 (by norm_num) (by norm_num) ha115.le hb116 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 118 with hb117 | ha117
  · exact rv_piece n 117 118 (by norm_num) (by norm_num) ha116.le hb117 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 119 with hb118 | ha118
  · exact rv_piece n 118 119 (by norm_num) (by norm_num) ha117.le hb118 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 120 with hb119 | ha119
  · exact rv_piece n 119 120 (by norm_num) (by norm_num) ha118.le hb119 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 121 with hb120 | ha120
  · exact rv_piece n 120 121 (by norm_num) (by norm_num) ha119.le hb120 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 122 with hb121 | ha121
  · exact rv_piece n 121 122 (by norm_num) (by norm_num) ha120.le hb121 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 123 with hb122 | ha122
  · exact rv_piece n 122 123 (by norm_num) (by norm_num) ha121.le hb122 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 124 with hb123 | ha123
  · exact rv_piece n 123 124 (by norm_num) (by norm_num) ha122.le hb123 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 125 with hb124 | ha124
  · exact rv_piece n 124 125 (by norm_num) (by norm_num) ha123.le hb124 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 126 with hb125 | ha125
  · exact rv_piece n 125 126 (by norm_num) (by norm_num) ha124.le hb125 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 127 with hb126 | ha126
  · exact rv_piece n 126 127 (by norm_num) (by norm_num) ha125.le hb126 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 128 with hb127 | ha127
  · exact rv_piece n 127 128 (by norm_num) (by norm_num) ha126.le hb127 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 129 with hb128 | ha128
  · exact rv_piece n 128 129 (by norm_num) (by norm_num) ha127.le hb128 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 130 with hb129 | ha129
  · exact rv_piece n 129 130 (by norm_num) (by norm_num) ha128.le hb129 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 131 with hb130 | ha130
  · exact rv_piece n 130 131 (by norm_num) (by norm_num) ha129.le hb130 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 132 with hb131 | ha131
  · exact rv_piece n 131 132 (by norm_num) (by norm_num) ha130.le hb131 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 133 with hb132 | ha132
  · exact rv_piece n 132 133 (by norm_num) (by norm_num) ha131.le hb132 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 134 with hb133 | ha133
  · exact rv_piece n 133 134 (by norm_num) (by norm_num) ha132.le hb133 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 135 with hb134 | ha134
  · exact rv_piece n 134 135 (by norm_num) (by norm_num) ha133.le hb134 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 136 with hb135 | ha135
  · exact rv_piece n 135 136 (by norm_num) (by norm_num) ha134.le hb135 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 137 with hb136 | ha136
  · exact rv_piece n 136 137 (by norm_num) (by norm_num) ha135.le hb136 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 138 with hb137 | ha137
  · exact rv_piece n 137 138 (by norm_num) (by norm_num) ha136.le hb137 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 139 with hb138 | ha138
  · exact rv_piece n 138 139 (by norm_num) (by norm_num) ha137.le hb138 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 140 with hb139 | ha139
  · exact rv_piece n 139 140 (by norm_num) (by norm_num) ha138.le hb139 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 141 with hb140 | ha140
  · exact rv_piece n 140 141 (by norm_num) (by norm_num) ha139.le hb140 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 142 with hb141 | ha141
  · exact rv_piece n 141 142 (by norm_num) (by norm_num) ha140.le hb141 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 143 with hb142 | ha142
  · exact rv_piece n 142 143 (by norm_num) (by norm_num) ha141.le hb142 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 144 with hb143 | ha143
  · exact rv_piece n 143 144 (by norm_num) (by norm_num) ha142.le hb143 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 145 with hb144 | ha144
  · exact rv_piece n 144 145 (by norm_num) (by norm_num) ha143.le hb144 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 146 with hb145 | ha145
  · exact rv_piece n 145 146 (by norm_num) (by norm_num) ha144.le hb145 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 147 with hb146 | ha146
  · exact rv_piece n 146 147 (by norm_num) (by norm_num) ha145.le hb146 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 148 with hb147 | ha147
  · exact rv_piece n 147 148 (by norm_num) (by norm_num) ha146.le hb147 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 149 with hb148 | ha148
  · exact rv_piece n 148 149 (by norm_num) (by norm_num) ha147.le hb148 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 150 with hb149 | ha149
  · exact rv_piece n 149 150 (by norm_num) (by norm_num) ha148.le hb149 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 151 with hb150 | ha150
  · exact rv_piece n 150 151 (by norm_num) (by norm_num) ha149.le hb150 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 152 with hb151 | ha151
  · exact rv_piece n 151 152 (by norm_num) (by norm_num) ha150.le hb151 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 153 with hb152 | ha152
  · exact rv_piece n 152 153 (by norm_num) (by norm_num) ha151.le hb152 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 154 with hb153 | ha153
  · exact rv_piece n 153 154 (by norm_num) (by norm_num) ha152.le hb153 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 155 with hb154 | ha154
  · exact rv_piece n 154 155 (by norm_num) (by norm_num) ha153.le hb154 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 156 with hb155 | ha155
  · exact rv_piece n 155 156 (by norm_num) (by norm_num) ha154.le hb155 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 157 with hb156 | ha156
  · exact rv_piece n 156 157 (by norm_num) (by norm_num) ha155.le hb156 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 158 with hb157 | ha157
  · exact rv_piece n 157 158 (by norm_num) (by norm_num) ha156.le hb157 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 159 with hb158 | ha158
  · exact rv_piece n 158 159 (by norm_num) (by norm_num) ha157.le hb158 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 160 with hb159 | ha159
  · exact rv_piece n 159 160 (by norm_num) (by norm_num) ha158.le hb159 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 161 with hb160 | ha160
  · exact rv_piece n 160 161 (by norm_num) (by norm_num) ha159.le hb160 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 162 with hb161 | ha161
  · exact rv_piece n 161 162 (by norm_num) (by norm_num) ha160.le hb161 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 163 with hb162 | ha162
  · exact rv_piece n 162 163 (by norm_num) (by norm_num) ha161.le hb162 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 164 with hb163 | ha163
  · exact rv_piece n 163 164 (by norm_num) (by norm_num) ha162.le hb163 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 165 with hb164 | ha164
  · exact rv_piece n 164 165 (by norm_num) (by norm_num) ha163.le hb164 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 166 with hb165 | ha165
  · exact rv_piece n 165 166 (by norm_num) (by norm_num) ha164.le hb165 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 167 with hb166 | ha166
  · exact rv_piece n 166 167 (by norm_num) (by norm_num) ha165.le hb166 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 168 with hb167 | ha167
  · exact rv_piece n 167 168 (by norm_num) (by norm_num) ha166.le hb167 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 169 with hb168 | ha168
  · exact rv_piece n 168 169 (by norm_num) (by norm_num) ha167.le hb168 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 170 with hb169 | ha169
  · exact rv_piece n 169 170 (by norm_num) (by norm_num) ha168.le hb169 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 171 with hb170 | ha170
  · exact rv_piece n 170 171 (by norm_num) (by norm_num) ha169.le hb170 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 172 with hb171 | ha171
  · exact rv_piece n 171 172 (by norm_num) (by norm_num) ha170.le hb171 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 173 with hb172 | ha172
  · exact rv_piece n 172 173 (by norm_num) (by norm_num) ha171.le hb172 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 174 with hb173 | ha173
  · exact rv_piece n 173 174 (by norm_num) (by norm_num) ha172.le hb173 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 175 with hb174 | ha174
  · exact rv_piece n 174 175 (by norm_num) (by norm_num) ha173.le hb174 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 176 with hb175 | ha175
  · exact rv_piece n 175 176 (by norm_num) (by norm_num) ha174.le hb175 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 177 with hb176 | ha176
  · exact rv_piece n 176 177 (by norm_num) (by norm_num) ha175.le hb176 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 178 with hb177 | ha177
  · exact rv_piece n 177 178 (by norm_num) (by norm_num) ha176.le hb177 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 179 with hb178 | ha178
  · exact rv_piece n 178 179 (by norm_num) (by norm_num) ha177.le hb178 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 180 with hb179 | ha179
  · exact rv_piece n 179 180 (by norm_num) (by norm_num) ha178.le hb179 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 181 with hb180 | ha180
  · exact rv_piece n 180 181 (by norm_num) (by norm_num) ha179.le hb180 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 182 with hb181 | ha181
  · exact rv_piece n 181 182 (by norm_num) (by norm_num) ha180.le hb181 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 183 with hb182 | ha182
  · exact rv_piece n 182 183 (by norm_num) (by norm_num) ha181.le hb182 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 184 with hb183 | ha183
  · exact rv_piece n 183 184 (by norm_num) (by norm_num) ha182.le hb183 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 185 with hb184 | ha184
  · exact rv_piece n 184 185 (by norm_num) (by norm_num) ha183.le hb184 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 186 with hb185 | ha185
  · exact rv_piece n 185 186 (by norm_num) (by norm_num) ha184.le hb185 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 187 with hb186 | ha186
  · exact rv_piece n 186 187 (by norm_num) (by norm_num) ha185.le hb186 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 188 with hb187 | ha187
  · exact rv_piece n 187 188 (by norm_num) (by norm_num) ha186.le hb187 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 189 with hb188 | ha188
  · exact rv_piece n 188 189 (by norm_num) (by norm_num) ha187.le hb188 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 190 with hb189 | ha189
  · exact rv_piece n 189 190 (by norm_num) (by norm_num) ha188.le hb189 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 191 with hb190 | ha190
  · exact rv_piece n 190 191 (by norm_num) (by norm_num) ha189.le hb190 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 192 with hb191 | ha191
  · exact rv_piece n 191 192 (by norm_num) (by norm_num) ha190.le hb191 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 193 with hb192 | ha192
  · exact rv_piece n 192 193 (by norm_num) (by norm_num) ha191.le hb192 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 194 with hb193 | ha193
  · exact rv_piece n 193 194 (by norm_num) (by norm_num) ha192.le hb193 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 195 with hb194 | ha194
  · exact rv_piece n 194 195 (by norm_num) (by norm_num) ha193.le hb194 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 196 with hb195 | ha195
  · exact rv_piece n 195 196 (by norm_num) (by norm_num) ha194.le hb195 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 197 with hb196 | ha196
  · exact rv_piece n 196 197 (by norm_num) (by norm_num) ha195.le hb196 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 198 with hb197 | ha197
  · exact rv_piece n 197 198 (by norm_num) (by norm_num) ha196.le hb197 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 199 with hb198 | ha198
  · exact rv_piece n 198 199 (by norm_num) (by norm_num) ha197.le hb198 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 200 with hb199 | ha199
  · exact rv_piece n 199 200 (by norm_num) (by norm_num) ha198.le hb199 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 201 with hb200 | ha200
  · exact rv_piece n 200 201 (by norm_num) (by norm_num) ha199.le hb200 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 202 with hb201 | ha201
  · exact rv_piece n 201 202 (by norm_num) (by norm_num) ha200.le hb201 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 203 with hb202 | ha202
  · exact rv_piece n 202 203 (by norm_num) (by norm_num) ha201.le hb202 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 204 with hb203 | ha203
  · exact rv_piece n 203 204 (by norm_num) (by norm_num) ha202.le hb203 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 205 with hb204 | ha204
  · exact rv_piece n 204 205 (by norm_num) (by norm_num) ha203.le hb204 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 206 with hb205 | ha205
  · exact rv_piece n 205 206 (by norm_num) (by norm_num) ha204.le hb205 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 207 with hb206 | ha206
  · exact rv_piece n 206 207 (by norm_num) (by norm_num) ha205.le hb206 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 208 with hb207 | ha207
  · exact rv_piece n 207 208 (by norm_num) (by norm_num) ha206.le hb207 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 209 with hb208 | ha208
  · exact rv_piece n 208 209 (by norm_num) (by norm_num) ha207.le hb208 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 210 with hb209 | ha209
  · exact rv_piece n 209 210 (by norm_num) (by norm_num) ha208.le hb209 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 211 with hb210 | ha210
  · exact rv_piece n 210 211 (by norm_num) (by norm_num) ha209.le hb210 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 212 with hb211 | ha211
  · exact rv_piece n 211 212 (by norm_num) (by norm_num) ha210.le hb211 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 213 with hb212 | ha212
  · exact rv_piece n 212 213 (by norm_num) (by norm_num) ha211.le hb212 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 214 with hb213 | ha213
  · exact rv_piece n 213 214 (by norm_num) (by norm_num) ha212.le hb213 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 215 with hb214 | ha214
  · exact rv_piece n 214 215 (by norm_num) (by norm_num) ha213.le hb214 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 216 with hb215 | ha215
  · exact rv_piece n 215 216 (by norm_num) (by norm_num) ha214.le hb215 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 217 with hb216 | ha216
  · exact rv_piece n 216 217 (by norm_num) (by norm_num) ha215.le hb216 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 218 with hb217 | ha217
  · exact rv_piece n 217 218 (by norm_num) (by norm_num) ha216.le hb217 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 219 with hb218 | ha218
  · exact rv_piece n 218 219 (by norm_num) (by norm_num) ha217.le hb218 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 220 with hb219 | ha219
  · exact rv_piece n 219 220 (by norm_num) (by norm_num) ha218.le hb219 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 221 with hb220 | ha220
  · exact rv_piece n 220 221 (by norm_num) (by norm_num) ha219.le hb220 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 222 with hb221 | ha221
  · exact rv_piece n 221 222 (by norm_num) (by norm_num) ha220.le hb221 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 223 with hb222 | ha222
  · exact rv_piece n 222 223 (by norm_num) (by norm_num) ha221.le hb222 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 224 with hb223 | ha223
  · exact rv_piece n 223 224 (by norm_num) (by norm_num) ha222.le hb223 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 225 with hb224 | ha224
  · exact rv_piece n 224 225 (by norm_num) (by norm_num) ha223.le hb224 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 226 with hb225 | ha225
  · exact rv_piece n 225 226 (by norm_num) (by norm_num) ha224.le hb225 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 227 with hb226 | ha226
  · exact rv_piece n 226 227 (by norm_num) (by norm_num) ha225.le hb226 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 228 with hb227 | ha227
  · exact rv_piece n 227 228 (by norm_num) (by norm_num) ha226.le hb227 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 229 with hb228 | ha228
  · exact rv_piece n 228 229 (by norm_num) (by norm_num) ha227.le hb228 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 230 with hb229 | ha229
  · exact rv_piece n 229 230 (by norm_num) (by norm_num) ha228.le hb229 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 231 with hb230 | ha230
  · exact rv_piece n 230 231 (by norm_num) (by norm_num) ha229.le hb230 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 232 with hb231 | ha231
  · exact rv_piece n 231 232 (by norm_num) (by norm_num) ha230.le hb231 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 233 with hb232 | ha232
  · exact rv_piece n 232 233 (by norm_num) (by norm_num) ha231.le hb232 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 234 with hb233 | ha233
  · exact rv_piece n 233 234 (by norm_num) (by norm_num) ha232.le hb233 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 235 with hb234 | ha234
  · exact rv_piece n 234 235 (by norm_num) (by norm_num) ha233.le hb234 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 236 with hb235 | ha235
  · exact rv_piece n 235 236 (by norm_num) (by norm_num) ha234.le hb235 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 237 with hb236 | ha236
  · exact rv_piece n 236 237 (by norm_num) (by norm_num) ha235.le hb236 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 238 with hb237 | ha237
  · exact rv_piece n 237 238 (by norm_num) (by norm_num) ha236.le hb237 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 239 with hb238 | ha238
  · exact rv_piece n 238 239 (by norm_num) (by norm_num) ha237.le hb238 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 240 with hb239 | ha239
  · exact rv_piece n 239 240 (by norm_num) (by norm_num) ha238.le hb239 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 241 with hb240 | ha240
  · exact rv_piece n 240 241 (by norm_num) (by norm_num) ha239.le hb240 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 242 with hb241 | ha241
  · exact rv_piece n 241 242 (by norm_num) (by norm_num) ha240.le hb241 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 243 with hb242 | ha242
  · exact rv_piece n 242 243 (by norm_num) (by norm_num) ha241.le hb242 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 244 with hb243 | ha243
  · exact rv_piece n 243 244 (by norm_num) (by norm_num) ha242.le hb243 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 245 with hb244 | ha244
  · exact rv_piece n 244 245 (by norm_num) (by norm_num) ha243.le hb244 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 246 with hb245 | ha245
  · exact rv_piece n 245 246 (by norm_num) (by norm_num) ha244.le hb245 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 247 with hb246 | ha246
  · exact rv_piece n 246 247 (by norm_num) (by norm_num) ha245.le hb246 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 248 with hb247 | ha247
  · exact rv_piece n 247 248 (by norm_num) (by norm_num) ha246.le hb247 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 249 with hb248 | ha248
  · exact rv_piece n 248 249 (by norm_num) (by norm_num) ha247.le hb248 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 250 with hb249 | ha249
  · exact rv_piece n 249 250 (by norm_num) (by norm_num) ha248.le hb249 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 251 with hb250 | ha250
  · exact rv_piece n 250 251 (by norm_num) (by norm_num) ha249.le hb250 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 252 with hb251 | ha251
  · exact rv_piece n 251 252 (by norm_num) (by norm_num) ha250.le hb251 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 253 with hb252 | ha252
  · exact rv_piece n 252 253 (by norm_num) (by norm_num) ha251.le hb252 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 254 with hb253 | ha253
  · exact rv_piece n 253 254 (by norm_num) (by norm_num) ha252.le hb253 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 255 with hb254 | ha254
  · exact rv_piece n 254 255 (by norm_num) (by norm_num) ha253.le hb254 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 256 with hb255 | ha255
  · exact rv_piece n 255 256 (by norm_num) (by norm_num) ha254.le hb255 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 257 with hb256 | ha256
  · exact rv_piece n 256 257 (by norm_num) (by norm_num) ha255.le hb256 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 258 with hb257 | ha257
  · exact rv_piece n 257 258 (by norm_num) (by norm_num) ha256.le hb257 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 259 with hb258 | ha258
  · exact rv_piece n 258 259 (by norm_num) (by norm_num) ha257.le hb258 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 260 with hb259 | ha259
  · exact rv_piece n 259 260 (by norm_num) (by norm_num) ha258.le hb259 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 261 with hb260 | ha260
  · exact rv_piece n 260 261 (by norm_num) (by norm_num) ha259.le hb260 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 262 with hb261 | ha261
  · exact rv_piece n 261 262 (by norm_num) (by norm_num) ha260.le hb261 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 263 with hb262 | ha262
  · exact rv_piece n 262 263 (by norm_num) (by norm_num) ha261.le hb262 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 264 with hb263 | ha263
  · exact rv_piece n 263 264 (by norm_num) (by norm_num) ha262.le hb263 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 265 with hb264 | ha264
  · exact rv_piece n 264 265 (by norm_num) (by norm_num) ha263.le hb264 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 266 with hb265 | ha265
  · exact rv_piece n 265 266 (by norm_num) (by norm_num) ha264.le hb265 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 267 with hb266 | ha266
  · exact rv_piece n 266 267 (by norm_num) (by norm_num) ha265.le hb266 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 268 with hb267 | ha267
  · exact rv_piece n 267 268 (by norm_num) (by norm_num) ha266.le hb267 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 269 with hb268 | ha268
  · exact rv_piece n 268 269 (by norm_num) (by norm_num) ha267.le hb268 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 270 with hb269 | ha269
  · exact rv_piece n 269 270 (by norm_num) (by norm_num) ha268.le hb269 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 271 with hb270 | ha270
  · exact rv_piece n 270 271 (by norm_num) (by norm_num) ha269.le hb270 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 272 with hb271 | ha271
  · exact rv_piece n 271 272 (by norm_num) (by norm_num) ha270.le hb271 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 273 with hb272 | ha272
  · exact rv_piece n 272 273 (by norm_num) (by norm_num) ha271.le hb272 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 274 with hb273 | ha273
  · exact rv_piece n 273 274 (by norm_num) (by norm_num) ha272.le hb273 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 275 with hb274 | ha274
  · exact rv_piece n 274 275 (by norm_num) (by norm_num) ha273.le hb274 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 276 with hb275 | ha275
  · exact rv_piece n 275 276 (by norm_num) (by norm_num) ha274.le hb275 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 277 with hb276 | ha276
  · exact rv_piece n 276 277 (by norm_num) (by norm_num) ha275.le hb276 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 278 with hb277 | ha277
  · exact rv_piece n 277 278 (by norm_num) (by norm_num) ha276.le hb277 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 279 with hb278 | ha278
  · exact rv_piece n 278 279 (by norm_num) (by norm_num) ha277.le hb278 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 280 with hb279 | ha279
  · exact rv_piece n 279 280 (by norm_num) (by norm_num) ha278.le hb279 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 281 with hb280 | ha280
  · exact rv_piece n 280 281 (by norm_num) (by norm_num) ha279.le hb280 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 282 with hb281 | ha281
  · exact rv_piece n 281 282 (by norm_num) (by norm_num) ha280.le hb281 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 283 with hb282 | ha282
  · exact rv_piece n 282 283 (by norm_num) (by norm_num) ha281.le hb282 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 284 with hb283 | ha283
  · exact rv_piece n 283 284 (by norm_num) (by norm_num) ha282.le hb283 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 285 with hb284 | ha284
  · exact rv_piece n 284 285 (by norm_num) (by norm_num) ha283.le hb284 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 286 with hb285 | ha285
  · exact rv_piece n 285 286 (by norm_num) (by norm_num) ha284.le hb285 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 287 with hb286 | ha286
  · exact rv_piece n 286 287 (by norm_num) (by norm_num) ha285.le hb286 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 288 with hb287 | ha287
  · exact rv_piece n 287 288 (by norm_num) (by norm_num) ha286.le hb287 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 289 with hb288 | ha288
  · exact rv_piece n 288 289 (by norm_num) (by norm_num) ha287.le hb288 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 290 with hb289 | ha289
  · exact rv_piece n 289 290 (by norm_num) (by norm_num) ha288.le hb289 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 291 with hb290 | ha290
  · exact rv_piece n 290 291 (by norm_num) (by norm_num) ha289.le hb290 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 292 with hb291 | ha291
  · exact rv_piece n 291 292 (by norm_num) (by norm_num) ha290.le hb291 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 293 with hb292 | ha292
  · exact rv_piece n 292 293 (by norm_num) (by norm_num) ha291.le hb292 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 294 with hb293 | ha293
  · exact rv_piece n 293 294 (by norm_num) (by norm_num) ha292.le hb293 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 295 with hb294 | ha294
  · exact rv_piece n 294 295 (by norm_num) (by norm_num) ha293.le hb294 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 296 with hb295 | ha295
  · exact rv_piece n 295 296 (by norm_num) (by norm_num) ha294.le hb295 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 297 with hb296 | ha296
  · exact rv_piece n 296 297 (by norm_num) (by norm_num) ha295.le hb296 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 298 with hb297 | ha297
  · exact rv_piece n 297 298 (by norm_num) (by norm_num) ha296.le hb297 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 299 with hb298 | ha298
  · exact rv_piece n 298 299 (by norm_num) (by norm_num) ha297.le hb298 (by norm_num) (by norm_num)
  exact rv_piece n 299 300 (by norm_num) (by norm_num) ha298.le h2 (by norm_num) (by norm_num)

end P27




/-! ## part: Phi -/

open Real

namespace RV27E

/-- `φ(x) = x / log² x`. -/
noncomputable def phi (x : ℝ) : ℝ := x / (log x) ^ 2

lemma g_anti {l l' : ℝ} (hl : 3 ≤ l) (hll : l ≤ l') :
    (l' - 2) / l' ^ 3 ≤ (l - 2) / l ^ 3 := by
  have h0 : 0 < l := by linarith
  have h0' : 0 < l' := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  obtain ⟨d, hd, rfl⟩ : ∃ d, 0 ≤ d ∧ l' = l + d := ⟨l' - l, by linarith, by ring⟩
  have : (l + d - 2) * l ^ 3 ≤ (l - 2) * (l + d) ^ 3 := by
    have e : (l - 2) * (l + d) ^ 3 - (l + d - 2) * l ^ 3 =
        d * ((2 * l - 6) * l ^ 2 + 3 * (l - 2) * l * d + (l - 2) * d ^ 2 + 0 * l) := by ring
    have : 0 ≤ d * ((2 * l - 6) * l ^ 2 + 3 * (l - 2) * l * d + (l - 2) * d ^ 2 + 0 * l) := by
      apply mul_nonneg hd
      have h1 : 0 ≤ (2 * l - 6) * l ^ 2 := mul_nonneg (by linarith) (by positivity)
      have h2 : 0 ≤ 3 * (l - 2) * l * d := by
        apply mul_nonneg (mul_nonneg (by linarith) h0.le) hd
      have h3 : 0 ≤ (l - 2) * d ^ 2 := mul_nonneg (by linarith) (by positivity)
      linarith
    linarith
  linarith

lemma hasDerivAt_phi {x : ℝ} (hx : 1 < x) :
    HasDerivAt phi ((log x - 2) / (log x) ^ 3) x := by
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos hx
  have h3 : HasDerivAt (fun y => y / (log y * log y))
      ((1 * (log x * log x) - x * (x⁻¹ * log x + log x * x⁻¹)) / (log x * log x) ^ 2) x :=
    (hasDerivAt_id' (x := x)).fun_div ((hasDerivAt_log hx0.ne').mul (hasDerivAt_log hx0.ne')) (by positivity)
  have e : phi = fun y => y / (log y * log y) := by funext y; simp [phi, pow_two]
  rw [e]
  convert h3 using 1
  field_simp
  ring

lemma phi_concave : ConcaveOn ℝ (Set.Ici (exp 3)) phi := by
  have he : (1 : ℝ) < exp 3 := by
    have := add_one_le_exp (3 : ℝ); linarith
  apply AntitoneOn.concaveOn_of_deriv (convex_Ici _)
  · intro x hx
    have hx1 : 1 < x := lt_of_lt_of_le he hx
    exact (hasDerivAt_phi hx1).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx1 : 1 < x := lt_trans he hx
    exact (hasDerivAt_phi hx1).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro x hx x' hx' hxx
    have hx1 : 1 < x := lt_trans he hx
    have hx1' : 1 < x' := lt_trans he hx'
    rw [(hasDerivAt_phi hx1).deriv, (hasDerivAt_phi hx1').deriv]
    have hl : 3 ≤ log x := by
      have := log_le_log (exp_pos 3) (le_of_lt hx); rwa [log_exp] at this
    exact g_anti hl (log_le_log (by linarith) hxx)

lemma phi_mono {a b : ℝ} (ha : exp 3 ≤ a) (hab : a ≤ b) : phi a ≤ phi b := by
  have he : (1 : ℝ) < exp 3 := by
    have := add_one_le_exp (3 : ℝ); linarith
  have hmono : MonotoneOn phi (Set.Ici (exp 3)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · intro x hx
      exact (hasDerivAt_phi (lt_of_lt_of_le he hx)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact (hasDerivAt_phi (lt_trans he hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hasDerivAt_phi (lt_trans he hx)).deriv]
      have hl : 3 ≤ log x := by
        have := log_le_log (exp_pos 3) (le_of_lt hx); rwa [log_exp] at this
      apply div_nonneg (by linarith) (by positivity)
  exact hmono ha (le_trans ha hab) hab

/-- concavity: `φ(a) + φ(b) ≤ 2 φ((a+b)/2)` for `a, b ≥ e³`. -/
lemma phi_add_le {a b : ℝ} (ha : exp 3 ≤ a) (hb : exp 3 ≤ b) :
    phi a + phi b ≤ 2 * phi ((a + b) / 2) := by
  have := phi_concave.2 ha hb (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  simp only [smul_eq_mul] at this
  have e : 1 / 2 * a + 1 / 2 * b = (a + b) / 2 := by ring
  rw [e] at this
  linarith

lemma exp3_le : exp 3 ≤ 25600 := by
  have := exp_one_lt_d9
  have h : exp 3 = exp 1 ^ 3 := by rw [← exp_nat_mul]; norm_num
  rw [h]
  have h0 := exp_pos 1
  nlinarith [pow_le_pow_left₀ h0.le this.le 3]

end RV27E

/-! ## part: Upper -/

open Finset Real

namespace RV27E

/-- Goldbach representations `s = p + (s - p)` with `p ∈ (a, a + L]`. -/
def G (s a L : ℕ) : ℕ := ((Finset.Ioc a (a + L)).filter (fun p => p.Prime ∧ p < s ∧ (s - p).Prime)).card

/-- primes in `I_k = (k h, k h + 2h]`. -/
def T (h k : ℕ) : Finset ℕ := (Finset.Ioc (k * h) (k * h + 2 * h)).filter Nat.Prime

/-- pairs `(t, t') ∈ T_k²` with `t + t' = m`. -/
def Npair (h k m : ℕ) : ℕ := ((T h k ×ˢ T h k).filter (fun x => x.1 + x.2 = m)).card

lemma mem_T {h k t : ℕ} : t ∈ T h k ↔ k * h < t ∧ t ≤ k * h + 2 * h ∧ t.Prime := by
  simp [T, and_assoc]

lemma Npair_le_G (h k m a L : ℕ)
    (hsub : ∀ t t', t ∈ T h k → t' ∈ T h k → t + t' = m → a < t ∧ t ≤ a + L) :
    Npair h k m ≤ G m a L := by
  unfold Npair G
  apply card_le_card_of_injOn Prod.fst
  · intro x hx
    simp only [coe_filter, Set.mem_setOf_eq, mem_product] at hx
    obtain ⟨⟨h1, h2⟩, hs⟩ := hx
    have hp1 := (mem_T.1 h1).2.2
    have hp2 := (mem_T.1 h2).2.2
    have := hsub x.1 x.2 h1 h2 hs
    simp only [coe_filter, Set.mem_setOf_eq, mem_Ioc]
    refine ⟨this, hp1, by have := hp2.two_le; omega, ?_⟩
    have : m - x.1 = x.2 := by omega
    rw [this]; exact hp2
  · intro x hx y hy hxy
    simp only [mem_coe, mem_filter] at hx hy
    have : x.2 = y.2 := by have := hx.2; have := hy.2; omega
    exact Prod.ext hxy this

lemma Npair_eq_zero (h k m : ℕ)
    (hno : ∀ t t', t ∈ T h k → t' ∈ T h k → t + t' ≠ m) : Npair h k m = 0 := by
  unfold Npair
  rw [card_eq_zero, filter_eq_empty_iff]
  intro x hx
  rw [mem_product] at hx
  exact hno x.1 x.2 hx.1 hx.2

/-- at most two intervals contribute, through nested ranges of lengths `v - 1` and `2h - v + 1`. -/
lemma Npair_le (h k m : ℕ) (hh : 1 ≤ h) (hm : 2 ≤ m) :
    Npair h k m ≤
      (if k = (m - 2) / (2 * h) then
          G m ((m - 2) / (2 * h) * h) (m - 2 * ((m - 2) / (2 * h) * h) - 1) else 0) +
      (if k + 1 = (m - 2) / (2 * h) then
          G m (k * h + (m - 2 * ((m - 2) / (2 * h) * h)) - 1)
            (2 * h + 1 - (m - 2 * ((m - 2) / (2 * h) * h))) else 0) := by
  set k1 := (m - 2) / (2 * h) with hk1
  set P := k1 * h with hP
  have hd1 : 2 * P ≤ m - 2 := by
    have := Nat.div_mul_le_self (m - 2) (2 * h)
    rw [← hk1] at this; rw [hP]; nlinarith
  have hd2 : m - 2 < 2 * P + 2 * h := by
    have := Nat.lt_mul_div_succ (m - 2) (show 0 < 2 * h by omega)
    rw [← hk1] at this; rw [hP]; nlinarith
  by_cases hk : k = k1
  · rw [if_pos hk]
    refine le_trans ?_ (Nat.le_add_right _ _)
    apply Npair_le_G
    intro t t' ht ht' hs
    rw [mem_T, hk, ← hP] at ht ht'
    omega
  · rw [if_neg hk, zero_add]
    by_cases hk' : k + 1 = k1
    · rw [if_pos hk']
      apply Npair_le_G
      intro t t' ht ht' hs
      rw [mem_T] at ht ht'
      have : k * h + h = P := by rw [hP, ← hk']; ring
      omega
    · rw [if_neg hk']
      apply le_of_eq
      apply Npair_eq_zero
      intro t t' ht ht' hs
      rw [mem_T] at ht ht'
      rcases lt_or_gt_of_ne hk with hlt | hgt
      · have : k + 2 ≤ k1 := by omega
        have : k * h + 2 * h ≤ P := by rw [hP]; nlinarith
        omega
      · have : P + h ≤ k * h := by rw [hP]; nlinarith
        omega

lemma Npair_sum_le (K h m : ℕ) (hh : 1 ≤ h) (hm : 2 ≤ m) :
    ∑ k ∈ Icc 1 K, Npair h k m ≤
      G m ((m - 2) / (2 * h) * h) (m - 2 * ((m - 2) / (2 * h) * h) - 1) +
      G m (((m - 2) / (2 * h) - 1) * h + (m - 2 * ((m - 2) / (2 * h) * h)) - 1)
            (2 * h + 1 - (m - 2 * ((m - 2) / (2 * h) * h))) := by
  set k1 := (m - 2) / (2 * h) with hk1
  set v := m - 2 * (k1 * h) with hv
  calc ∑ k ∈ Icc 1 K, Npair h k m
      ≤ ∑ k ∈ Icc 1 K, ((if k = k1 then G m (k1 * h) (v - 1) else 0) +
          (if k + 1 = k1 then G m (k * h + v - 1) (2 * h + 1 - v) else 0)) :=
        sum_le_sum fun k _ => Npair_le h k m hh hm
    _ = ∑ k ∈ Icc 1 K, (if k = k1 then G m (k1 * h) (v - 1) else 0) +
          ∑ k ∈ Icc 1 K, (if k + 1 = k1 then G m (k * h + v - 1) (2 * h + 1 - v) else 0) :=
        sum_add_distrib
    _ ≤ G m (k1 * h) (v - 1) + G m ((k1 - 1) * h + v - 1) (2 * h + 1 - v) := by
        apply add_le_add
        · rw [sum_ite_eq']; split_ifs <;> simp
        · have : ∀ k ∈ Icc 1 K, (if k + 1 = k1 then G m (k * h + v - 1) (2 * h + 1 - v) else 0) =
              if k = k1 - 1 ∧ 1 ≤ k1 then G m ((k1 - 1) * h + v - 1) (2 * h + 1 - v) else 0 := by
            intro k _
            by_cases hkk : k + 1 = k1
            · rw [if_pos hkk, if_pos ⟨by omega, by omega⟩]
              have : k = k1 - 1 := by omega
              rw [this]
            · rw [if_neg hkk, if_neg (by omega)]
          rw [sum_congr rfl this]
          by_cases h1 : 1 ≤ k1
          · simp only [h1, and_true]
            rw [sum_ite_eq']; split_ifs <;> simp
          · simp [h1]

/-- the singular-series factor `K(s)`. -/
noncomputable def Kp (s : ℕ) : ℝ :=
  ∏ p ∈ s.primeFactors, if 2 < p then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1

lemma Kp_nonneg (s : ℕ) : 0 ≤ Kp s := by
  unfold Kp
  apply prod_nonneg
  intro p _
  split_ifs with h
  · have : (2 : ℝ) < p := by exact_mod_cast h
    apply div_nonneg <;> linarith
  · norm_num

lemma C_nonneg : 0 ≤ TaoFivePrimes.twinPrimeConstant := by
  have := PrimePairSieve.sieve_constants_certificate.1; linarith

lemma G_le_L (s a L : ℕ) : G s a L ≤ L := by
  unfold G
  calc _ ≤ (Finset.Ioc a (a + L)).card := card_filter_le _ _
    _ = L := by simp

lemma G_le_B (s a L : ℕ) (hs : Even s) (hs0 : 0 < s) (hL : 25600 ≤ L) :
    (G s a L : ℝ) ≤ 8 * TaoFivePrimes.twinPrimeConstant * Kp s * phi L + √(L : ℝ) / 2 + 2 := by
  have := RV27.interval_goldbach_bound s a L hs hs0 hL
  unfold G
  convert this using 2
  unfold phi Kp; ring

lemma phi_nonneg (x : ℝ) : 0 ≤ x → 0 ≤ phi x := fun hx => by unfold phi; positivity

lemma phi_two_mul (h : ℝ) (hh : 1 < h) : phi (2 * h) ≤ 2 * phi h := by
  unfold phi
  have h1 : 0 < log h := log_pos hh
  have h2 : log h ≤ log (2 * h) := log_le_log (by linarith) (by linarith)
  have h3 : 0 < log (2 * h) := lt_of_lt_of_le h1 h2
  have : (log h) ^ 2 ≤ (log (2 * h)) ^ 2 := pow_le_pow_left₀ h1.le h2 2
  rw [div_le_iff₀ (by positivity)]
  calc 2 * h = 2 * h / (log h) ^ 2 * (log h) ^ 2 := by field_simp
    _ ≤ 2 * h / (log h) ^ 2 * (log (2 * h)) ^ 2 := by gcongr
    _ = _ := by ring

/-- one interval of length `L ≤ 2h`. -/
lemma G_le_one (s a L h : ℕ) (hs : Even s) (hs0 : 0 < s) (hLh : L ≤ 2 * h) :
    (G s a L : ℝ) ≤ (if 25600 ≤ L then 8 * TaoFivePrimes.twinPrimeConstant * Kp s * phi L + √(2 * (h : ℝ)) / 2 + 2
      else 25600) := by
  split_ifs with hL
  · have := G_le_B s a L hs hs0 hL
    have h2 : √(L : ℝ) ≤ √(2 * (h : ℝ)) := Real.sqrt_le_sqrt (by exact_mod_cast hLh)
    linarith
  · have := G_le_L s a L
    have : (G s a L : ℝ) ≤ L := by exact_mod_cast this
    have : (L : ℝ) ≤ 25600 := by exact_mod_cast (show L ≤ 25600 by omega)
    linarith

/-- **Lemma 9** (Riesel–Vaughan), interval form. -/
theorem pair_sum_le (K h m : ℕ) (hh : 25600 ≤ h) (hm : Even m) (hm0 : 0 < m) :
    ((∑ k ∈ Icc 1 K, Npair h k m : ℕ) : ℝ) ≤
      16 * TaoFivePrimes.twinPrimeConstant * Kp m * phi h + √(2 * (h : ℝ)) + 51204 := by
  have hm2 : 2 ≤ m := by obtain ⟨j, hj⟩ := hm; omega
  have h1 := Npair_sum_le K h m (by omega) hm2
  set k1 := (m - 2) / (2 * h) with hk1
  set v := m - 2 * (k1 * h) with hv
  have hd1 : 2 * (k1 * h) ≤ m - 2 := by
    have := Nat.div_mul_le_self (m - 2) (2 * h)
    rw [← hk1] at this; nlinarith
  have hd2 : m - 2 < 2 * (k1 * h) + 2 * h := by
    have := Nat.lt_mul_div_succ (m - 2) (show 0 < 2 * h by omega)
    rw [← hk1] at this; nlinarith
  set L1 := v - 1 with hL1
  set L2 := 2 * h + 1 - v with hL2
  have hsum : (L1 : ℝ) + L2 = 2 * h := by
    have : L1 + L2 = 2 * h := by
      clear_value k1 v L1 L2
      subst hL1 hL2 hv
      omega
    exact_mod_cast this
  have hb1 := G_le_one m (k1 * h) L1 h hm hm0 (by omega)
  have hb2 := G_le_one m ((k1 - 1) * h + v - 1) L2 h hm hm0 (by omega)
  have hcast : ((∑ k ∈ Icc 1 K, Npair h k m : ℕ) : ℝ) ≤
      (G m (k1 * h) L1 : ℝ) + G m ((k1 - 1) * h + v - 1) L2 := by exact_mod_cast h1
  have hC := C_nonneg
  have hK := Kp_nonneg m
  have hCK : 0 ≤ TaoFivePrimes.twinPrimeConstant * Kp m := mul_nonneg hC hK
  have hhR : (25600 : ℝ) ≤ h := by exact_mod_cast hh
  have hph := phi_nonneg (h : ℝ) (by linarith)
  have he3 := exp3_le
  have hsq : 0 ≤ √(2 * (h : ℝ)) := Real.sqrt_nonneg _
  -- monotone bound for a single long interval
  have hlong : ∀ L : ℕ, 25600 ≤ L → L ≤ 2 * h → phi L ≤ 2 * phi h := by
    intro L hL hLh
    have hLR : (25600 : ℝ) ≤ L := by exact_mod_cast hL
    have := phi_mono (a := (L : ℝ)) (b := 2 * (h : ℝ)) (by linarith) (by exact_mod_cast hLh)
    exact this.trans (phi_two_mul h (by linarith))
  by_cases c1 : 25600 ≤ L1 <;> by_cases c2 : 25600 ≤ L2 <;>
    simp only [c1, c2, if_true, if_false] at hb1 hb2
  · have hL1R : (25600 : ℝ) ≤ L1 := by exact_mod_cast c1
    have hL2R : (25600 : ℝ) ≤ L2 := by exact_mod_cast c2
    have hc := phi_add_le (a := (L1 : ℝ)) (b := L2) (by linarith) (by linarith)
    rw [hsum, show 2 * (h : ℝ) / 2 = h by ring] at hc
    have : 8 * TaoFivePrimes.twinPrimeConstant * Kp m * phi L1 +
        8 * TaoFivePrimes.twinPrimeConstant * Kp m * phi L2 ≤
        16 * TaoFivePrimes.twinPrimeConstant * Kp m * phi h := by
      have := mul_le_mul_of_nonneg_left hc hCK
      have e1 : 8 * TaoFivePrimes.twinPrimeConstant * Kp m * phi L1 +
          8 * TaoFivePrimes.twinPrimeConstant * Kp m * phi L2 =
          8 * (TaoFivePrimes.twinPrimeConstant * Kp m * (phi L1 + phi L2)) := by ring
      have e2 : 16 * TaoFivePrimes.twinPrimeConstant * Kp m * phi h =
          8 * (TaoFivePrimes.twinPrimeConstant * Kp m * (2 * phi h)) := by ring
      rw [e1, e2]; linarith
    linarith
  · have := hlong L1 c1 (by omega)
    have : 8 * TaoFivePrimes.twinPrimeConstant * Kp m * phi L1 ≤
        16 * TaoFivePrimes.twinPrimeConstant * Kp m * phi h := by
      have := mul_le_mul_of_nonneg_left this hCK
      have e1 : 8 * TaoFivePrimes.twinPrimeConstant * Kp m * phi L1 =
          8 * (TaoFivePrimes.twinPrimeConstant * Kp m * phi L1) := by ring
      have e2 : 16 * TaoFivePrimes.twinPrimeConstant * Kp m * phi h =
          8 * (TaoFivePrimes.twinPrimeConstant * Kp m * (2 * phi h)) := by ring
      rw [e1, e2]; linarith
    linarith
  · have := hlong L2 c2 (by omega)
    have : 8 * TaoFivePrimes.twinPrimeConstant * Kp m * phi L2 ≤
        16 * TaoFivePrimes.twinPrimeConstant * Kp m * phi h := by
      have := mul_le_mul_of_nonneg_left this hCK
      have e1 : 8 * TaoFivePrimes.twinPrimeConstant * Kp m * phi L2 =
          8 * (TaoFivePrimes.twinPrimeConstant * Kp m * phi L2) := by ring
      have e2 : 16 * TaoFivePrimes.twinPrimeConstant * Kp m * phi h =
          8 * (TaoFivePrimes.twinPrimeConstant * Kp m * (2 * phi h)) := by ring
      rw [e1, e2]; linarith
    linarith
  · have : 0 ≤ 16 * TaoFivePrimes.twinPrimeConstant * Kp m * phi h := by
      have := mul_nonneg hCK hph; linarith
    linarith

end RV27E

/-! ## part: Weight -/

open Finset Real

namespace RV27E

/-- odd primes `≤ E`. -/
def Sset (E : ℕ) : Finset ℕ := (range (E + 1)).filter (fun p => p.Prime ∧ p ≠ 2)

/-- truncated weight `w_S(m) = ∏_{p ∈ S, p ∣ m} (p-2)/(p-1)`. -/
noncomputable def wS (S : Finset ℕ) (m : ℕ) : ℝ :=
  ∏ p ∈ S, if p ∣ m then ((p : ℝ) - 2) / ((p : ℝ) - 1) else 1

lemma three_le_of_mem_Sset {E p : ℕ} (hp : p ∈ Sset E) : 3 ≤ p := by
  simp only [Sset, mem_filter, mem_range] at hp
  have := hp.2.1.two_le; omega

lemma wS_nonneg (E m : ℕ) : 0 ≤ wS (Sset E) m := by
  unfold wS
  apply prod_nonneg
  intro p hp
  have h3 : (3 : ℝ) ≤ p := by exact_mod_cast three_le_of_mem_Sset hp
  split_ifs
  · apply div_nonneg <;> linarith
  · norm_num

lemma wS_le_one (E m : ℕ) : wS (Sset E) m ≤ 1 := by
  unfold wS
  apply prod_le_one
  · intro p hp
    have h3 : (3 : ℝ) ≤ p := by exact_mod_cast three_le_of_mem_Sset hp
    split_ifs
    · apply div_nonneg <;> linarith
    · norm_num
  · intro p hp
    have h3 : (3 : ℝ) ≤ p := by exact_mod_cast three_le_of_mem_Sset hp
    split_ifs
    · rw [div_le_one (by linarith)]; linarith
    · norm_num

/-- `w_S(m) K(m) ≤ (E/(E-1))^4` when `m < (E+1)^5`. -/
lemma wK_le (E m : ℕ) (hE : 3 ≤ E) (hm0 : 0 < m) (hm : m < (E + 1) ^ 5) :
    wS (Sset E) m * Kp m ≤ ((E : ℝ) / ((E : ℝ) - 1)) ^ 4 := by
  have hER : (3 : ℝ) ≤ E := by exact_mod_cast hE
  set g : ℕ → ℝ := fun p => if 2 < p then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1 with hg
  have hK : Kp m = (∏ p ∈ m.primeFactors.filter (fun p => p ≤ E), g p) *
      ∏ p ∈ m.primeFactors.filter (fun p => ¬ p ≤ E), g p := by
    rw [prod_filter_mul_prod_filter_not]; rfl
  set X := (Sset E).filter (fun p => p ∣ m) with hX
  have hA : ∏ p ∈ m.primeFactors.filter (fun p => p ≤ E), g p =
      ∏ p ∈ X, ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
    rw [hg]; simp only
    rw [← prod_filter]
    apply prod_congr _ (fun _ _ => rfl)
    ext p
    simp only [hX, Sset, mem_filter, Nat.mem_primeFactors, mem_range]
    constructor
    · rintro ⟨⟨⟨hp, hpm, -⟩, hpE⟩, h2⟩
      exact ⟨⟨by omega, hp, by omega⟩, hpm⟩
    · rintro ⟨⟨hpE, hp, h2⟩, hpm⟩
      have := hp.two_le
      exact ⟨⟨⟨hp, hpm, by omega⟩, by omega⟩, by omega⟩
  have hw : wS (Sset E) m = ∏ p ∈ X, ((p : ℝ) - 2) / ((p : ℝ) - 1) := by
    unfold wS; rw [hX, prod_filter]
  have hone : wS (Sset E) m * ∏ p ∈ m.primeFactors.filter (fun p => p ≤ E), g p = 1 := by
    rw [hA, hw, ← prod_mul_distrib]
    apply prod_eq_one
    intro p hp
    have h3 : (3 : ℝ) ≤ p := by exact_mod_cast three_le_of_mem_Sset (mem_filter.1 hp).1
    have h1 : (p : ℝ) - 2 ≠ 0 := by linarith
    have h2 : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
  set B := m.primeFactors.filter (fun p => ¬ p ≤ E) with hB
  have hBcard : B.card ≤ 4 := by
    by_contra hc
    push Not at hc
    have h1 : (E + 1) ^ B.card ≤ ∏ p ∈ B, p := by
      apply Finset.pow_card_le_prod
      intro p hp; simp only [hB, mem_filter] at hp; omega
    have h2 : ∏ p ∈ B, p ∣ m := by
      apply dvd_trans _ (Nat.prod_primeFactors_dvd m)
      exact prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)
    have h3 : ∏ p ∈ B, p ≤ m := Nat.le_of_dvd hm0 h2
    have h4 : (E + 1) ^ 5 ≤ (E + 1) ^ B.card := Nat.pow_le_pow_right (by omega) hc
    omega
  have hq1 : (1 : ℝ) ≤ (E : ℝ) / ((E : ℝ) - 1) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hBprod : ∏ p ∈ B, g p ≤ ((E : ℝ) / ((E : ℝ) - 1)) ^ 4 := by
    calc ∏ p ∈ B, g p ≤ ∏ _p ∈ B, ((E : ℝ) / ((E : ℝ) - 1)) := by
          apply prod_le_prod
          · intro p hp
            simp only [hg]
            split_ifs with h
            · have : (2 : ℝ) < p := by exact_mod_cast h
              apply div_nonneg <;> linarith
            · norm_num
          · intro p hp
            simp only [hB, mem_filter] at hp
            have hpE : (E : ℝ) + 1 ≤ p := by exact_mod_cast (show E + 1 ≤ p by omega)
            simp only [hg]
            rw [if_pos (by omega)]
            rw [div_le_div_iff₀ (by linarith) (by linarith)]
            nlinarith
      _ = ((E : ℝ) / ((E : ℝ) - 1)) ^ B.card := prod_const _
      _ ≤ _ := pow_le_pow_right₀ hq1 hBcard
  rw [hK, ← mul_assoc, hone, one_mul]
  exact hBprod

/-- the bound for a single sum `m`. -/
noncomputable def Bmax (E h : ℕ) : ℝ :=
  16 * TaoFivePrimes.twinPrimeConstant * ((E : ℝ) / ((E : ℝ) - 1)) ^ 4 * phi h +
    √(2 * (h : ℝ)) + 51204

lemma T_odd {h k t : ℕ} (hh : 3 ≤ h) (hk : 1 ≤ k) (ht : t ∈ T h k) : t.Prime ∧ t ≠ 2 ∧ h < t := by
  rw [mem_T] at ht
  have : h ≤ k * h := Nat.le_mul_of_pos_left h hk
  exact ⟨ht.2.2, by omega, by omega⟩

lemma one_term_le (K h E m : ℕ) (hh : 25600 ≤ h) (hE : 3 ≤ E) (hm : m < (E + 1) ^ 5) :
    wS (Sset E) m * ((∑ k ∈ Icc 1 K, Npair h k m : ℕ) : ℝ) ≤
      if 0 < Schnir.r m then Bmax E h else 0 := by
  by_cases hz : ∑ k ∈ Icc 1 K, Npair h k m = 0
  · rw [hz]; simp only [Nat.cast_zero, mul_zero]
    split_ifs
    · unfold Bmax
      have := phi_nonneg (h : ℝ) (by positivity)
      have := C_nonneg
      have : 0 ≤ ((E : ℝ) / ((E : ℝ) - 1)) ^ 4 := by
        have : (3 : ℝ) ≤ E := by exact_mod_cast hE
        apply pow_nonneg; apply div_nonneg <;> linarith
      have := Real.sqrt_nonneg (2 * (h : ℝ))
      have : 0 ≤ 16 * TaoFivePrimes.twinPrimeConstant * ((E : ℝ) / ((E : ℝ) - 1)) ^ 4 * phi h := by
        positivity
      linarith
    · exact le_rfl
  · obtain ⟨k, hk, hk0⟩ := exists_ne_zero_of_sum_ne_zero hz
    unfold Npair at hk0
    obtain ⟨x, hx⟩ := card_ne_zero.1 hk0
    simp only [mem_filter, mem_product] at hx
    obtain ⟨⟨h1, h2⟩, hs⟩ := hx
    have hk1 : 1 ≤ k := (mem_Icc.1 hk).1
    obtain ⟨p1, q1, r1⟩ := T_odd (by omega) hk1 h1
    obtain ⟨p2, q2, r2⟩ := T_odd (by omega) hk1 h2
    have hr : 0 < Schnir.r m := by
      unfold Schnir.r
      apply card_pos.2
      refine ⟨x.1, ?_⟩
      simp only [mem_filter, mem_range]
      have : m - x.1 = x.2 := by omega
      rw [this]
      exact ⟨by omega, p1, q1, p2, q2⟩
    rw [if_pos hr]
    have hev : Even m := by
      rw [← hs]
      exact (p1.odd_of_ne_two q1).add_odd (p2.odd_of_ne_two q2)
    have hm0 : 0 < m := by omega
    have hL9 := pair_sum_le K h m hh hev hm0
    have hwK := wK_le E m hE hm0 hm
    have hw0 := wS_nonneg E m
    have hw1 := wS_le_one E m
    have hC := C_nonneg
    have hph := phi_nonneg (h : ℝ) (by positivity)
    unfold Bmax
    calc wS (Sset E) m * ((∑ k ∈ Icc 1 K, Npair h k m : ℕ) : ℝ)
        ≤ wS (Sset E) m * (16 * TaoFivePrimes.twinPrimeConstant * Kp m * phi h +
            √(2 * (h : ℝ)) + 51204) := mul_le_mul_of_nonneg_left hL9 hw0
      _ = 16 * TaoFivePrimes.twinPrimeConstant * phi h * (wS (Sset E) m * Kp m) +
            wS (Sset E) m * (√(2 * (h : ℝ)) + 51204) := by ring
      _ ≤ 16 * TaoFivePrimes.twinPrimeConstant * phi h * ((E : ℝ) / ((E : ℝ) - 1)) ^ 4 +
            1 * (√(2 * (h : ℝ)) + 51204) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hwK (by positivity)
          · exact mul_le_mul_of_nonneg_right hw1 (by positivity)
      _ = _ := by ring

/-- **upper bound**: the weighted pair sum is at most `#{s ≤ n : r(s) > 0} · Bmax`. -/
theorem psi_upper (n K h E : ℕ) (hh : 25600 ≤ h) (hn : 2 * ((K + 2) * h) ≤ n) (hE : 3 ≤ E)
    (hEn : n < (E + 1) ^ 5) :
    ∑ k ∈ Icc 1 K, ∑ t ∈ T h k, ∑ t' ∈ T h k, wS (Sset E) (t + t') ≤
      (((range (n + 1)).filter (fun s => 0 < Schnir.r s)).card : ℝ) * Bmax E h := by
  have hfib : ∀ k ∈ Icc 1 K, ∑ t ∈ T h k, ∑ t' ∈ T h k, wS (Sset E) (t + t') =
      ∑ m ∈ range (n + 1), wS (Sset E) m * (Npair h k m : ℝ) := by
    intro k hk
    have hk' : k ≤ K := (mem_Icc.1 hk).2
    rw [← sum_product']
    rw [← sum_fiberwise_of_maps_to (g := fun x : ℕ × ℕ => x.1 + x.2) (t := range (n + 1))]
    · apply sum_congr rfl
      intro m _
      rw [sum_congr rfl (fun x hx => by rw [(mem_filter.1 hx).2]), sum_const, nsmul_eq_mul,
        mul_comm]
      rfl
    · intro x hx
      rw [mem_product, mem_T, mem_T] at hx
      rw [mem_range]
      have : k * h + 2 * h ≤ (K + 2) * h := by nlinarith
      omega
  rw [sum_congr rfl hfib, sum_comm]
  calc ∑ m ∈ range (n + 1), ∑ k ∈ Icc 1 K, wS (Sset E) m * (Npair h k m : ℝ)
      = ∑ m ∈ range (n + 1), wS (Sset E) m * ((∑ k ∈ Icc 1 K, Npair h k m : ℕ) : ℝ) := by
        apply sum_congr rfl; intro m _; rw [← mul_sum]; push_cast; rfl
    _ ≤ ∑ m ∈ range (n + 1), (if 0 < Schnir.r m then Bmax E h else 0) := by
        apply sum_le_sum; intro m hm
        exact one_term_le K h E m hh hE (by rw [mem_range] at hm; omega)
    _ = _ := by rw [← sum_filter, sum_const, nsmul_eq_mul]

end RV27E

/-! ## part: Lower2 -/

open Finset Real

namespace RV27E

lemma card_T (h k : ℕ) : (T h k).card + Nat.primeCounting (k * h) = Nat.primeCounting (k * h + 2 * h) := by
  rw [← Nat.primesLE_card_eq_primeCounting, ← Nat.primesLE_card_eq_primeCounting,
    Nat.primesLE_eq_filter_range, Nat.primesLE_eq_filter_range]
  rw [← card_filter_add_card_filter_not (s := filter Nat.Prime (range (k * h + 2 * h + 1))) (fun p => k * h < p)]
  congr 2
  · ext p; simp only [T, mem_filter, mem_range, mem_Ioc]
    constructor
    · rintro ⟨⟨a, b⟩, c⟩; exact ⟨⟨by omega, c⟩, a⟩
    · rintro ⟨⟨a, c⟩, b⟩; exact ⟨⟨b, by omega⟩, c⟩
  · ext p; simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨a, c⟩; exact ⟨⟨by omega, c⟩, by omega⟩
    · rintro ⟨⟨a, c⟩, b⟩; exact ⟨by omega, c⟩

lemma sum_card_T (h K : ℕ) :
    ∑ k ∈ Icc 1 K, ((T h k).card : ℝ) =
      (Nat.primeCounting ((K + 2) * h) : ℝ) + Nat.primeCounting ((K + 1) * h) -
        Nat.primeCounting (2 * h) - Nat.primeCounting h := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_Icc_succ_top (by omega), ih]
    have e := card_T h (K + 1)
    have e2 : (K + 1) * h + 2 * h = (K + 1 + 2) * h := by ring
    rw [e2] at e
    have e' : ((T h (K + 1)).card : ℝ) + Nat.primeCounting ((K + 1) * h) =
        Nat.primeCounting ((K + 1 + 2) * h) := by exact_mod_cast e
    have e3 : (K + 1 + 1) * h = (K + 2) * h := by ring
    rw [e3]
    linarith

/-- `𝒫_S = ∏_{p ∈ S} (1 - 1/(p-1)²)`. -/
noncomputable def PP (E : ℕ) : ℝ := ∏ p ∈ Sset E, (1 - 1 / ((p : ℝ) - 1) ^ 2)

lemma PP_ge (E : ℕ) : TaoFivePrimes.twinPrimeConstant / 2 ≤ PP E := by
  have hpart : PP E = TaoFivePrimes.twinPrimePartial E := by
    unfold PP TaoFivePrimes.twinPrimePartial
    rw [← prod_filter]
    apply prod_congr _ (fun _ _ => rfl)
    unfold Sset
    apply filter_congr
    intro p _
    constructor
    · rintro ⟨hp, h2⟩; exact ⟨hp, by have := hp.two_le; omega⟩
    · rintro ⟨hp, h2⟩; exact ⟨hp, by omega⟩
  have hbdd : BddBelow (Set.range TaoFivePrimes.twinPrimePartial) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨Q, rfl⟩
    unfold TaoFivePrimes.twinPrimePartial
    apply prod_nonneg
    intro p _
    split_ifs with hp
    · have : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by omega)
      have h4 : (4 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
      have : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
        rw [div_le_one (by linarith)]; linarith
      linarith
    · norm_num
  rw [hpart, TaoFivePrimes.twinPrimeConstant]
  have := csInf_le hbdd ⟨E, rfl⟩
  linarith

/-- `B_S = ∏_{p ∈ S} (1 + (p-1)/(p(p-2)))`. -/
noncomputable def BS (E : ℕ) : ℝ := ∏ p ∈ Sset E, (1 + ((p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 2)))

lemma telescope (E : ℕ) (hE : 2 ≤ E) :
    ∏ j ∈ Icc 3 E, (((j : ℝ) - 1) / ((j : ℝ) - 2)) = (E : ℝ) - 1 := by
  induction E with
  | zero => omega
  | succ E ih =>
    rcases Nat.lt_or_ge E 2 with hE2 | hE2
    · have : E = 1 := by omega
      subst this; norm_num
    · rw [prod_Icc_succ_top (by omega), ih hE2]
      have : (2 : ℝ) ≤ E := by exact_mod_cast hE2
      have hne : (E : ℝ) - 1 ≠ 0 := by linarith
      rw [show ((E + 1 : ℕ) : ℝ) - 1 = E by push_cast; ring,
        show ((E + 1 : ℕ) : ℝ) - 2 = E - 1 by push_cast; ring]
      field_simp

lemma BS_le (E : ℕ) (hE : 2 ≤ E) : BS E ≤ E := by
  have hER : (2 : ℝ) ≤ E := by exact_mod_cast hE
  calc BS E ≤ ∏ p ∈ Sset E, (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
        apply prod_le_prod
        · intro p hp
          have : (3 : ℝ) ≤ p := by exact_mod_cast three_le_of_mem_Sset hp
          have : 0 ≤ ((p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 2)) := by
            apply div_nonneg (by linarith); apply mul_nonneg <;> linarith
          linarith
        · intro p hp
          have h3 : (3 : ℝ) ≤ p := by exact_mod_cast three_le_of_mem_Sset hp
          have h1 : ((p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 2)) ≤ 1 / ((p : ℝ) - 2) := by
            rw [div_le_div_iff₀ (by nlinarith) (by linarith)]; nlinarith
          have h2 : ((p : ℝ) - 1) / ((p : ℝ) - 2) = 1 + 1 / ((p : ℝ) - 2) := by
            have : (p : ℝ) - 2 ≠ 0 := by linarith
            field_simp; ring
          linarith
    _ ≤ ∏ j ∈ Icc 3 E, (((j : ℝ) - 1) / ((j : ℝ) - 2)) := by
        apply prod_le_prod_of_subset_of_one_le
        · intro p hp
          have := three_le_of_mem_Sset hp
          simp only [Sset, mem_filter, mem_range] at hp
          simp only [mem_Icc]; omega
        · intro p hp
          have : (3 : ℝ) ≤ p := by exact_mod_cast three_le_of_mem_Sset hp
          apply div_nonneg <;> linarith
        · intro j hj _
          have : (3 : ℝ) ≤ j := by exact_mod_cast (mem_Icc.1 hj).1
          rw [le_div_iff₀ (by linarith)]; linarith
    _ = (E : ℝ) - 1 := telescope E hE
    _ ≤ E := by linarith

/-- **lower bound** for the weighted pair sum, summed over the `K` intervals. -/
theorem psi_lower_sum (K h E Q w : ℕ) (hK : 1 ≤ K) (hQ : 20 < Q) (hN : 16 * Q ^ 2 ≤ 2 * h)
    (hw : 1 ≤ w) (hwQ : 12 * w ≤ Q) (hQh : Q < h) (hEh : E < h) :
    PP E * ((16 / 15) * (∑ k ∈ Icc 1 K, ((T h k).card : ℝ)) ^ 2 / K -
      (2 * (h : ℝ) / (15 * (Real.log Q - Real.log 20)) + (2 * (h : ℝ) / w + 2) * BS E) *
        ∑ k ∈ Icc 1 K, ((T h k).card : ℝ)) ≤
      ∑ k ∈ Icc 1 K, ∑ t ∈ T h k, ∑ t' ∈ T h k, wS (Sset E) (t + t') := by
  set D := 2 * (h : ℝ) / (15 * (Real.log Q - Real.log 20)) + (2 * (h : ℝ) / w + 2) * BS E with hD
  have hone : ∀ k ∈ Icc 1 K, PP E * ((16 / 15) * ((T h k).card : ℝ) ^ 2 - D * (T h k).card) ≤
      ∑ t ∈ T h k, ∑ t' ∈ T h k, wS (Sset E) (t + t') := by
    intro k hk
    have hk1 : 1 ≤ k := (mem_Icc.1 hk).1
    have hkh : h ≤ k * h := Nat.le_mul_of_pos_left h hk1
    have := RV27.interval_pair_weight_lower (Sset E)
      (fun p hp => by simp only [Sset, mem_filter] at hp; exact hp.2)
      ⟨Q, by omega⟩ (k * h + 1) (2 * h) w (by simpa using hN) hw (by simpa using hwQ)
      (by simpa using hQ) (T h k)
      (by intro t ht; rw [mem_T] at ht; rw [mem_Ico]; omega)
      (by intro t ht; rw [mem_T] at ht; simp only [PNat.mk_coe]; exact ⟨ht.2.2, by omega⟩)
      (by
        intro t ht p hp hpt
        rw [mem_T] at ht
        have hpS := hp
        simp only [Sset, mem_filter, mem_range] at hp
        rcases (Nat.prime_dvd_prime_iff_eq hp.2.1 ht.2.2).1 hpt with rfl
        omega)
    simp only [PNat.mk_coe] at this
    unfold PP wS
    convert this using 2
    rw [hD]; unfold BS; push_cast; ring
  calc PP E * ((16 / 15) * (∑ k ∈ Icc 1 K, ((T h k).card : ℝ)) ^ 2 / K -
        D * ∑ k ∈ Icc 1 K, ((T h k).card : ℝ))
      ≤ PP E * ((16 / 15) * ∑ k ∈ Icc 1 K, ((T h k).card : ℝ) ^ 2 -
          D * ∑ k ∈ Icc 1 K, ((T h k).card : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by have := PP_ge E; have := C_nonneg; linarith)
        have hcs := sq_sum_le_card_mul_sum_sq (s := Icc 1 K) (f := fun k => ((T h k).card : ℝ))
        simp only [Nat.card_Icc, add_tsub_cancel_right] at hcs
        have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
        have : (∑ k ∈ Icc 1 K, ((T h k).card : ℝ)) ^ 2 / K ≤ ∑ k ∈ Icc 1 K, ((T h k).card : ℝ) ^ 2 := by
          rw [div_le_iff₀ hKpos]; linarith
        have e : (16 / 15) * (∑ k ∈ Icc 1 K, ((T h k).card : ℝ)) ^ 2 / K =
            (16 / 15) * ((∑ k ∈ Icc 1 K, ((T h k).card : ℝ)) ^ 2 / K) := by ring
        rw [e]; linarith
    _ = ∑ k ∈ Icc 1 K, PP E * ((16 / 15) * ((T h k).card : ℝ) ^ 2 - D * (T h k).card) := by
        rw [← mul_sum, sum_sub_distrib, ← mul_sum, ← mul_sum]
    _ ≤ _ := sum_le_sum hone

end RV27E

/-! ## part: Pi -/

open Real

namespace RV27E

lemma pi_lower (x : ℕ) (hx : 30 ≤ x) :
    0.9212 * (x : ℝ) / log x - 5 ≤ (Nat.primeCounting x : ℝ) := by
  have hxR : (30 : ℝ) ≤ x := by exact_mod_cast hx
  have h1 := Chebyshev.psi_le_primeCounting_mul_log x
  have h2 := Chebyshev.psi_lower (x : ℝ) hxR
  have ha := Chebyshev.a_bound.1
  have hl : 0 < log (x : ℝ) := log_pos (by linarith)
  have hax : 0.9212 * (x : ℝ) ≤ Chebyshev.a * x := mul_le_mul_of_nonneg_right ha (by linarith)
  have : 0.9212 * (x : ℝ) - 5 * log x ≤ (Nat.primeCounting x : ℝ) * log x := by linarith
  rw [sub_le_iff_le_add, div_le_iff₀ hl]
  linarith

lemma pi_upper (x : ℕ) (hx : 2 ≤ x) :
    (Nat.primeCounting x : ℝ) ≤ 2 * log 4 * x / log x + √(x : ℝ) := by
  have hxR : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have h := Chebyshev.pi_le_log4_mul_div (x := (x : ℝ)) (by linarith)
  rw [Nat.floor_natCast, Real.log_sqrt (by linarith)] at h
  have e : log 4 * (x : ℝ) / (log x / 2) = 2 * log 4 * x / log x := by
    have : log (x : ℝ) ≠ 0 := (log_pos (by linarith)).ne'
    field_simp
  linarith

lemma log4_le : log 4 ≤ 1.3863 := by
  have : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; norm_num
  have := log_two_lt_d9
  linarith

lemma log1002_le : log 1002 ≤ 7 := by
  rw [log_le_iff_le_exp (by norm_num)]
  have h1 := exp_one_gt_d9
  have h : exp 7 = exp 1 ^ 7 := by rw [← exp_nat_mul]; norm_num
  rw [h]
  have : (2.7182818283 : ℝ) ^ 7 ≤ exp 1 ^ 7 := pow_le_pow_left₀ (by norm_num) h1.le 7
  nlinarith

/-- lower bound for `Σ_k S_k = π(1002h) + π(1001h) - π(2h) - π(h)`. -/
lemma sigma_lower (h : ℕ) (hl : 292 ≤ log (h : ℝ))
    (hsmall : 10 + 3 * √(h : ℝ) ≤ 0.08 * h / log h) :
    (h : ℝ) * (1845 / (log h + 7) - 8.4 / log h) ≤
      (Nat.primeCounting ((1000 + 2) * h) : ℝ) + Nat.primeCounting ((1000 + 1) * h) -
        Nat.primeCounting (2 * h) - Nat.primeCounting h := by
  set l := log (h : ℝ) with hlD
  have hl0 : 0 < l := by linarith
  have hh1 : (1 : ℝ) < h := by
    by_contra hc; push Not at hc
    have : log (h : ℝ) ≤ 0 := by
      exact log_nonpos (Nat.cast_nonneg h) hc
    linarith
  have hhpos : (0 : ℝ) < h := by linarith
  have h30 : (30 : ℝ) ≤ h := by
    by_contra hc; push Not at hc
    have := log_le_log hhpos hc.le
    have : log (30 : ℝ) ≤ 30 - 1 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 30); linarith
    linarith
  have hhN : 30 ≤ h := by exact_mod_cast h30
  -- the two large terms
  have hbig : ∀ c : ℕ, 1 ≤ c → c ≤ 1002 →
      0.9212 * ((c : ℝ) * h) / (l + 7) - 5 ≤ (Nat.primeCounting (c * h) : ℝ) := by
    intro c hc1 hc2
    have hcR : (1 : ℝ) ≤ c := by exact_mod_cast hc1
    have hc2R : (c : ℝ) ≤ 1002 := by exact_mod_cast hc2
    have := pi_lower (c * h) (by nlinarith)
    push_cast at this
    have hlc : log ((c : ℝ) * h) ≤ l + 7 := by
      rw [log_mul (by linarith) (by linarith)]
      have := log_le_log (by linarith) hc2R
      linarith [log1002_le]
    have hlc0 : 0 < log ((c : ℝ) * h) := log_pos (by nlinarith)
    have : 0.9212 * ((c : ℝ) * h) / (l + 7) ≤ 0.9212 * ((c : ℝ) * h) / log ((c : ℝ) * h) :=
      div_le_div_of_nonneg_left (by positivity) hlc0 hlc
    linarith
  have h1002 := hbig 1002 (by norm_num) le_rfl
  have h1001 := hbig 1001 (by norm_num) (by norm_num)
  have hu2 := pi_upper (2 * h) (by omega)
  have hu1 := pi_upper h (by omega)
  rw [← hlD] at hu1
  push_cast at h1002 h1001 hu2
  have hl2 : l ≤ log (2 * (h : ℝ)) := log_le_log hhpos (by linarith)
  have h4 := log4_le
  have hlog4 : 0 ≤ log (4 : ℝ) := log_nonneg (by norm_num)
  have hu2' : 2 * log 4 * (2 * (h : ℝ)) / log (2 * h) ≤ 2 * 1.3863 * (2 * (h : ℝ)) / l := by
    calc 2 * log 4 * (2 * (h : ℝ)) / log (2 * h) ≤ 2 * log 4 * (2 * (h : ℝ)) / l :=
          div_le_div_of_nonneg_left (by positivity) hl0 hl2
      _ ≤ _ := by gcongr
  have hu1' : 2 * log 4 * (h : ℝ) / l ≤ 2 * 1.3863 * (h : ℝ) / l := by gcongr
  have hs2 : √(2 * (h : ℝ)) ≤ 2 * √(h : ℝ) := by
    rw [sqrt_le_left (by positivity)]
    have := sq_sqrt hhpos.le
    nlinarith [sqrt_nonneg (h : ℝ)]
  have e1 : 0.9212 * ((1002 : ℝ) * h) / (l + 7) + 0.9212 * ((1001 : ℝ) * h) / (l + 7) =
      1845 * h / (l + 7) + 0.1636 * h / (l + 7) := by ring
  have e2 : 2 * 1.3863 * (2 * (h : ℝ)) / l + 2 * 1.3863 * (h : ℝ) / l = 8.4 * h / l - 0.0822 * h / l := by
    ring
  have e3 : (h : ℝ) * (1845 / (l + 7) - 8.4 / l) = 1845 * h / (l + 7) - 8.4 * h / l := by ring
  have hpos : 0 ≤ 0.1636 * (h : ℝ) / (l + 7) := by positivity
  have h008 : 0.08 * (h : ℝ) / l ≤ 0.0822 * h / l := by gcongr; norm_num
  rw [e3]
  linarith

end RV27E

/-! ## part: Num -/

open Real

namespace RV27E

/-- `A(l)`: lower density of `Σ_k S_k` in units of `h`. -/
noncomputable def Af (l : ℝ) : ℝ := 1845 / (l + 7) - 8.4 / l
/-- `D(l)`: the error coefficient in units of `h`. -/
noncomputable def Df (l : ℝ) : ℝ := 4 / (15 * (l - 10)) + 1 / 1000 / l ^ 2

lemma poly_ineq (l : ℝ) (hl : 292 ≤ l) :
    2005 * 16.01 / l ^ 2 ≤ 11.995 * ((16 / 15) * Af l ^ 2 / 1000 - Af l * Df l) := by
  unfold Af Df
  have hl0 : 0 < l := by linarith
  have hl10 : 0 < l - 10 := by linarith
  have hl7 : 0 < l + 7 := by linarith
  set t := l - 292 with ht
  have ht0 : 0 ≤ t := by linarith
  have hlt : l = t + 292 := by rw [ht]; ring
  have key : 11.995 * ((16 / 15) * (1845 / (l + 7) - 8.4 / l) ^ 2 / 1000 -
      (1845 / (l + 7) - 8.4 / l) * (4 / (15 * (l - 10)) + 1 / 1000 / l ^ 2)) - 2005 * 16.01 / l ^ 2 =
      (129574082592 * t ^ 4 + 136250100037799 * t ^ 3 + 53140814329533049 * t ^ 2 + 9087012579880720912 * t + 572642948631326068148) /
        (25000000 * l ^ 3 * (l - 10) * (l + 7) ^ 2) := by
    rw [hlt]
    have h1 : t + 292 ≠ 0 := by linarith
    have h2 : t + 292 - 10 ≠ 0 := by linarith
    have h3 : t + 292 + 7 ≠ 0 := by linarith
    field_simp
    ring
  have hpos : 0 ≤ (129574082592 * t ^ 4 + 136250100037799 * t ^ 3 + 53140814329533049 * t ^ 2 + 9087012579880720912 * t + 572642948631326068148) /
        (25000000 * l ^ 3 * (l - 10) * (l + 7) ^ 2) := by positivity
  linarith

lemma Af_nonneg (l : ℝ) (hl : 292 ≤ l) : 0 ≤ Af l := by
  unfold Af
  have hl0 : 0 < l := by linarith
  rw [sub_nonneg, div_le_div_iff₀ hl0 (by linarith)]
  nlinarith

lemma Df_le (l : ℝ) (hl : 292 ≤ l) : Df l ≤ (32 / 15) * Af l / 1000 := by
  unfold Df Af
  have hl0 : 0 < l := by linarith
  have h1 : 4 / (15 * (l - 10)) ≤ 4 / (15 * 282) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have h2 : 1 / 1000 / l ^ 2 ≤ 1 / 1000 / 292 ^ 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    exact pow_le_pow_left₀ (by norm_num) hl 2
  -- Af l ≥ 1845/(l+7) - 8.4/l ≥ ... use l ≤ anything? need a lower bound valid for all l ≥ 292
  -- (32/15) Af/1000 ≥ (32/15)(1836.6 l - 58.8)/(1000 l (l+7)), while Df ≤ 4/(15(l-10)) + 1/(1000 l^2)
  have e : (32 / 15) * (1845 / (l + 7) - 8.4 / l) / 1000 - (4 / (15 * (l - 10)) + 1 / 1000 / l ^ 2) =
      ((32 / 15) * (1845 * l - 8.4 * (l + 7)) * (15 * (l - 10)) * l - 4 * 1000 * l ^ 2 * (l + 7) -
        (l + 7) * (15 * (l - 10))) / (1000 * l ^ 2 * (l + 7) * (15 * (l - 10))) := by
    have : l + 7 ≠ 0 := by linarith
    have : l - 10 ≠ 0 := by linarith
    field_simp
    ring
  have hnum : 0 ≤ (32 / 15) * (1845 * l - 8.4 * (l + 7)) * (15 * (l - 10)) * l - 4 * 1000 * l ^ 2 * (l + 7) -
        (l + 7) * (15 * (l - 10)) := by nlinarith
  have : 0 ≤ (32 / 15) * (1845 / (l + 7) - 8.4 / l) / 1000 - (4 / (15 * (l - 10)) + 1 / 1000 / l ^ 2) := by
    rw [e]; apply div_nonneg hnum
    have : 0 < l - 10 := by linarith
    positivity
  linarith

/-- the final comparison, with every analytic input abstracted. -/
theorem final_abstract (h l C Sig D cnt Bm PPv n Psi : ℝ)
    (hl : 292 ≤ l) (hh : 0 < h) (hn : n ≤ 2005 * h)
    (hC : 1.25 ≤ C) (hPP : C / 2 ≤ PPv)
    (hSig : h * Af l ≤ Sig) (hD : D ≤ h * Df l)
    (hlow : PPv * ((16 / 15) * Sig ^ 2 / 1000 - D * Sig) ≤ Psi) (hup : Psi ≤ cnt * Bm)
    (hBm : Bm ≤ 16.01 * C * h / l ^ 2) (hcnt : 0 ≤ cnt) :
    n * (100 / 2399) ≤ cnt := by
  have hA := Af_nonneg l hl
  have hDf := Df_le l hl
  have hg := poly_ineq l hl
  set A := Af l
  set Dd := Df l
  set g := (16 / 15) * A ^ 2 / 1000 - A * Dd with hgdef
  have hl0 : 0 < l := by linarith
  have hgpos : 0 ≤ g := by
    have : 0 ≤ 2005 * 16.01 / l ^ 2 := by positivity
    linarith
  have hhA : 0 ≤ h * A := mul_nonneg hh.le hA
  -- f(Σ) ≥ f(hA) ≥ h² g
  have hf1 : (16 / 15) * (h * A) ^ 2 / 1000 - D * (h * A) ≤ (16 / 15) * Sig ^ 2 / 1000 - D * Sig := by
    have hdiff : (16 / 15) * Sig ^ 2 / 1000 - D * Sig - ((16 / 15) * (h * A) ^ 2 / 1000 - D * (h * A)) =
        (Sig - h * A) * ((16 / 15) * (Sig + h * A) / 1000 - D) := by ring
    have h1 : 0 ≤ Sig - h * A := by linarith
    have h2 : 0 ≤ (16 / 15) * (Sig + h * A) / 1000 - D := by
      have : h * Dd ≤ h * ((32 / 15) * A / 1000) := mul_le_mul_of_nonneg_left hDf hh.le
      have : (16 / 15) * (Sig + h * A) / 1000 ≥ (32 / 15) * (h * A) / 1000 := by
        have : (16 / 15) * (Sig + h * A) / 1000 - (32 / 15) * (h * A) / 1000 = (16 / 15) * (Sig - h * A) / 1000 := by ring
        have : 0 ≤ (16 / 15) * (Sig - h * A) / 1000 := by positivity
        linarith
      have e : h * ((32 / 15) * A / 1000) = (32 / 15) * (h * A) / 1000 := by ring
      linarith
    have := mul_nonneg h1 h2
    linarith
  have hf2 : h ^ 2 * g ≤ (16 / 15) * (h * A) ^ 2 / 1000 - D * (h * A) := by
    have : D * (h * A) ≤ h * Dd * (h * A) := mul_le_mul_of_nonneg_right hD hhA
    have e : h ^ 2 * g = (16 / 15) * (h * A) ^ 2 / 1000 - h * Dd * (h * A) := by rw [hgdef]; ring
    linarith
  have hPP0 : 0 < PPv := by linarith
  have hPsi : C / 2 * (h ^ 2 * g) ≤ Psi := by
    have h1 : 0 ≤ h ^ 2 * g := by positivity
    calc C / 2 * (h ^ 2 * g) ≤ PPv * (h ^ 2 * g) := mul_le_mul_of_nonneg_right hPP h1
      _ ≤ PPv * ((16 / 15) * Sig ^ 2 / 1000 - D * Sig) :=
          mul_le_mul_of_nonneg_left (hf2.trans hf1) hPP0.le
      _ ≤ Psi := hlow
  have hcB : cnt * Bm ≤ cnt * (16.01 * C * h / l ^ 2) := mul_le_mul_of_nonneg_left hBm hcnt
  -- C/2 h² g ≤ cnt * 16.01 C h / l²  ⇒  cnt ≥ h g l² / 32.02
  have hmain : C / 2 * (h ^ 2 * g) ≤ cnt * (16.01 * C * h / l ^ 2) := by linarith
  have hgl : 2005 * 16.01 ≤ 11.995 * g * l ^ 2 := by
    have := mul_le_mul_of_nonneg_right hg (sq_nonneg l)
    rw [div_mul_cancel₀ _ (by positivity)] at this
    linarith
  have hCpos : 0 < C := by linarith
  have h3 : h * (g * l ^ 2) ≤ cnt * 32.02 := by
    have e1 : cnt * (16.01 * C * h / l ^ 2) = (C * h / l ^ 2) * (cnt * 16.01) := by ring
    have e2 : C / 2 * (h ^ 2 * g) = (C * h / l ^ 2) * (h * g * l ^ 2 / 2) := by
      field_simp
    rw [e1, e2] at hmain
    have hpos : 0 < C * h / l ^ 2 := by positivity
    have := le_of_mul_le_mul_left hmain hpos
    linarith
  have : 2005 * h * (100 / 2399) ≤ cnt := by
    have : h * (2005 * 16.01) ≤ h * (11.995 * g * l ^ 2) := mul_le_mul_of_nonneg_left hgl hh.le
    nlinarith
  linarith

end RV27E

/-! ## part: Final -/

open Finset Real

namespace RV27E

lemma exp8_ge : (2980 : ℝ) ≤ exp 8 := by
  have h1 := exp_one_gt_d9
  have h : exp 8 = exp 1 ^ 8 := by rw [← exp_nat_mul]; norm_num
  rw [h]
  have : (2.7182818283 : ℝ) ^ 8 ≤ exp 1 ^ 8 := pow_le_pow_left₀ (by norm_num) h1.le 8
  nlinarith

lemma exp5_ge : (148 : ℝ) ≤ exp 5 := by
  have h1 := exp_one_gt_d9
  have h : exp 5 = exp 1 ^ 5 := by rw [← exp_nat_mul]; norm_num
  rw [h]
  have : (2.7182818283 : ℝ) ^ 5 ≤ exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) h1.le 5
  nlinarith

/-- `exp(l/4) ≥ 10⁶ l²` for `l ≥ 292`. -/
lemma q_large (l : ℝ) (hl : 292 ≤ l) : 1000000 * l ^ 2 ≤ exp (l / 4) := by
  have h := Real.pow_div_factorial_le_exp (x := l / 4) (by linarith) 10
  have hf : ((10 : ℕ).factorial : ℝ) = 3628800 := by norm_num [Nat.factorial]
  rw [hf] at h
  have h8 : (292 : ℝ) ^ 8 ≤ l ^ 8 := pow_le_pow_left₀ (by norm_num) hl 8
  have e : (l / 4) ^ 10 / 3628800 = l ^ 2 * (l ^ 8 / (4 ^ 10 * 3628800)) := by ring
  have : 1000000 ≤ l ^ 8 / (4 ^ 10 * 3628800) := by
    rw [le_div_iff₀ (by norm_num)]; nlinarith
  have := mul_le_mul_of_nonneg_left this (sq_nonneg l)
  linarith


lemma s_up (s q : ℝ) (hs0 : 0 ≤ s) (h : s ^ 2 ≤ 2 * q ^ 4) : s ≤ 1.4143 * q ^ 2 := by
  by_contra hc; push Not at hc
  have h1 : (1.4143 * q ^ 2) ^ 2 < s ^ 2 := pow_lt_pow_left₀ hc (by positivity) (by norm_num)
  have : (1.4143 * q ^ 2) ^ 2 = 2.00024449 * q ^ 4 := by ring
  have : 0 ≤ q ^ 4 := by positivity
  linarith

lemma s_lo (s q : ℝ) (hs0 : 0 ≤ s) (h : 2 * q ^ 4 < (s + 1) ^ 2) : 1.4142 * q ^ 2 < s + 1 := by
  by_contra hc; push Not at hc
  have h1 : (s + 1) ^ 2 ≤ (1.4142 * q ^ 2) ^ 2 := pow_le_pow_left₀ (by linarith) hc 2
  have : (1.4142 * q ^ 2) ^ 2 = 1.99996164 * q ^ 4 := by ring
  have : 0 ≤ q ^ 4 := by positivity
  linarith

lemma E_up (E Q q : ℝ) (hE0 : 0 ≤ E) (hq : 0 ≤ q) (h1 : E ^ 2 ≤ Q) (h2 : Q ≤ 0.3536 * q ^ 2) :
    E ≤ 0.6 * q := by
  by_contra hc; push Not at hc
  have : (0.6 * q) ^ 2 < E ^ 2 := pow_lt_pow_left₀ hc (by positivity) (by norm_num)
  nlinarith

lemma E_lo (E Q q : ℝ) (hE0 : 0 ≤ E) (hq : 0 ≤ q) (h1 : Q < (E + 1) ^ 2) (h2 : 0.35 * q ^ 2 ≤ Q) :
    0.59 * q < E + 1 := by
  by_contra hc; push Not at hc
  have : (E + 1) ^ 2 ≤ (0.59 * q) ^ 2 := pow_le_pow_left₀ (by linarith) hc 2
  nlinarith

lemma pow_chain (q : ℝ) (hq : 1 ≤ q) : q ≤ q ^ 2 ∧ q ^ 2 ≤ q ^ 3 ∧ q ^ 3 ≤ q ^ 4 := by
  have h0 : 0 ≤ q := by linarith
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · have : 0 ≤ q ^ 2 := by positivity
    nlinarith
  · have : 0 ≤ q ^ 3 := by positivity
    nlinarith


lemma l_le_sq (l : ℝ) (hl : 1 ≤ l) : l ≤ l ^ 2 := by nlinarith

lemma small_sig (q l : ℝ) (hl : 292 ≤ l) (hq : 1000000 * l ^ 2 ≤ q) :
    10 + 3 * q ^ 2 ≤ 0.08 * q ^ 4 / l := by
  have hl0 : 0 < l := by linarith
  have hll := l_le_sq l (by linarith)
  have hq1 : 1 ≤ q := by nlinarith
  have hqq : q ≤ q ^ 2 := by nlinarith
  have h50 : 50 * l ≤ q ^ 2 := by linarith
  rw [le_div_iff₀ hl0]
  have a1 : q ^ 2 * (50 * l) ≤ q ^ 2 * q ^ 2 := mul_le_mul_of_nonneg_left h50 (by positivity)
  have a2 : (10 + 3 * q ^ 2) * l ≤ 4 * q ^ 2 * l := mul_le_mul_of_nonneg_right (by linarith) hl0.le
  have e : q ^ 2 * q ^ 2 = q ^ 4 := by ring
  linarith

lemma t2_lem (q w : ℝ) (hq : 1000 ≤ q ^ 2) (hw : 0.029 * q ^ 2 ≤ w) : 2 * q ^ 4 / w + 2 ≤ 70 * q ^ 2 := by
  have hq0 : 0 < q ^ 2 := by linarith
  have : 2 * q ^ 4 / w ≤ 2 * q ^ 4 / (0.029 * q ^ 2) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hw
  have e : 2 * q ^ 4 / (0.029 * q ^ 2) = (2 / 0.029) * q ^ 2 := by field_simp
  rw [e] at this
  have : (2 / 0.029 : ℝ) ≤ 69 := by norm_num
  nlinarith

lemma t4_lem (q l : ℝ) (hl : 292 ≤ l) (hq : 1000000 * l ^ 2 ≤ q) :
    70 * q ^ 2 * (0.6 * q) ≤ q ^ 4 * (1 / 1000 / l ^ 2) := by
  have hl0 : 0 < l ^ 2 := by positivity
  have hqpos : 0 < q := by nlinarith
  have e : q ^ 4 * (1 / 1000 / l ^ 2) = q ^ 3 * (q / (1000 * l ^ 2)) := by field_simp
  rw [e]
  have : 42 ≤ q / (1000 * l ^ 2) := by rw [le_div_iff₀ (by positivity)]; nlinarith
  have h3 := pow_pos hqpos 3
  have e2 : 70 * q ^ 2 * (0.6 * q) = 42 * q ^ 3 := by ring
  rw [e2]
  calc 42 * q ^ 3 = q ^ 3 * 42 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left this h3.le

lemma small_B (q l : ℝ) (hl : 292 ≤ l) (hq : 1000000 * l ^ 2 ≤ q) :
    2 * q ^ 2 + 51204 ≤ 0.0105 * (q ^ 4 / l ^ 2) := by
  have hl0 : 0 < l ^ 2 := by positivity
  have hl2 : (85264 : ℝ) ≤ l ^ 2 := by nlinarith
  have hq1 : 1 ≤ q := by nlinarith
  have hqq : q ≤ q ^ 2 := by nlinarith
  have h300 : 300 * l ^ 2 ≤ q ^ 2 := by linarith
  rw [mul_div_assoc', le_div_iff₀ hl0]
  have a1 : q ^ 2 * (300 * l ^ 2) ≤ q ^ 2 * q ^ 2 := mul_le_mul_of_nonneg_left h300 (by positivity)
  have a2 : 51204 * l ^ 2 ≤ q ^ 2 * l ^ 2 := mul_le_mul_of_nonneg_right (by nlinarith) hl0.le
  have e : q ^ 2 * q ^ 2 = q ^ 4 := by ring
  nlinarith

lemma sq2_lem (q : ℝ) : √(2 * q ^ 4) ≤ 2 * q ^ 2 := by
  rw [sqrt_le_left (by positivity)]
  have : 0 ≤ q ^ 4 := by positivity
  nlinarith

lemma rho_lem (E : ℝ) (hE : 50001 ≤ E) : (E / (E - 1)) ^ 4 ≤ 1.0001 := by
  have : E / (E - 1) ≤ 1.00002 := by rw [div_le_iff₀ (by linarith)]; nlinarith
  have h0 : 0 ≤ E / (E - 1) := by apply div_nonneg <;> linarith
  calc (E / (E - 1)) ^ 4 ≤ 1.00002 ^ 4 := pow_le_pow_left₀ h0 this 4
    _ ≤ 1.0001 := by norm_num

lemma Bm_comb (C ρ X sm : ℝ) (hC : 1.25 ≤ C) (hρ : ρ ≤ 1.0001) (hX : 0 ≤ X) (hsm : sm ≤ 0.0105 * X) :
    16 * C * ρ * X + sm ≤ 16.01 * C * X := by
  have : 16 * C * ρ * X ≤ 16 * C * 1.0001 * X := by
    apply mul_le_mul_of_nonneg_right _ hX
    apply mul_le_mul_of_nonneg_left hρ (by linarith)
  nlinarith

lemma logQ_lem (Q q l : ℝ) (hq2e : q ^ 2 = exp (l / 2)) (hQ : 0.35 * q ^ 2 ≤ Q) :
    l / 2 - 5 ≤ Real.log Q - Real.log 20 := by
  have h148 := exp5_ge
  have e : exp (l / 2 - 5) * exp 5 = exp (l / 2) := by rw [← exp_add]; ring_nf
  have h1 : exp (l / 2 - 5) * 148 ≤ q ^ 2 := by
    rw [hq2e, ← e]; exact mul_le_mul_of_nonneg_left h148 (exp_pos _).le
  have h2 : 20 * exp (l / 2 - 5) ≤ Q := by have := exp_pos (l / 2 - 5); nlinarith
  have := log_le_log (by positivity) h2
  rw [log_mul (by norm_num) (exp_pos _).ne', log_exp] at this
  linarith

set_option maxHeartbeats 1000000 in
theorem large_range_aux (n : ℕ) (hn : exp 300 ≤ (n : ℝ)) :
    (n : ℝ) * (100 / 2399) ≤ (((range (n + 1)).filter (fun s => 0 < Schnir.r s)).card : ℝ) := by
  set cnt := (((range (n + 1)).filter (fun s => 0 < Schnir.r s)).card : ℝ) with hcnt
  set h := n / 2004 with hhdef
  have hdiv1 : 2004 * h ≤ n := by rw [hhdef]; exact Nat.mul_div_le n 2004
  have hdiv2 : n < 2004 * (h + 1) := by
    rw [hhdef]; have := Nat.lt_mul_div_succ n (show 0 < 2004 by norm_num); linarith
  have hdiv2R : (n : ℝ) < 2004 * ((h : ℝ) + 1) := by exact_mod_cast hdiv2
  have he292 : (3 : ℝ) ≤ exp 292 := by
    have := add_one_le_exp (292 : ℝ); linarith
  have hhexp : exp 292 ≤ (h : ℝ) := by
    have e : exp 300 = exp 292 * exp 8 := by rw [← exp_add]; norm_num
    have := exp8_ge
    have h3 : exp 292 * 2980 ≤ exp 300 := by rw [e]; exact mul_le_mul_of_nonneg_left this (exp_pos _).le
    linarith
  have hhpos : (0 : ℝ) < h := by linarith
  set l := log (h : ℝ) with hl
  have hl292 : 292 ≤ l := by
    have := log_le_log (exp_pos 292) hhexp
    rwa [log_exp] at this
  have hl0 : 0 < l := by linarith
  set q := exp (l / 4) with hq
  have hq4 : q ^ 4 = (h : ℝ) := by
    rw [hq, ← exp_nat_mul]; push_cast
    rw [show (4 : ℝ) * (l / 4) = l by ring, hl, exp_log hhpos]
  have hqbig : 1000000 * l ^ 2 ≤ q := q_large l hl292
  have hl2 : (85264 : ℝ) ≤ l ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num) hl292 2; norm_num at this; linarith
  have hq0 : (85264000000 : ℝ) ≤ q := by linarith
  have hqpos : (0 : ℝ) < q := by linarith
  have hhq : (h : ℝ) = q ^ 4 := hq4.symm
  obtain ⟨hp2, hp3, hp4⟩ := pow_chain q (by linarith)
  have hnh : (n : ℝ) ≤ 2005 * h := by
    have : (2004 : ℝ) ≤ h := by rw [hhq]; linarith
    linarith
  -- s, Q, w, E
  set s := Nat.sqrt (2 * h) with hs
  set Q := s / 4 with hQ
  set w := Q / 12 with hw
  set E := Nat.sqrt Q with hE
  have hs1 : s ^ 2 ≤ 2 * h := Nat.sqrt_le' _
  have hs2 : 2 * h < (s + 1) ^ 2 := Nat.lt_succ_sqrt' _
  have hs1R : (s : ℝ) ^ 2 ≤ 2 * q ^ 4 := by rw [← hhq]; exact_mod_cast hs1
  have hs2R : 2 * q ^ 4 < ((s : ℝ) + 1) ^ 2 := by rw [← hhq]; exact_mod_cast hs2
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hsup : (s : ℝ) ≤ 1.4143 * q ^ 2 := s_up s q hs0 hs1R
  have hslo : 1.4142 * q ^ 2 < (s : ℝ) + 1 := s_lo s q hs0 hs2R
  have hQ1 : 4 * Q ≤ s := by rw [hQ]; exact Nat.mul_div_le s 4
  have hQ2 : s < 4 * (Q + 1) := by
    rw [hQ]; have := Nat.lt_mul_div_succ s (show 0 < 4 by norm_num); linarith
  have hQ1R : 4 * (Q : ℝ) ≤ s := by exact_mod_cast hQ1
  have hQ2R : (s : ℝ) < 4 * ((Q : ℝ) + 1) := by exact_mod_cast hQ2
  have hq2 : (1000 : ℝ) ≤ q ^ 2 := by linarith
  have hQlo : 0.35 * q ^ 2 ≤ (Q : ℝ) := by linarith
  have hQup : (Q : ℝ) ≤ 0.3536 * q ^ 2 := by linarith
  have hw1 : 12 * w ≤ Q := by rw [hw]; exact Nat.mul_div_le Q 12
  have hw2 : Q < 12 * (w + 1) := by
    rw [hw]; have := Nat.lt_mul_div_succ Q (show 0 < 12 by norm_num); linarith
  have hw2R : (Q : ℝ) < 12 * ((w : ℝ) + 1) := by exact_mod_cast hw2
  have hwlo : 0.029 * q ^ 2 ≤ (w : ℝ) := by linarith
  have hE1 : E ^ 2 ≤ Q := Nat.sqrt_le' _
  have hE2 : Q < (E + 1) ^ 2 := Nat.lt_succ_sqrt' _
  have hE1R : (E : ℝ) ^ 2 ≤ Q := by exact_mod_cast hE1
  have hE2R : (Q : ℝ) < ((E : ℝ) + 1) ^ 2 := by exact_mod_cast hE2
  have hE0 : (0 : ℝ) ≤ E := Nat.cast_nonneg _
  have hEup : (E : ℝ) ≤ 0.6 * q := E_up E Q q hE0 hqpos.le hE1R hQup
  have hElo : 0.59 * q < (E : ℝ) + 1 := E_lo E Q q hE0 hqpos.le hE2R hQlo
  -- natural-number side conditions
  have hQ20 : 20 < Q := by
    have : (20 : ℝ) < Q := by linarith
    exact_mod_cast this
  have hN : 16 * Q ^ 2 ≤ 2 * h := by
    have : (4 * Q) ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left hQ1 2
    have e : (4 * Q) ^ 2 = 16 * Q ^ 2 := by ring
    omega
  have hw1' : 1 ≤ w := by
    have : (1 : ℝ) ≤ w := by linarith
    exact_mod_cast this
  have hQh : Q < h := by
    have : (Q : ℝ) < h := by rw [hhq]; linarith
    exact_mod_cast this
  have hEh : E < h := by
    have : (E : ℝ) < h := by rw [hhq]; linarith
    exact_mod_cast this
  have hE3 : 3 ≤ E := by
    have : (3 : ℝ) ≤ E := by linarith
    exact_mod_cast this
  have hh25 : 25600 ≤ h := by
    have : (25600 : ℝ) ≤ h := by rw [hhq]; linarith
    exact_mod_cast this
  have hnK : 2 * ((1000 + 2) * h) ≤ n := by omega
  have hEn : n < (E + 1) ^ 5 := by
    have h5 : (0.59 * q) ^ 5 ≤ ((E : ℝ) + 1) ^ 5 := pow_le_pow_left₀ (by positivity) hElo.le 5
    have : (n : ℝ) < ((E : ℝ) + 1) ^ 5 := by
      have e : (0.59 * q) ^ 5 = 0.59 ^ 5 * q * q ^ 4 := by ring
      have hq5 : 2005 * q ^ 4 < 0.59 ^ 5 * q * q ^ 4 := by
        have : (2005 : ℝ) < 0.59 ^ 5 * q := by norm_num; linarith
        exact mul_lt_mul_of_pos_right this (pow_pos hqpos 4)
      rw [hhq] at hnh
      linarith
    exact_mod_cast this
  -- the two sides
  have hup := psi_upper n 1000 h E hh25 hnK hE3 hEn
  have hlow := psi_lower_sum 1000 h E Q w (by norm_num) hQ20 hN hw1' hw1 hQh hEh
  rw [← hcnt] at hup
  have hSig := sigma_lower h hl292 (by
    rw [← hl]
    have hsq : √(h : ℝ) = q ^ 2 := by
      rw [hhq, show q ^ 4 = (q ^ 2) ^ 2 by ring, sqrt_sq (by positivity)]
    rw [hsq, hhq]
    exact small_sig q l hl292 hqbig)
  rw [← hl] at hSig
  have hsum := sum_card_T h 1000
  rw [← hsum] at hSig
  have hC := PrimePairSieve.sieve_constants_certificate.1
  -- D bound
  have hlogQ : l / 2 - 5 ≤ Real.log Q - Real.log 20 := by
    have hq2e : q ^ 2 = exp (l / 2) := by
      rw [hq, ← exp_nat_mul]; push_cast; ring_nf
    exact logQ_lem Q q l hq2e hQlo
  have hBS := BS_le E (by omega)
  have hBS0 : 0 ≤ BS E := by
    unfold BS; apply prod_nonneg; intro p hp
    have : (3 : ℝ) ≤ p := by exact_mod_cast three_le_of_mem_Sset hp
    have : 0 ≤ ((p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 2)) := by
      apply div_nonneg (by linarith); apply mul_nonneg <;> linarith
    linarith
  have hD : 2 * (h : ℝ) / (15 * (Real.log Q - Real.log 20)) + (2 * (h : ℝ) / w + 2) * BS E ≤
      (h : ℝ) * Df l := by
    unfold Df
    have hL0 : 0 < l / 2 - 5 := by linarith
    have t1 : 2 * (h : ℝ) / (15 * (Real.log Q - Real.log 20)) ≤ (h : ℝ) * (4 / (15 * (l - 10))) := by
      calc 2 * (h : ℝ) / (15 * (Real.log Q - Real.log 20)) ≤ 2 * (h : ℝ) / (15 * (l / 2 - 5)) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
        _ = (h : ℝ) * (4 / (15 * (l - 10))) := by
            rw [show 15 * (l / 2 - 5) = 15 * (l - 10) / 2 by ring, div_div_eq_mul_div]; ring
    have hwpos : (0 : ℝ) < w := by linarith
    have t2 : 2 * (h : ℝ) / w + 2 ≤ 70 * q ^ 2 := by
      rw [hhq]; exact t2_lem q w hq2 hwlo
    have t3 : (2 * (h : ℝ) / w + 2) * BS E ≤ 70 * q ^ 2 * (0.6 * q) := by
      apply mul_le_mul t2 (hBS.trans hEup) hBS0 (by positivity)
    have t4 : 70 * q ^ 2 * (0.6 * q) ≤ (h : ℝ) * (1 / 1000 / l ^ 2) := by
      rw [hhq]; exact t4_lem q l hl292 hqbig
    have e : (h : ℝ) * (4 / (15 * (l - 10)) + 1 / 1000 / l ^ 2) =
        (h : ℝ) * (4 / (15 * (l - 10))) + (h : ℝ) * (1 / 1000 / l ^ 2) := by ring
    rw [e]; linarith
  -- Bmax bound
  have hBm : Bmax E h ≤ 16.01 * TaoFivePrimes.twinPrimeConstant * h / l ^ 2 := by
    unfold Bmax phi
    rw [← hl]
    have hE1 : (50001 : ℝ) ≤ E := by linarith
    have hρ := rho_lem (E : ℝ) hE1
    have hsq2 : √(2 * (h : ℝ)) ≤ 2 * q ^ 2 := by rw [hhq]; exact sq2_lem q
    have hhl : 0 ≤ (h : ℝ) / l ^ 2 := by positivity
    have hsm : √(2 * (h : ℝ)) + 51204 ≤ 0.0105 * ((h : ℝ) / l ^ 2) := by
      have := small_B q l hl292 hqbig
      rw [hhq]; rw [hhq] at hsq2; linarith
    have e : 16 * TaoFivePrimes.twinPrimeConstant * ((E : ℝ) / ((E : ℝ) - 1)) ^ 4 * ((h : ℝ) / l ^ 2) +
        √(2 * (h : ℝ)) + 51204 = 16 * TaoFivePrimes.twinPrimeConstant * ((E : ℝ) / ((E : ℝ) - 1)) ^ 4 *
          ((h : ℝ) / l ^ 2) + (√(2 * (h : ℝ)) + 51204) := by ring
    rw [e, show 16.01 * TaoFivePrimes.twinPrimeConstant * h / l ^ 2 =
        16.01 * TaoFivePrimes.twinPrimeConstant * ((h : ℝ) / l ^ 2) by ring]
    exact Bm_comb _ _ _ _ PrimePairSieve.sieve_constants_certificate.1 hρ hhl hsm
  have hcnt0 : 0 ≤ cnt := Nat.cast_nonneg _
  have hK : ((1000 : ℕ) : ℝ) = 1000 := by norm_num
  rw [hK] at hlow
  exact final_abstract (h : ℝ) l TaoFivePrimes.twinPrimeConstant _ _ cnt (Bmax E h) (PP E) n _
    hl292 hhpos hnh hC (PP_ge E) hSig hD hlow hup hBm hcnt0

end RV27E



namespace OAI25
open Schnir Finset Real


theorem s6d_zero_mem_B : 0 ∈ B := ⟨3, Nat.prime_three, by norm_num, rfl⟩

theorem s6d_B_sub_A : B ⊆ A := by
  intro b hb
  open Pointwise in exact Set.mem_add.2 ⟨0, s6d_zero_mem_B, b, hb, zero_add b⟩

theorem s6d_one_mem_A : 1 ∈ A :=
  s6d_B_sub_A ⟨5, by norm_num, by norm_num, rfl⟩

theorem s6d_odd_of_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : p % 2 = 1 :=
  Nat.odd_iff.1 (hp.odd_of_ne_two h2)

open Classical in
/-- Medium range: `#(A ∩ [1,N]) + 2 ≥ π(2N+3)`. -/
theorem s6d_medium (N : ℕ) :
    Nat.primeCounting (2 * N + 3) ≤ #{a ∈ Ioc 0 N | a ∈ A} + 2 := by
  set T := (range (2 * N + 4)).filter (fun p => p.Prime ∧ 5 ≤ p) with hT
  have h1 : Nat.primeCounting (2 * N + 3) ≤ #T + 2 := by
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
    have hsub : (range (2 * N + 3 + 1)).filter Nat.Prime ⊆ insert 2 (insert 3 T) := by
      intro p hp
      simp only [mem_filter, mem_range] at hp
      simp only [mem_insert, hT, mem_filter, mem_range]
      by_cases h5 : 5 ≤ p
      · exact Or.inr (Or.inr ⟨by omega, hp.2, h5⟩)
      · have := hp.2.two_le
        interval_cases p
        · simp
        · simp
        · exact absurd hp.2 (by norm_num)
    refine (card_le_card hsub).trans ?_
    refine (card_insert_le _ _).trans ?_
    have := card_insert_le 3 T
    omega
  have h2 : #T ≤ #{a ∈ Ioc 0 N | a ∈ A} := by
    have hinj : Set.InjOn (fun p => (p - 3) / 2) (T : Set ℕ) := by
      intro p hp q hq hpq
      simp only [hT, coe_filter, mem_range, Set.mem_ofPred_eq] at hp hq
      have := s6d_odd_of_prime hp.2.1 (by omega)
      have := s6d_odd_of_prime hq.2.1 (by omega)
      simp only at hpq
      omega
    rw [← card_image_of_injOn hinj]
    apply card_le_card
    intro a ha
    simp only [hT, mem_image, mem_filter, mem_range] at ha
    obtain ⟨p, ⟨hp1, hp2, hp3⟩, rfl⟩ := ha
    have := s6d_odd_of_prime hp2 (by omega)
    simp only [mem_filter, mem_Ioc]
    exact ⟨⟨by omega, by omega⟩, s6d_B_sub_A ⟨p, hp2, by omega, rfl⟩⟩
  omega

open Classical in
/-- Large range: `#(A ∩ [1,N]) + 1 ≥ R(2N+6)`. -/
theorem s6d_large (N : ℕ) :
    #((range (2 * N + 6 + 1)).filter (fun s => 0 < r s)) ≤ #{a ∈ Ioc 0 N | a ∈ A} + 1 := by
  set T := (range (2 * N + 6 + 1)).filter (fun s => 0 < r s) with hT
  have hmem : ∀ s ∈ T, ∃ p q, p.Prime ∧ p ≠ 2 ∧ q.Prime ∧ q ≠ 2 ∧ s = p + q ∧ s ≤ 2 * N + 6 := by
    intro s hs
    simp only [hT, mem_filter, mem_range] at hs
    obtain ⟨hs1, hs2⟩ := hs
    unfold r at hs2
    obtain ⟨p, hp⟩ := card_pos.1 hs2
    simp only [mem_filter, mem_range] at hp
    exact ⟨p, s - p, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2, by omega, by omega⟩
  have hinj : Set.InjOn (fun s => (s - 6) / 2) (T : Set ℕ) := by
    intro s hs t ht hst
    obtain ⟨p, q, hp, hp2, hq, hq2, rfl, -⟩ := hmem s hs
    obtain ⟨p', q', hp', hp2', hq', hq2', rfl, -⟩ := hmem t ht
    have := s6d_odd_of_prime hp hp2
    have := s6d_odd_of_prime hq hq2
    have := s6d_odd_of_prime hp' hp2'
    have := s6d_odd_of_prime hq' hq2'
    have := hp.two_le; have := hq.two_le; have := hp'.two_le; have := hq'.two_le
    simp only at hst
    omega
  rw [← card_image_of_injOn hinj]
  have hsub : T.image (fun s => (s - 6) / 2) ⊆ insert 0 ({a ∈ Ioc 0 N | a ∈ A}) := by
    intro a ha
    obtain ⟨s, hs, rfl⟩ := mem_image.1 ha
    obtain ⟨p, q, hp, hp2, hq, hq2, rfl, hle⟩ := hmem _ hs
    have := s6d_odd_of_prime hp hp2
    have := s6d_odd_of_prime hq hq2
    have := hp.two_le; have := hq.two_le
    rw [mem_insert, mem_filter, mem_Ioc]
    by_cases h0 : (p + q - 6) / 2 = 0
    · exact Or.inl h0
    · refine Or.inr ⟨⟨by omega, by omega⟩, ?_⟩
      have : (p + q - 6) / 2 = (p - 3) / 2 + (q - 3) / 2 := by omega
      rw [this]
      open Pointwise in
      exact Set.mem_add.2 ⟨(p - 3) / 2, ⟨p, hp, hp2, rfl⟩, (q - 3) / 2, ⟨q, hq, hq2, rfl⟩, rfl⟩
  exact (card_le_card hsub).trans (card_insert_le _ _)

theorem s6d_two_mem_A : 2 ∈ A :=
  open Pointwise in Set.mem_add.2 ⟨1, ⟨5, by norm_num, by norm_num, rfl⟩, 1, ⟨5, by norm_num, by norm_num, rfl⟩, rfl⟩

theorem s6d_three_mem_A : 3 ∈ A :=
  open Pointwise in Set.mem_add.2 ⟨1, ⟨5, by norm_num, by norm_num, rfl⟩, 2, ⟨7, by norm_num, by norm_num, rfl⟩, rfl⟩


theorem n9_mem_B (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) : (p - 3) / 2 ∈ B := ⟨p, hp, h2, rfl⟩

theorem n9_small_mem_A (a : ℕ) (h1 : 1 ≤ a) (h10 : a ≤ 10) : a ∈ A := by
  have b0 : 0 ∈ B := n9_mem_B 3 (by norm_num) (by norm_num)
  have b1 : 1 ∈ B := n9_mem_B 5 (by norm_num) (by norm_num)
  have b2 : 2 ∈ B := n9_mem_B 7 (by norm_num) (by norm_num)
  have b4 : 4 ∈ B := n9_mem_B 11 (by norm_num) (by norm_num)
  have b5 : 5 ∈ B := n9_mem_B 13 (by norm_num) (by norm_num)
  open Pointwise in
  interval_cases a
  · exact Set.mem_add.2 ⟨0, b0, 1, b1, rfl⟩
  · exact Set.mem_add.2 ⟨0, b0, 2, b2, rfl⟩
  · exact Set.mem_add.2 ⟨1, b1, 2, b2, rfl⟩
  · exact Set.mem_add.2 ⟨0, b0, 4, b4, rfl⟩
  · exact Set.mem_add.2 ⟨0, b0, 5, b5, rfl⟩
  · exact Set.mem_add.2 ⟨1, b1, 5, b5, rfl⟩
  · exact Set.mem_add.2 ⟨2, b2, 5, b5, rfl⟩
  · exact Set.mem_add.2 ⟨4, b4, 4, b4, rfl⟩
  · exact Set.mem_add.2 ⟨4, b4, 5, b5, rfl⟩
  · exact Set.mem_add.2 ⟨5, b5, 5, b5, rfl⟩

open Classical in
/-- `σ(A) ≥ 1/13`. -/
theorem density_A : (1 : ℝ) / 12 ≤ schnirelmannDensity A := by
  rw [le_schnirelmannDensity_iff]
  intro N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [div_le_div_iff₀ (by norm_num) hNpos, one_mul]
  by_cases hsmall : N ≤ 120
  · by_cases h10 : 10 ≤ N
    · have h1 : Icc 1 10 ⊆ {a ∈ Ioc 0 N | a ∈ A} := by
        intro a ha
        simp only [Finset.mem_Icc] at ha
        simp only [mem_filter, mem_Ioc]
        exact ⟨⟨by omega, by omega⟩, n9_small_mem_A a ha.1 ha.2⟩
      have h2 := card_le_card h1
      have h3' : (10 : ℝ) ≤ #{a ∈ Ioc 0 N | a ∈ A} := by
        rw [Nat.card_Icc] at h2; exact_mod_cast h2
      have : (N : ℝ) ≤ 120 := by exact_mod_cast hsmall
      linarith
    · have h1 : Icc 1 N ⊆ {a ∈ Ioc 0 N | a ∈ A} := by
        intro a ha
        simp only [Finset.mem_Icc] at ha
        simp only [mem_filter, mem_Ioc]
        exact ⟨⟨by omega, ha.2⟩, n9_small_mem_A a ha.1 (by omega)⟩
      have h2 := card_le_card h1
      have h3' : (N : ℝ) ≤ #{a ∈ Ioc 0 N | a ∈ A} := by
        rw [Nat.card_Icc] at h2; exact_mod_cast (show N ≤ _ by omega)
      linarith
  push Not at hsmall
  have hN' : (121 : ℝ) ≤ N := by exact_mod_cast hsmall
  have hL := s6d_large N
  have hL' : (#((range (2 * N + 6 + 1)).filter (fun s => 0 < r s)) : ℝ)
      ≤ #{a ∈ Ioc 0 N | a ∈ A} + 1 := by exact_mod_cast hL
  have hy6 : (0 : ℝ) < ((2 * N + 6 : ℕ) : ℝ) := by push_cast; linarith
  have hx22 : (10 : ℝ) ^ 9 ≤ exp 22 := by
    have h3 : (2.7 : ℝ) ≤ exp 1 := by linarith [exp_one_gt_d9]
    have e : exp 22 = exp 1 ^ 22 := by rw [← exp_nat_mul]; norm_num
    rw [e]
    calc (10 : ℝ) ^ 9 ≤ 2.7 ^ 22 := by norm_num
      _ ≤ exp 1 ^ 22 := pow_le_pow_left₀ (by norm_num) h3 22
  by_cases hbig : exp 300 ≤ ((2 * N + 6 : ℕ) : ℝ)
  · have hR := RV27E.large_range_aux _ hbig
    have hx : exp 22 ≤ exp 300 := exp_le_exp.2 (by norm_num)
    push_cast at hR hbig
    linarith
  push Not at hbig
  by_cases hmid : 22 ≤ log ((2 * N + 6 : ℕ) : ℝ)
  · have hlog : log ((2 * N + 6 : ℕ) : ℝ) ≤ 300 := by
      rw [log_le_iff_le_exp hy6]; exact hbig.le
    have hR := P27.rv_range _ hmid hlog
    have hx : exp 22 ≤ ((2 * N + 6 : ℕ) : ℝ) := by
      rw [← exp_log hy6]; exact exp_le_exp.2 hmid
    push_cast at hR hx
    linarith
  · push Not at hmid
    have hy : (30 : ℝ) ≤ ((2 * N + 3 : ℕ) : ℝ) := by push_cast; linarith
    have hP := Chebyshev.psi_lower _ hy
    have hpi := Chebyshev.psi_le_primeCounting_mul_log (2 * N + 3)
    have ha := Chebyshev.a_bound.1
    have hM := s6d_medium N
    have hM' : (Nat.primeCounting (2 * N + 3) : ℝ) ≤ #{a ∈ Ioc 0 N | a ∈ A} + 2 := by
      exact_mod_cast hM
    have hypos : (0 : ℝ) < ((2 * N + 3 : ℕ) : ℝ) := by linarith
    have hlogpos : 0 < log ((2 * N + 3 : ℕ) : ℝ) := log_pos (by linarith)
    have hlog36 : log ((2 * N + 3 : ℕ) : ℝ) ≤ log ((2 * N + 6 : ℕ) : ℝ) :=
      log_le_log hypos (by push_cast; linarith)
    have hpi0 : (0 : ℝ) ≤ (Nat.primeCounting (2 * N + 3) : ℝ) := Nat.cast_nonneg _
    have hma : Chebyshev.a * ((2 * N + 3 : ℕ) : ℝ) ≥ 0.9212 * ((2 * N + 3 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right ha hypos.le
    by_cases hlo : N < 100000
    · have hlog : log ((2 * N + 3 : ℕ) : ℝ) < 13 := by
        rw [log_lt_iff_lt_exp hypos]
        have he := exp_one_gt_d9
        have h13 : exp 13 = exp 1 ^ 13 := by rw [← exp_nat_mul]; norm_num
        have h3 : (2.7182818283 : ℝ) ^ 13 ≤ exp 1 ^ 13 := pow_le_pow_left₀ (by norm_num) he.le 13
        have hN5 : (N : ℝ) < 100000 := by exact_mod_cast hlo
        push_cast
        nlinarith
      have hmul : (Nat.primeCounting (2 * N + 3) : ℝ) * log ((2 * N + 3 : ℕ) : ℝ) ≤
          (Nat.primeCounting (2 * N + 3) : ℝ) * 13 :=
        mul_le_mul_of_nonneg_left hlog.le hpi0
      have hlog5 : 5 * log ((2 * N + 3 : ℕ) : ℝ) ≤ 5 * 13 := by linarith
      push_cast at hma hP hpi hmul hlog5 hlog
      nlinarith
    · push Not at hlo
      have hN5 : (100000 : ℝ) ≤ N := by exact_mod_cast hlo
      have hlog : log ((2 * N + 3 : ℕ) : ℝ) < 22 := by linarith
      have hmul : (Nat.primeCounting (2 * N + 3) : ℝ) * log ((2 * N + 3 : ℕ) : ℝ) ≤
          (Nat.primeCounting (2 * N + 3) : ℝ) * 22 :=
        mul_le_mul_of_nonneg_left hlog.le hpi0
      have hlog5 : 5 * log ((2 * N + 3 : ℕ) : ℝ) ≤ 5 * 22 := by linarith
      push_cast at hma hP hpi hmul hlog5 hlog
      nlinarith

open Pointwise

theorem s6m_zero_mem_A : (0 : ℕ) ∈ A :=
  Set.mem_add.2 ⟨0, ⟨3, Nat.prime_three, by norm_num, rfl⟩, 0, ⟨3, Nat.prime_three, by norm_num, rfl⟩,
    rfl⟩

/-- `P k t`: there are `k` odd primes summing to `2t + 3k`. -/
def s6m_P (k t : ℕ) : Prop :=
  ∃ s : Multiset ℕ, s.card = k ∧ (∀ p ∈ s, Nat.Prime p ∧ p ≠ 2) ∧ s.sum = 2 * t + 3 * k

theorem s6m_P_add {j k t u : ℕ} (h1 : s6m_P j t) (h2 : s6m_P k u) : s6m_P (j + k) (t + u) := by
  obtain ⟨s, hs1, hs2, hs3⟩ := h1
  obtain ⟨s', hs1', hs2', hs3'⟩ := h2
  refine ⟨s + s', by simp [hs1, hs1'], fun p hp => ?_, by simp [hs3, hs3']; ring⟩
  rcases Multiset.mem_add.1 hp with h | h
  · exact hs2 p h
  · exact hs2' p h

theorem s6m_P_B {b : ℕ} (hb : b ∈ B) : s6m_P 1 b := by
  obtain ⟨p, hp, hp2, rfl⟩ := hb
  have := Nat.odd_iff.1 (hp.odd_of_ne_two hp2)
  have := hp.two_le
  refine ⟨{p}, by simp, fun q hq => ?_, ?_⟩
  · rw [Multiset.mem_singleton] at hq; subst hq; exact ⟨hp, hp2⟩
  · simp; omega

theorem s6m_P_A {a : ℕ} (ha : a ∈ A) : s6m_P 2 a := by
  obtain ⟨b, hb, c, hc, rfl⟩ := Set.mem_add.1 ha
  exact s6m_P_add (s6m_P_B hb) (s6m_P_B hc)


theorem n9_P_multiset (t : Multiset ℕ) (ht : ∀ x ∈ t, x ∈ A) : s6m_P (2 * t.card) t.sum := by
  induction t using Multiset.induction_on with
  | empty => exact ⟨0, by simp, by simp, by simp⟩
  | cons a t ih =>
    have h1 := ih (fun x hx => ht x (Multiset.mem_cons_of_mem hx))
    have h2 := s6m_P_A (ht a (Multiset.mem_cons_self a t))
    have := s6m_P_add h2 h1
    rw [Multiset.card_cons, Multiset.sum_cons]
    rwa [show 2 * (t.card + 1) = 2 + 2 * t.card by ring]

open Classical in
theorem n9_all (t : ℕ) : s6m_P 24 t := by
  have hA := density_A
  have hk : (1 : ℝ) ≤ ((12 : ℕ) : ℝ) * schnirelmannDensity A := by
    push_cast; linarith
  obtain ⟨u, hu1, hu2, hu3⟩ := basis_of_density A s6m_zero_mem_A 12 hk t
  have := n9_P_multiset u hu2
  rwa [hu1, hu3] at this

/-- Every odd `n ≥ 51` is a sum of exactly `25` primes. -/
theorem exact_25 (n : ℕ) (hodd : Odd n) (hn : 51 ≤ n) :
    ∃ s : Multiset ℕ, s.card = 25 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  have hn2 := Nat.odd_iff.1 hodd
  by_cases hbig : 75 ≤ n
  · obtain ⟨s, hs1, hs2, hs3⟩ := n9_all ((n - 75) / 2)
    refine ⟨3 ::ₘ s, by simp [hs1], fun p hp => ?_, ?_⟩
    · rcases Multiset.mem_cons.1 hp with h | h
      · rw [h]; exact Nat.prime_three
      · exact (hs2 p h).1
    · rw [Multiset.sum_cons, hs3]; omega
  · refine ⟨Multiset.replicate (n - 50) 3 + Multiset.replicate (75 - n) 2,
      by simp; omega, fun p hp => ?_, ?_⟩
    · rcases Multiset.mem_add.1 hp with h | h
      · rw [Multiset.eq_of_mem_replicate h]; exact Nat.prime_three
      · rw [Multiset.eq_of_mem_replicate h]; exact Nat.prime_two
    · simp; omega

end OAI25

/-- The campaign goal (platform theorem `odd_sum_le_25_primes`). -/
theorem solution (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 25 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  by_cases hbig : 51 ≤ n
  · obtain ⟨s, hs1, hs2, hs3⟩ := OAI25.exact_25 n hodd hbig
    exact ⟨s, hs1.le, hs2, hs3⟩
  · have hn2 := Nat.odd_iff.1 hodd
    refine ⟨3 ::ₘ Multiset.replicate ((n - 3) / 2) 2, by simp; omega, fun p hp => ?_, ?_⟩
    · rcases Multiset.mem_cons.1 hp with h | h
      · rw [h]; exact Nat.prime_three
      · rw [Multiset.eq_of_mem_replicate h]; exact Nat.prime_two
    · simp; omega

#print axioms solution
