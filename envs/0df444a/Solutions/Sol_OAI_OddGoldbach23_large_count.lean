-- Prove2me | solution 1 for OAI.OddGoldbach23.large_count
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-25T07:59:27.496775+00:00
-- url     : https://prove2.me/submissions/e3485d98-d364-4947-b2b3-a12cf872dffd

import Mathlib
import Definitions.Def_Schnir_defs
import Theorems.Thm_PrimePairSieve_sieve_constants_certificate
import Definitions.Def_TaoFivePrimes_SingularSeries
import Theorems.Thm_RV27_interval_goldbach_bound
import Theorems.Thm_RV27_interval_pair_weight_lower

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
open Finset Real
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
    2005 * 16.01 / l ^ 2 ≤ 10.995 * ((16 / 15) * Af l ^ 2 / 1000 - Af l * Df l) := by
  unfold Af Df
  have hl0 : 0 < l := by linarith
  have hl10 : 0 < l - 10 := by linarith
  have hl7 : 0 < l + 7 := by linarith
  set t := l - 292 with ht
  have ht0 : 0 ≤ t := by linarith
  have hlt : l = t + 292 := by rw [ht]; ring
  have key : 10.995 * ((16 / 15) * (1845 / (l + 7) - 8.4 / l) ^ 2 / 1000 -
      (1845 / (l + 7) - 8.4 / l) * (4 / (15 * (l - 10)) + 1 / 1000 / l ^ 2)) - 2005 * 16.01 / l ^ 2 =
      (51868760992 * t ^ 4 + 46480899117599 * t ^ 3 + 14255732997662849 * t ^ 2 + 1601823601786663312 * t + 32387425852146737748) /
        (25000000 * l ^ 3 * (l - 10) * (l + 7) ^ 2) := by
    rw [hlt]
    have h1 : t + 292 ≠ 0 := by linarith
    have h2 : t + 292 - 10 ≠ 0 := by linarith
    have h3 : t + 292 + 7 ≠ 0 := by linarith
    field_simp
    ring
  have hpos : 0 ≤ (51868760992 * t ^ 4 + 46480899117599 * t ^ 3 + 14255732997662849 * t ^ 2 + 1601823601786663312 * t + 32387425852146737748) /
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
    n * (100 / 2199) ≤ cnt := by
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
  have hgl : 2005 * 16.01 ≤ 10.995 * g * l ^ 2 := by
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
  have : 2005 * h * (100 / 2199) ≤ cnt := by
    have : h * (2005 * 16.01) ≤ h * (10.995 * g * l ^ 2) := mul_le_mul_of_nonneg_left hgl hh.le
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
    (n : ℝ) * (100 / 2199) ≤ (((range (n + 1)).filter (fun s => 0 < Schnir.r s)).card : ℝ) := by
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




theorem solution (n : ℕ) (hn : Real.exp 300 ≤ (n : ℝ)) :
    (n : ℝ) * (100 / 2199) ≤ (((Finset.range (n + 1)).filter (fun s => 0 < Schnir.r s)).card : ℝ) := RV27E.large_range_aux n hn
#print axioms solution
