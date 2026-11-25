-- Prove2me | solution 1 for ManyServerQED.Scheduling.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T19:37:23.147998+00:00
-- url     : https://prove2.me/submissions/7cdc2392-4c56-4d3f-b1e4-5e9fc075a2c9

import Theorems.Thm_ManyServerQED_Scheduling_queue_state_moment_from_forcing
import Theorems.Thm_ManyServerQED_Scheduling_queue_forcing_polynomial_moment

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

private theorem uniform_service_abandon_rates {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) :
    ∃ a > 0, ∀ᶠ n in atTop, ∀ i, M.muN n i ≤ a ∧ M.thetaN n i ≤ a := by
  let a := 1 + ∑ i, (M.mu i + M.theta i)
  have hbase (i : Fin k) : 0 ≤ M.mu i + M.theta i :=
    add_nonneg (M.mu_pos i).le (M.theta_nonneg i)
  refine ⟨a, add_pos_of_pos_of_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => hbase i)), ?_⟩
  rw [Filter.eventually_all]
  intro i
  have hle := Finset.single_le_sum (fun j _ => hbase j) (Finset.mem_univ i)
  have h₁ : M.mu i < a := by dsimp [a]; linarith [M.theta_nonneg i]
  have h₂ : M.theta i < a := by dsimp [a]; linarith [M.mu_pos i]
  filter_upwards [(tendsto_order.1 (M.mu_lim i)).2 _ h₁,
    (tendsto_order.1 (M.theta_lim i)).2 _ h₂] with n hM hO
  exact ⟨hM.le, hO.le⟩

private theorem increasing_polynomial_bound (m d : ℕ) (hmd : m ≤ d) {s : ℝ} (hs : 0 ≤ s) :
    1 + s^m ≤ 2 * (1 + s^d) := by
  rcases le_total s 1 with h | h
  · linarith [pow_le_one₀ (n := m) hs h, pow_nonneg hs d]
  · linarith [pow_le_pow_right₀ h hmd, pow_nonneg hs d]

private theorem absorb_time_multiplier (k a p : ℝ) (hk : 0 ≤ k) (ha : 0 ≤ a) (hp : 0 ≤ p)
    (m d : ℕ) (hD : 2 * p + m ≤ (d : ℝ)) (t : ℝ) (ht : 0 ≤ t) :
    (k * (1 + a * t)^2)^p * (1 + t^m) ≤ 2 * ((k * (1 + a)^2)^p) * (1 + t^d) := by
  let b := (k * (1 + a)^2)^p
  have hbase : 0 ≤ k * (1 + a)^2 := by positivity
  have hb : 0 ≤ b := Real.rpow_nonneg hbase _
  rcases le_total t 1 with ht1 | ht1
  · have hr : (k * (1 + a * t)^2)^p ≤ b := by
      apply Real.rpow_le_rpow (by positivity) _ hp
      apply mul_le_mul_of_nonneg_left _ hk
      have h : a * t ≤ a := mul_le_of_le_one_right ha ht1
      gcongr
    calc
      _ ≤ b * 2 := mul_le_mul hr (by linarith [pow_le_one₀ (n := m) ht ht1])
        (by positivity) hb
      _ ≤ _ := by linarith [mul_nonneg hb (pow_nonneg ht d)]
  · have hta : 1 + a * t ≤ (1 + a) * t := by linarith
    have hr : (k * (1 + a * t)^2)^p ≤ b * t^(2*p) := by
      have h1 : k * (1 + a * t)^2 ≤ (k * (1 + a)^2) * t^2 := by
        rw [mul_assoc, ← mul_pow]
        gcongr
      have h2 := Real.rpow_le_rpow (by positivity : 0 ≤ k * (1 + a * t)^2) h1 hp
      rwa [Real.mul_rpow hbase (sq_nonneg _), ← Real.rpow_natCast t 2, ← Real.rpow_mul ht,
        Nat.cast_ofNat] at h2
    have htM : 1 ≤ t^m := one_le_pow₀ ht1
    have hr' : t^(2*p + (m : ℝ)) ≤ t^d := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le ht1 hD
    calc
      _ ≤ (b * t^(2*p)) * (2 * t^m) := mul_le_mul hr (by linarith)
        (by positivity) (mul_nonneg hb (Real.rpow_nonneg ht _))
      _ = 2 * b * t^(2*p + (m : ℝ)) := by
        rw [Real.rpow_add (zero_lt_one.trans_le ht1), Real.rpow_natCast]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hr'.trans (le_add_of_nonneg_left zero_le_one)) (by positivity)

theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (M : SystemSequence Ω k) (mL mU : ℝ)
    (hA3 : M.Assumption3 mL mU) :
    ∃ (c : ℝ) (mbar : ℕ), ∀ (x : Fin k → ℝ) (X0 : ℕ → Fin k → ℕ),
      Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x) →
      ∀ (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ),
      (∀ n, 1 ≤ n → M.IsSCP n (X0 n) (X n) (Ψ n) ∧ M.IsAdmissible n (X n) (Ψ n) ∧
        IsWorkConserving n (X n) (Ψ n)) →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ t : ℝ, 0 ≤ t →
      ∫⁻ ω, ENNReal.ofReal (l1norm (M.Xhat n (X n) ω t)) ^ mU ∂M.P ≤
        ENNReal.ofReal (c * (1 + l1norm x ^ mbar) * (1 + t ^ mbar)) := by
  have hp : 0 ≤ mU := (by norm_num : (0 : ℝ) ≤ 2).trans hA3.1
  by_cases h0 : k = 0
  · subst k
    refine ⟨0, 0, fun x X0 hx X Ψ hP => ⟨0, fun n hn t ht => ?_⟩⟩
    simp [l1norm, ENNReal.zero_rpow_of_pos ((by norm_num : (0 : ℝ) < 2).trans_le hA3.1)]
  letI : NeZero k := ⟨h0⟩
  obtain ⟨a, ha, hRates⟩ := uniform_service_abandon_rates M
  obtain ⟨c, m, hFor⟩ := queue_forcing_polynomial_moment M mL mU hA3
  let b := ((k : ℝ) * (1 + a)^2)^mU
  let d := max m ⌈2 * mU + (m : ℝ)⌉₊
  have hD : 2*mU + (m : ℝ) ≤ (d : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right m ⌈2 * mU + (m : ℝ)⌉₊)
  refine ⟨4 * (c : ℝ) * b, d, fun x X0 hx X Ψ hP => ?_⟩
  obtain ⟨N, hN⟩ := hFor x X0 hx X Ψ (fun n hn => ⟨(hP n hn).1.controlled, (hP n hn).2.2⟩)
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hRates
  refine ⟨max N (max J 1), fun n hn t ht => ?_⟩
  have hn' : 1 ≤ n := by omega
  have hrs := hJ n (by omega)
  have htransfer := queue_state_moment_from_forcing M n hn' (X0 n) (X n) (Ψ n)
    (hP n hn').1.controlled (hP n hn').2.2 a ha (fun i => (hrs i).1) (fun i => (hrs i).2) t ht mU hp
  dsimp only at htransfer
  have hf := hN n (by omega) t ht
  dsimp only at hf
  refine (htransfer.trans (mul_le_mul_right hf _)).trans ?_
  let g := ((k : ℝ) * (1 + a*t)^2)^mU
  have hg : 0 ≤ g := Real.rpow_nonneg (by positivity) _
  have hb : 0 ≤ b := Real.rpow_nonneg (by positivity) _
  have hxN : 0 ≤ l1norm x := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  change ENNReal.ofReal ((k : ℝ) * (1 + a*t)^2)^mU *
    ENNReal.ofReal ((c : ℝ) * (1 + l1norm x^m) * (1 + t^m)) ≤ _
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity : 0 ≤ (k : ℝ) * (1+a*t)^2) hp,
    ← ENNReal.ofReal_mul hg]
  apply ENNReal.ofReal_le_ofReal
  have hxP := increasing_polynomial_bound m d (le_max_left _ _) hxN
  have htP := absorb_time_multiplier (k : ℝ) a mU (Nat.cast_nonneg k) ha.le hp m d hD t ht
  calc
    g * ((c : ℝ) * (1 + l1norm x^m) * (1 + t^m)) =
        (c : ℝ) * (1 + l1norm x^m) * (g * (1 + t^m)) := by ring
    _ ≤ (c : ℝ) * (2 * (1 + l1norm x^d)) * (2 * b * (1 + t^d)) := by gcongr
    _ = _ := by ring
