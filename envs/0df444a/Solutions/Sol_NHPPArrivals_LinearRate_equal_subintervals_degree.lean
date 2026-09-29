-- Prove2me | solution 1 for NHPPArrivals.LinearRate.equal_subintervals_degree
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T04:50:33.66914+00:00
-- url     : https://prove2.me/submissions/79f6aa46-77e7-46bf-beab-ae82e7b7d9cd

import Mathlib
import Definitions.Def_NHPPArrivals_LinearRate_ConditionalCdf

set_option autoImplicit false

open NHPPArrivals.LinearRate in
theorem p9158_cum (a b x : ℝ) : cumRate (linRate a b) x = a * x + b * x ^ 2 / 2 := by
  unfold cumRate linRate
  rw [intervalIntegral.integral_add intervalIntegrable_const
    ((intervalIntegral.intervalIntegrable_id).const_mul b)]
  rw [intervalIntegral.integral_const_mul, integral_id]
  simp
  ring

theorem p9158_tele (g : ℝ → ℝ) (n : ℕ) :
    ∑ j ∈ Finset.Icc 1 n, (g j - g ((j:ℝ) - 1)) = g n - g 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    simp only [add_sub_cancel_right]
    ring

theorem p9158_alg4 (w b T K L : ℝ) (hK : 0 < K) (hT : 0 < T) (hL : 0 < L) (hb : 0 ≤ b) :
    w * (b * (T / K) / 2 / (L + b * (T / K) / 2) / 4) =
      w * (b / L * T / K) / (8 + 4 * (b / L) * T / K) := by
  have h1 : 0 < L + b * (T / K) / 2 := by positivity
  have h2 : 0 < 8 + 4 * (b / L) * T / K := by positivity
  field_simp
  ring

theorem p9158_alg5 (w a b T K m : ℝ) (ha : a = 0) (hK : 0 < K) (hT : 0 < T) (hb : 0 < b)
    (hm : 0 < m) :
    w * (b * (T / K) / 2 / (a + b * (m * T / K) + b * (T / K) / 2) / 4) =
      w / m / (8 + 4 / m) := by
  subst ha
  have h1 : 0 < 0 + b * (m * T / K) + b * (T / K) / 2 := by positivity
  have h2 : 0 < 8 + 4 / m := by positivity
  field_simp
  ring

theorem p9158_alg1 (w a b T K : ℝ) (ha : a = 0) (hK : 0 < K) (hT : 0 < T) (hb : 0 < b) :
    w * (b * (T / K) / 2 / (a + b * (0 * T / K) + b * (T / K) / 2) / 4) = w / 4 := by
  subst ha
  have h1 : 0 < b * (T / K) / 2 := by positivity
  simp only [zero_mul, zero_div, mul_zero, zero_add]
  rw [div_self h1.ne']
  ring

theorem p9158_quad (F : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c) (hF : ∀ t, F t - t = c * (t ^ 2 - t)) :
    IsGreatest ((fun t => |F t - t|) '' Set.Icc (0:ℝ) 1) (c / 4) := by
  refine ⟨⟨1/2, ⟨by norm_num, by norm_num⟩, ?_⟩, ?_⟩
  · simp only [hF]
    rw [abs_of_nonpos (by nlinarith)]
    ring
  · rintro y ⟨t, ⟨h0, h1⟩, rfl⟩
    simp only [hF]
    rw [abs_le]
    constructor
    · nlinarith [mul_nonneg hc (sq_nonneg (t - 1/2))]
    · nlinarith [mul_nonneg hc (mul_nonneg h0 (sub_nonneg.2 h1))]

open NHPPArrivals.LinearRate in
theorem solution (a b T : ℝ) (hT : 0 < T) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : 0 < a ∨ 0 < b) :
    ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k →
      IsGreatest ((fun t => |mixCdf (linRate a b) T k t - t|) '' Set.Icc (0:ℝ) 1)
        (degree (mixCdf (linRate a b) T k)) ∧
      (∀ j ∈ Finset.Icc 1 k,
        IsGreatest ((fun t => |subCdf (linRate a b) T k j t - t|) '' Set.Icc (0:ℝ) 1)
          (degree (subCdf (linRate a b) T k j))) ∧
      degree (mixCdf (linRate a b) T k) =
        ∑ j ∈ Finset.Icc 1 k,
          weight (linRate a b) T k j * degree (subCdf (linRate a b) T k j) ∧
      (0 < a → degree (mixCdf (linRate a b) T k) =
        ∑ j ∈ Finset.Icc 1 k,
          weight (linRate a b) T k j * (subSlope a b T k j * T / k) /
            (8 + 4 * subSlope a b T k j * T / k)) ∧
      (a = 0 → degree (mixCdf (linRate a b) T k) =
        weight (linRate a b) T k 1 / 4 +
          ∑ j ∈ Finset.Icc 2 k,
            (weight (linRate a b) T k j / ((j:ℝ) - 1)) / (8 + 4 / ((j:ℝ) - 1))) ∧
      degree (mixCdf (linRate a b) T k) ≤ C / k := by
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : ℝ, Λ = a * T + b * T ^ 2 / 2 := ⟨_, rfl⟩
  have hΛpos : 0 < Λ := by
    rw [hΛdef]
    rcases hab with h | h
    · have : 0 ≤ b * T ^ 2 / 2 := by positivity
      have : 0 < a * T := mul_pos h hT
      linarith
    · have : 0 ≤ a * T := mul_nonneg ha hT.le
      have : 0 < b * T ^ 2 / 2 := by positivity
      linarith
  refine ⟨b * T ^ 2 / (8 * Λ), ?_⟩
  intro k hk
  have hkpos : (0:ℝ) < k := by exact_mod_cast hk
  have hk0 : (k:ℝ) ≠ 0 := hkpos.ne'
  obtain ⟨P, hPdef⟩ : ∃ P : ℕ → ℝ,
      P = fun j : ℕ => a + b * (((j:ℝ) - 1) * T / k) + b * (T / k) / 2 := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c : ℕ → ℝ, c = fun j => (b * (T / k) / 2) / P j := ⟨_, rfl⟩
  have hL : ∀ j ∈ Finset.Icc 1 k, 0 ≤ b * (((j:ℝ) - 1) * T / k) := by
    intro j hj
    have hj1 : (1:ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.1 hj).1
    exact mul_nonneg hb (div_nonneg (mul_nonneg (by linarith) hT.le) hkpos.le)
  have hP : ∀ j ∈ Finset.Icc 1 k, 0 < P j := by
    intro j hj
    have h1 := hL j hj
    simp only [hPdef]
    rcases hab with h | h
    · have : 0 ≤ b * (T / k) / 2 := by positivity
      linarith
    · have : 0 < b * (T / k) / 2 := by positivity
      linarith
  have hc0 : ∀ j ∈ Finset.Icc 1 k, 0 ≤ c j := by
    intro j hj
    simp only [hcdef]
    exact div_nonneg (by positivity) (hP j hj).le
  have hsubCum : ∀ (j : ℕ) (s : ℝ), subCum (linRate a b) T k j s =
      (a + b * (((j:ℝ) - 1) * T / k)) * s + b * s ^ 2 / 2 := by
    intro j s
    unfold subCum
    rw [p9158_cum, p9158_cum]
    ring
  have key : ∀ j ∈ Finset.Icc 1 k, ∀ t : ℝ,
      subCdf (linRate a b) T k j t - t = c j * (t ^ 2 - t) := by
    intro j hj t
    have hPj := hP j hj
    have hτ : T / (k:ℝ) ≠ 0 := by positivity
    have e1 : subCum (linRate a b) T k j (t * T / k) =
        (T / k) * (P j * t + (b * (T / k) / 2) * (t ^ 2 - t)) := by
      rw [hsubCum]
      simp only [hPdef]
      ring
    have e2 : subCum (linRate a b) T k j (T / k) = (T / k) * P j := by
      rw [hsubCum]
      simp only [hPdef]
      ring
    unfold subCdf
    rw [e1, e2, mul_div_mul_left _ _ hτ, add_div, mul_div_cancel_left₀ _ hPj.ne']
    simp only [hcdef]
    ring
  have hw : ∀ j : ℕ, weight (linRate a b) T k j = (T / k) * P j / Λ := by
    intro j
    unfold weight
    rw [p9158_cum, p9158_cum, p9158_cum]
    simp only [hPdef, hΛdef]
    ring
  have hsumw : ∑ j ∈ Finset.Icc 1 k, weight (linRate a b) T k j = 1 := by
    unfold weight
    rw [← Finset.sum_div]
    have ht := p9158_tele (fun x => cumRate (linRate a b) (x * T / k)) k
    rw [ht, mul_div_cancel_left₀ T hk0, zero_mul, zero_div, p9158_cum, p9158_cum]
    rw [div_eq_one_iff_eq (by rw [← hΛdef]; exact hΛpos.ne')]
    ring
  have hwc : ∀ j ∈ Finset.Icc 1 k,
      weight (linRate a b) T k j * c j = b * (T / k) ^ 2 / (2 * Λ) := by
    intro j hj
    have hPj := (hP j hj).ne'
    have hΛne := hΛpos.ne'
    rw [hw]
    simp only [hcdef]
    field_simp
  have hS : ∑ j ∈ Finset.Icc 1 k, weight (linRate a b) T k j * c j =
      b * T ^ 2 / (2 * k * Λ) := by
    rw [Finset.sum_congr rfl hwc, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul,
      Nat.add_sub_cancel]
    have hΛne := hΛpos.ne'
    field_simp
  have hmix : ∀ t : ℝ, mixCdf (linRate a b) T k t - t = b * T ^ 2 / (2 * k * Λ) * (t ^ 2 - t) := by
    intro t
    unfold mixCdf
    calc ∑ j ∈ Finset.Icc 1 k, weight (linRate a b) T k j * subCdf (linRate a b) T k j t - t
        = ∑ j ∈ Finset.Icc 1 k, weight (linRate a b) T k j * subCdf (linRate a b) T k j t
          - (∑ j ∈ Finset.Icc 1 k, weight (linRate a b) T k j) * t := by rw [hsumw, one_mul]
      _ = ∑ j ∈ Finset.Icc 1 k, weight (linRate a b) T k j *
            (subCdf (linRate a b) T k j t - t) := by
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = ∑ j ∈ Finset.Icc 1 k, (weight (linRate a b) T k j * c j) * (t ^ 2 - t) :=
          Finset.sum_congr rfl (fun j hj => by rw [key j hj t]; ring)
      _ = b * T ^ 2 / (2 * k * Λ) * (t ^ 2 - t) := by rw [← Finset.sum_mul, hS]
  have hqmix := p9158_quad (mixCdf (linRate a b) T k) (b * T ^ 2 / (2 * k * Λ))
    (by positivity) hmix
  have hdegmix : degree (mixCdf (linRate a b) T k) = b * T ^ 2 / (2 * k * Λ) / 4 :=
    hqmix.csSup_eq
  have hqsub : ∀ j ∈ Finset.Icc 1 k,
      IsGreatest ((fun t => |subCdf (linRate a b) T k j t - t|) '' Set.Icc (0:ℝ) 1) (c j / 4) :=
    fun j hj => p9158_quad _ (c j) (hc0 j hj) (key j hj)
  have hdegsub : ∀ j ∈ Finset.Icc 1 k, degree (subCdf (linRate a b) T k j) = c j / 4 :=
    fun j hj => (hqsub j hj).csSup_eq
  have h3 : degree (mixCdf (linRate a b) T k) =
      ∑ j ∈ Finset.Icc 1 k,
        weight (linRate a b) T k j * degree (subCdf (linRate a b) T k j) := by
    rw [hdegmix, ← hS, Finset.sum_div]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [hdegsub j hj]
    ring
  refine ⟨?_, ?_, h3, ?_, ?_, ?_⟩
  · rw [hdegmix]; exact hqmix
  · intro j hj
    rw [hdegsub j hj]
    exact hqsub j hj
  · intro ha0
    rw [h3]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [hdegsub j hj]
    have hLpos : 0 < a + b * (((j:ℝ) - 1) * T / k) := by
      have := hL j hj
      linarith
    simp only [hcdef, hPdef, subSlope, linRate]
    exact p9158_alg4 _ b T k _ hkpos hT hLpos hb
  · intro ha0
    have hb0 : 0 < b := by
      rcases hab with h | h
      · linarith
      · exact h
    have hsplit := Finset.add_sum_Ioc_eq_sum_Icc
      (f := fun j => weight (linRate a b) T k j * degree (subCdf (linRate a b) T k j)) hk
    have hIcc2 : Finset.Icc 2 k = Finset.Ioc 1 k := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      omega
    rw [h3, ← hsplit, hIcc2]
    congr 1
    · rw [hdegsub 1 (Finset.mem_Icc.2 ⟨le_rfl, hk⟩)]
      simp only [hcdef, hPdef]
      have e : (((1:ℕ):ℝ) - 1) = 0 := by norm_num
      rw [e]
      exact p9158_alg1 _ a b T k ha0 hkpos hT hb0
    · refine Finset.sum_congr rfl (fun j hj => ?_)
      have hj' : j ∈ Finset.Icc 1 k := Finset.Ioc_subset_Icc_self hj
      rw [hdegsub j hj']
      have hj2 : (2:ℝ) ≤ j := by exact_mod_cast (Finset.mem_Ioc.1 hj).1
      simp only [hcdef, hPdef]
      exact p9158_alg5 _ a b T k _ ha0 hkpos hT hb0 (by linarith)
  · rw [hdegmix]
    apply le_of_eq
    have hΛne := hΛpos.ne'
    field_simp
    ring
