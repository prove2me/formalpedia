-- Prove2me | solution 1 for LightningChannels.SymmetricCosts.asymptotic_optimal_cost_and_collateral
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T23:45:58.287313+00:00
-- url     : https://prove2.me/submissions/c4629afa-c69c-4a87-9b39-7c5fd9c1bc6c

import Mathlib
import Definitions.Def_LightningChannels_SymmetricCosts_IsGlobalMin

set_option autoImplicit false

namespace LNChSR3

/-- `log (1 + c) < log (1 + u) + c / u` for `u, c > 0`. -/
lemma log_bound (u c : ℝ) (hu : 0 < u) (hc : 0 < c) :
    Real.log (1 + c) < Real.log (1 + u) + c / u := by
  have h1 : Real.log ((1 + c) / (1 + u)) ≤ (1 + c) / (1 + u) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by positivity) (by positivity)] at h1
  have h2 : (1 + c) / (1 + u) - 1 < c / u := by
    rw [div_sub_one (by positivity), div_lt_div_iff₀ (by positivity) hu]
    nlinarith
  linarith

lemma pow12 : ∀ n : ℕ, (12:ℝ) ^ n ≤ 6 * ((2 * n).factorial : ℝ) := by
  intro n
  induction n with
  | zero => norm_num
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · norm_num [Nat.factorial]
    · have hf : ((2 * (k+1)).factorial : ℝ) = (2*k+2) * (2*k+1) * ((2*k).factorial : ℝ) := by
        rw [show 2 * (k+1) = (2*k+1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
        push_cast; ring
      rw [hf, pow_succ]
      have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
      have hF : (0:ℝ) ≤ 6 * ((2*k).factorial : ℝ) := by positivity
      have h12 : (12:ℝ) ≤ (2*k+2)*(2*k+1) := by nlinarith
      have := mul_le_mul_of_nonneg_left h12 hF
      nlinarith

lemma cosh_upper (u : ℝ) (hu2 : u ^ 2 < 12) :
    Real.cosh u ≤ 72 / (12 - u ^ 2) - 5 := by
  have hx0 : 0 ≤ u ^ 2 / 12 := by positivity
  have hx1 : u ^ 2 / 12 < 1 := by rw [div_lt_one (by norm_num)]; exact hu2
  have hg : HasSum (fun n : ℕ => 6 * (u ^ 2 / 12) ^ n - (if n = 0 then (5:ℝ) else 0))
      (6 * (1 - u ^ 2 / 12)⁻¹ - 5) :=
    ((hasSum_geometric_of_lt_one hx0 hx1).mul_left 6).sub (hasSum_ite_eq 0 (5:ℝ))
  have hle : Real.cosh u ≤ 6 * (1 - u ^ 2 / 12)⁻¹ - 5 := by
    refine hasSum_le (fun n => ?_) (Real.hasSum_cosh u) hg
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num
    · have hn0 : n ≠ 0 := by omega
      simp only [hn0, if_false, sub_zero]
      have hF : (0:ℝ) < ((2 * n).factorial : ℝ) := by positivity
      have h12 : (0:ℝ) < 12 ^ n := by positivity
      rw [pow_mul, div_pow, show 6 * ((u ^ 2) ^ n / 12 ^ n) = (u ^ 2) ^ n * (6 / 12 ^ n) by ring,
        div_eq_mul_one_div ((u ^ 2) ^ n)]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [div_le_div_iff₀ hF h12]
      linarith [pow12 n]
  have h12 : (0:ℝ) < 12 - u ^ 2 := by linarith
  calc Real.cosh u ≤ 6 * (1 - u ^ 2 / 12)⁻¹ - 5 := hle
    _ = 72 / (12 - u ^ 2) - 5 := by
      congr 1
      rw [show (1:ℝ) - u ^ 2 / 12 = (12 - u ^ 2) / 12 by ring, inv_div]
      ring

lemma recip_lower (u : ℝ) (hu : 0 < u) :
    2 / u ^ 2 - 1 / 6 ≤ 2 / (Real.exp u + Real.exp (-u) - 2) := by
  have hc : 1 < Real.cosh u := Real.one_lt_cosh.mpr hu.ne'
  have hE : Real.exp u + Real.exp (-u) - 2 = 2 * (Real.cosh u - 1) := by
    rw [Real.cosh_eq]; ring
  rw [hE]
  have hK : 0 < Real.cosh u - 1 := by linarith
  have hu2 : 0 < u ^ 2 := by positivity
  rw [show 2 / (2 * (Real.cosh u - 1)) = 1 / (Real.cosh u - 1) by field_simp]
  by_cases h : u ^ 2 < 12
  · have h1 := cosh_upper u h
    have h12 : (0:ℝ) < 12 - u ^ 2 := by linarith
    have h2 : (Real.cosh u - 1) * (12 - u ^ 2) ≤ 6 * u ^ 2 := by
      have : Real.cosh u - 1 ≤ 6 * u ^ 2 / (12 - u ^ 2) := by
        have : 72 / (12 - u ^ 2) - 5 - 1 = 6 * u ^ 2 / (12 - u ^ 2) := by
          field_simp; ring
        linarith
      rwa [le_div_iff₀ h12] at this
    rw [show 2 / u ^ 2 - 1 / 6 = (12 - u ^ 2) / (6 * u ^ 2) by field_simp; ring,
      div_le_div_iff₀ (by positivity) hK]
    nlinarith
  · push_neg at h
    have : 2 / u ^ 2 ≤ 1 / 6 := by
      rw [div_le_div_iff₀ hu2 (by norm_num)]; linarith
    have : 0 < 1 / (Real.cosh u - 1) := by positivity
    linarith

lemma sq_le_cosh_sub (k : ℝ) (hk : 0 ≤ k) : k ^ 2 ≤ Real.exp k + Real.exp (-k) - 2 := by
  have h1 : k / 2 ≤ Real.sinh (k / 2) := Real.self_le_sinh_iff.mpr (by linarith)
  have h2 : Real.exp k + Real.exp (-k) - 2 = 4 * Real.sinh (k / 2) ^ 2 := by
    rw [Real.sinh_eq]
    have e1 : Real.exp k = Real.exp (k / 2) * Real.exp (k / 2) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (-k) = Real.exp (-(k / 2)) * Real.exp (-(k / 2)) := by
      rw [← Real.exp_add]; ring_nf
    have e3 : Real.exp (k / 2) * Real.exp (-(k / 2)) = 1 := by
      rw [← Real.exp_add]; simp
    rw [e1, e2]
    nlinarith [e3]
  rw [h2]
  nlinarith

theorem part1 (lam r B C : ℝ) (hlam : 0 < lam) (hr : 0 < r) (hB : 0 < B) :
    (∃ m : ℝ, 0 < m ∧ LNChannels.Exact.uniCost lam r B m < lam * C / r) →
        Real.log (1 + B * Real.log (1 + r / lam)) < C := by
  rintro ⟨m, hm, hc⟩
  unfold LNChannels.Exact.uniCost at hc
  have hq : (r + lam) / lam = 1 + r / lam := by field_simp; ring
  rw [hq] at hc
  have hrl : 0 < r / lam := div_pos hr hlam
  set a := Real.log (1 + r / lam) with ha
  have ha0 : 0 < a := Real.log_pos (by linarith)
  have hal : a < r / lam := by
    have := Real.log_lt_sub_one_of_pos (by linarith : (0:ℝ) < 1 + r / lam) (by linarith)
    linarith
  have hpow : (1 + r / lam) ^ m = Real.exp (a * m) := Real.rpow_def_of_pos (by linarith) m
  rw [hpow] at hc
  have hu0 : 0 < Real.exp (a * m) - 1 := by
    have ham : 0 < a * m := by positivity
    have := Real.add_one_lt_exp ham.ne'; linarith
  set u := Real.exp (a * m) - 1 with hu
  have h1u : 1 + u = Real.exp (a * m) := by rw [hu]; ring
  have hlog : Real.log (1 + u) = a * m := by rw [h1u, Real.log_exp]
  have hk := log_bound u (a * B) hu0 (by positivity)
  rw [hlog] at hk
  have hc' : a * m + a * B / u < a * (lam * C / r) := by
    have e : a * m + a * B / u = a * (m + B * u⁻¹) := by ring
    rw [e]; exact mul_lt_mul_of_pos_left hc ha0
  have hL : 0 < Real.log (1 + a * B) := Real.log_pos (by nlinarith)
  have hC : 0 < C := by
    by_contra h
    push_neg at h
    have : lam * C / r ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hlam.le h) hr.le
    nlinarith
  have hal' : a * lam < r := by rwa [lt_div_iff₀ hlam] at hal
  have hfin : a * (lam * C / r) < C := by
    rw [mul_div_assoc', div_lt_iff₀ hr]
    nlinarith [mul_lt_mul_of_pos_right hal' hC]
  rw [mul_comm B a]
  linarith

lemma key_X (P Q w : ℝ) (hP1 : 1 < P) (hQ1 : 1 < Q) (hw1 : 1 < w) (hw2 : w * w = P * Q) :
    2 / (w + w⁻¹ - 2) ≤ (P + Q) / ((P - 1) * (Q - 1)) := by
  have hσ : 2 * w ≤ P + Q := by
    by_contra h
    push_neg at h
    have h' : (P + Q) ^ 2 < (2 * w) ^ 2 := pow_lt_pow_left₀ h (by linarith) two_ne_zero
    nlinarith [sq_nonneg (P - Q)]
  have hw0 : 0 < w := by linarith
  have hden : w + w⁻¹ - 2 = (w - 1) ^ 2 / w := by field_simp; ring
  rw [hden, div_div_eq_mul_div,
    div_le_div_iff₀ (pow_pos (by linarith) 2) (mul_pos (by linarith) (by linarith))]
  have h3 : w * (P * Q) = w * (w * w) := by rw [hw2]
  nlinarith [mul_le_mul_of_nonneg_right hσ (by positivity : (0:ℝ) ≤ w ^ 2 + 1)]

open LNChannels.RateBounds in
lemma bicost_formula (lam r B l₁ l₂ E : ℝ) (hE1 : 1 < E) (h1 : 0 < l₁) (h2 : 0 < l₂)
    (hαp : LNChannels.Exact.alphaPlus lam lam r = E)
    (hαm : LNChannels.Exact.alphaMinus lam lam r = E⁻¹) :
    biCost lam lam r B l₁ l₂
      = (l₁ + l₂) + B * ((E ^ l₁ + E ^ l₂) / ((E ^ l₁ - 1) * (E ^ l₂ - 1))) := by
  have hE0 : 0 < E := by linarith
  have hP1 : 1 < E ^ l₁ := Real.one_lt_rpow hE1 h1
  have hQ1 : 1 < E ^ l₂ := Real.one_lt_rpow hE1 h2
  unfold biCost
  dsimp only
  rw [hαm, hαp, Real.inv_rpow hE0.le, Real.inv_rpow hE0.le, Real.rpow_add hE0]
  generalize E ^ l₁ = P at *
  generalize E ^ l₂ = Q at *
  have hP0 : 0 < P := by linarith
  have hQ0 : 0 < Q := by linarith
  have hPQ1 : 0 < P * Q - 1 := by nlinarith
  have hP1' : 0 < P - 1 := by linarith
  have hQ1' : 0 < Q - 1 := by linarith
  have hD : P⁻¹ * (1 - P * Q) - P * (1 - (P * Q)⁻¹) + P * Q - (P * Q)⁻¹
      = (P * Q - 1) * (P - 1) * (Q - 1) / (P * Q) := by
    field_simp; ring
  have hN : P⁻¹ * (1 - P * Q) - P * (1 - (P * Q)⁻¹) = -((P * Q - 1) * (P + Q)) / (P * Q) := by
    field_simp; ring
  have hDne : (P * Q - 1) * (P - 1) * (Q - 1) / (P * Q) ≠ 0 := by positivity
  have key : B * (P⁻¹ * (1 - P * Q) - P * (1 - (P * Q)⁻¹))
      / (P⁻¹ * (1 - P * Q) - P * (1 - (P * Q)⁻¹) + P * Q - (P * Q)⁻¹)
      = -(B * ((P + Q) / ((P - 1) * (Q - 1)))) := by
    rw [hD, div_eq_iff hDne, hN]
    field_simp
  rw [key]; ring

lemma amgm3 (A Y M : ℝ) (hA : 0 < A) (hM : 0 < M) (h : A ^ 2 * Y = M ^ 3) :
    3 * M ≤ 2 * A + Y := by
  have hid : A ^ 2 * (2 * A + Y - 3 * M) = (A - M) ^ 2 * (2 * A + M) := by
    linear_combination h
  have hnn : 0 ≤ A ^ 2 * (2 * A + Y - 3 * M) := by rw [hid]; positivity
  have := (mul_nonneg_iff_of_pos_left (by positivity : 0 < A ^ 2)).mp hnn
  linarith

set_option maxHeartbeats 1000000 in
open LNChannels.RateBounds in
theorem part2 (lam r B C l₁ l₂ : ℝ) (hlam : 0 < lam) (hr : 0 < r) (hB : 0 < B)
    (h1 : 0 < l₁) (h2 : 0 < l₂) (hcost : biCost lam lam r B l₁ l₂ < 2 * C * lam / r) :
    3 * (B * Real.log ((r + 2 * lam + √(r * (4 * lam + r))) / (2 * lam)) ^ 4 / 4) ^ (1 / 3 : ℝ)
      - B / 12 * Real.log ((r + 2 * lam + √(r * (4 * lam + r))) / (2 * lam)) ^ 2 < C := by
  obtain ⟨S, hSdef⟩ : ∃ S, S = √(r * (4 * lam + r)) := ⟨_, rfl⟩
  rw [← hSdef]
  have hS0 : 0 ≤ S := by rw [hSdef]; exact Real.sqrt_nonneg _
  have hS2 : S ^ 2 = r * (4 * lam + r) := by rw [hSdef]; exact Real.sq_sqrt (by positivity)
  have hSlt : S < r + 2 * lam := by
    have hsq : S ^ 2 < (r + 2 * lam) ^ 2 := by rw [hS2]; nlinarith [sq_pos_of_pos hlam]
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
  obtain ⟨E, hEdef⟩ : ∃ E, E = (r + 2 * lam + S) / (2 * lam) := ⟨_, rfl⟩
  rw [← hEdef]
  have hE1 : 1 < E := by rw [hEdef, lt_div_iff₀ (by positivity)]; linarith
  have hE0 : 0 < E := by linarith
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = Real.log E := ⟨_, rfl⟩
  rw [← hκdef]
  have hκ0 : 0 < κ := by rw [hκdef]; exact Real.log_pos hE1
  have hexpκ : Real.exp κ = E := by rw [hκdef]; exact Real.exp_log hE0
  have harg : (lam - lam) ^ 2 + r ^ 2 + 2 * r * (lam + lam) = r * (4 * lam + r) := by ring
  have hαp : LNChannels.Exact.alphaPlus lam lam r = E := by
    unfold LNChannels.Exact.alphaPlus
    rw [harg, ← hSdef, hEdef]; ring
  have hEinv : E⁻¹ = (2 * lam + r - S) / (2 * lam) := by
    rw [hEdef, inv_div, div_eq_div_iff (by linarith) (by positivity)]
    linear_combination hS2
  have hαm : LNChannels.Exact.alphaMinus lam lam r = E⁻¹ := by
    unfold LNChannels.Exact.alphaMinus
    rw [harg, ← hSdef, hEinv]; ring
  have hrl : r / lam = Real.exp κ + Real.exp (-κ) - 2 := by
    rw [Real.exp_neg, hexpκ, hEinv, hEdef]
    field_simp; ring
  have hcκ : κ ^ 2 / 2 ≤ r / (2 * lam) := by
    have := sq_le_cosh_sub κ hκ0.le
    rw [show r / (2 * lam) = (r / lam) / 2 by field_simp]
    linarith
  rw [bicost_formula lam r B l₁ l₂ E hE1 h1 h2 hαp hαm] at hcost
  have hP1 : 1 < E ^ l₁ := Real.one_lt_rpow hE1 h1
  have hQ1 : 1 < E ^ l₂ := Real.one_lt_rpow hE1 h2
  obtain ⟨s, hs⟩ : ∃ s, s = l₁ + l₂ := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; positivity
  obtain ⟨u, hu⟩ : ∃ u, u = κ * s / 2 := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; positivity
  have hwE : E ^ (s / 2) = Real.exp u := by
    rw [Real.rpow_def_of_pos hE0, ← hκdef, hu]; ring_nf
  have hw1 : 1 < Real.exp u := Real.one_lt_exp_iff.mpr hu0
  have hw2 : Real.exp u * Real.exp u = E ^ l₁ * E ^ l₂ := by
    rw [← hwE, ← Real.rpow_add hE0, ← Real.rpow_add hE0, hs]; ring_nf
  have hX := key_X (E ^ l₁) (E ^ l₂) (Real.exp u) hP1 hQ1 hw1 hw2
  rw [← Real.exp_neg] at hX
  generalize (E ^ l₁ + E ^ l₂) / ((E ^ l₁ - 1) * (E ^ l₂ - 1)) = X at hX hcost
  have hY := recip_lower u hu0
  have hYpos : 0 < 2 / (Real.exp u + Real.exp (-u) - 2) := by
    have : 0 < Real.exp u + Real.exp (-u) - 2 := by
      have := sq_le_cosh_sub u hu0.le; nlinarith
    positivity
  generalize 2 / (Real.exp u + Real.exp (-u) - 2) = Y at hX hY hYpos
  rw [← hs] at hcost
  obtain ⟨c, hc⟩ : ∃ c, c = r / (2 * lam) := ⟨_, rfl⟩
  rw [← hc] at hcκ
  have hc0 : 0 < c := by rw [hc]; positivity
  have hmain : c * (s + B * X) < C := by
    have := mul_lt_mul_of_pos_left hcost hc0
    have e : c * (2 * C * lam / r) = C := by rw [hc]; field_simp
    linarith
  have hlow1 : κ ^ 2 / 2 * s ≤ c * s := mul_le_mul_of_nonneg_right hcκ hs0.le
  have a1 : κ ^ 2 / 2 * B * (2 / u ^ 2 - 1 / 6) ≤ κ ^ 2 / 2 * B * Y :=
    mul_le_mul_of_nonneg_left hY (by positivity)
  have a2 : κ ^ 2 / 2 * B * Y ≤ c * B * Y :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcκ hB.le) hYpos.le
  have a3 : c * B * Y ≤ c * B * X :=
    mul_le_mul_of_nonneg_left hX (by positivity)
  have hκu : κ ^ 2 / 2 * B * (2 / u ^ 2 - 1 / 6) = 4 * B / s ^ 2 - B / 12 * κ ^ 2 := by
    rw [hu]; field_simp; ring
  obtain ⟨M, hM⟩ : ∃ M, M = (B * κ ^ 4 / 4) ^ (1 / 3 : ℝ) := ⟨_, rfl⟩
  rw [← hM]
  have hM0 : 0 < M := by rw [hM]; positivity
  have hM3 : M ^ 3 = B * κ ^ 4 / 4 := by
    rw [hM, show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.rpow_inv_natCast_pow (by positivity) (by norm_num)
  have hAY : (κ ^ 2 * s / 4) ^ 2 * (4 * B / s ^ 2) = M ^ 3 := by
    rw [hM3]; field_simp
  have ham := amgm3 (κ ^ 2 * s / 4) (4 * B / s ^ 2) M (by positivity) hM0 hAY
  have expand : c * (s + B * X) = c * s + c * B * X := by ring
  rw [expand] at hmain
  linarith


lemma cosh_lower (u : ℝ) : u ^ 2 + u ^ 4 / 12 ≤ Real.exp u + Real.exp (-u) - 2 := by
  have h := Real.hasSum_cosh u
  have hs := sum_le_hasSum (Finset.range 3)
    (fun n _ => div_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg u) n) (Nat.cast_nonneg _)) h
  norm_num [Finset.sum_range_succ, Nat.factorial] at hs
  rw [Real.cosh_eq] at hs
  linarith

lemma recip_upper (u : ℝ) (hu : 0 < u) :
    2 / (Real.exp u + Real.exp (-u) - 2) ≤ 2 / u ^ 2 - 1 / 6 + u ^ 2 / 72 := by
  have h := cosh_lower u
  have hpos : 0 < u ^ 2 + u ^ 4 / 12 := by positivity
  have hu2 : u ^ 2 ≠ 0 := by positivity
  have hd : 2 / u ^ 2 - 1 / 6 + u ^ 2 / 72 - 2 / (u ^ 2 + u ^ 4 / 12)
      = u ^ 4 / (72 * (12 + u ^ 2)) := by
    field_simp
    ring
  have hnn : 0 ≤ u ^ 4 / (72 * (12 + u ^ 2)) := by positivity
  have h2 : 2 / (Real.exp u + Real.exp (-u) - 2) ≤ 2 / (u ^ 2 + u ^ 4 / 12) :=
    div_le_div_of_nonneg_left (by norm_num) hpos h
  linarith

lemma kappa_facts (lam r : ℝ) (hlam : 0 < lam) (hr : 0 < r) (hr12 : r < 12 * lam) :
    ∃ E κ : ℝ, 1 < E ∧ κ = Real.log E ∧ 0 < κ ∧
      LNChannels.Exact.alphaPlus lam lam r = E ∧ LNChannels.Exact.alphaMinus lam lam r = E⁻¹ ∧
      κ = Real.log ((r + 2 * lam + √(r * (4 * lam + r))) / (2 * lam)) ∧
      κ ^ 2 ≤ r / lam ∧ 1 / κ ^ 2 ≤ lam / r + 1 / 12 := by
  obtain ⟨S, hSdef⟩ : ∃ S, S = √(r * (4 * lam + r)) := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hSdef]; exact Real.sqrt_nonneg _
  have hS2 : S ^ 2 = r * (4 * lam + r) := by rw [hSdef]; exact Real.sq_sqrt (by positivity)
  have hSlt : S < r + 2 * lam := by
    have hsq : S ^ 2 < (r + 2 * lam) ^ 2 := by rw [hS2]; nlinarith [sq_pos_of_pos hlam]
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
  obtain ⟨E, hEdef⟩ : ∃ E, E = (r + 2 * lam + S) / (2 * lam) := ⟨_, rfl⟩
  have hE1 : 1 < E := by rw [hEdef, lt_div_iff₀ (by positivity)]; linarith
  have hE0 : 0 < E := by linarith
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = Real.log E := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκdef]; exact Real.log_pos hE1
  have hexpκ : Real.exp κ = E := by rw [hκdef]; exact Real.exp_log hE0
  have harg : (lam - lam) ^ 2 + r ^ 2 + 2 * r * (lam + lam) = r * (4 * lam + r) := by ring
  have hαp : LNChannels.Exact.alphaPlus lam lam r = E := by
    unfold LNChannels.Exact.alphaPlus
    rw [harg, ← hSdef, hEdef]; ring
  have hEinv : E⁻¹ = (2 * lam + r - S) / (2 * lam) := by
    rw [hEdef, inv_div, div_eq_div_iff (by linarith) (by positivity)]
    linear_combination hS2
  have hαm : LNChannels.Exact.alphaMinus lam lam r = E⁻¹ := by
    unfold LNChannels.Exact.alphaMinus
    rw [harg, ← hSdef, hEinv]; ring
  have hrl : r / lam = Real.exp κ + Real.exp (-κ) - 2 := by
    rw [Real.exp_neg, hexpκ, hEinv, hEdef]
    field_simp; ring
  have hk2 : κ ^ 2 ≤ r / lam := by
    have := sq_le_cosh_sub κ hκ0.le
    linarith
  have hrl12 : r / lam < 12 := by rw [div_lt_iff₀ hlam]; linarith
  have hk12 : κ ^ 2 < 12 := by linarith
  have hcu := cosh_upper κ hk12
  rw [Real.cosh_eq] at hcu
  have h12 : 0 < 12 - κ ^ 2 := by linarith
  have h12' : 12 - κ ^ 2 ≠ 0 := h12.ne'
  have hq : r / lam ≤ 2 * (72 / (12 - κ ^ 2)) - 12 := by linarith
  have he : 2 * (72 / (12 - κ ^ 2)) - 12 = 12 * κ ^ 2 / (12 - κ ^ 2) := by field_simp; ring
  rw [he, le_div_iff₀ h12] at hq
  have hrl0 : 0 < r / lam := by positivity
  have hk1 : 1 / κ ^ 2 ≤ lam / r + 1 / 12 := by
    rw [div_le_iff₀ (by positivity)]
    have e2 : (lam / r + 1 / 12) * κ ^ 2 = κ ^ 2 * (12 + r / lam) / (12 * (r / lam)) := by
      field_simp
    rw [e2, le_div_iff₀ (by positivity)]
    nlinarith
  refine ⟨E, κ, hE1, hκdef, hκ0, hαp, hαm, ?_, hk2, hk1⟩
  rw [hκdef, hEdef, hSdef]

open LNChannels.RateBounds in
lemma part2' (lam r B l₁ l₂ : ℝ) (hlam : 0 < lam) (hr : 0 < r) (hB : 0 < B)
    (h1 : 0 < l₁) (h2 : 0 < l₂) :
    3 * (B * Real.log ((r + 2 * lam + √(r * (4 * lam + r))) / (2 * lam)) ^ 4 / 4) ^ (1 / 3 : ℝ)
      - B / 12 * Real.log ((r + 2 * lam + √(r * (4 * lam + r))) / (2 * lam)) ^ 2
      ≤ r / (2 * lam) * biCost lam lam r B l₁ l₂ := by
  by_contra hcon
  push_neg at hcon
  refine lt_irrefl _ (part2 lam r B _ l₁ l₂ hlam hr hB h1 h2 ?_)
  rw [lt_div_iff₀ hr]
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)] at hcon
  nlinarith

open LNChannels.RateBounds in
lemma lower_bd (lam r B l₁ l₂ T ρ : ℝ) (hlam : 0 < lam) (hr : 0 < r) (hB : 0 < B)
    (h1 : 0 < l₁) (h2 : 0 < l₂) (hr12 : r < 12 * lam) (hρ : 0 < ρ) (hρ3 : ρ ^ 3 = r)
    (hT : 0 < T) (hT3 : T ^ 3 = 2 * B * lam) :
    3 * T / ρ - B / 6 - T * ρ ^ 2 / (4 * lam) ≤ biCost lam lam r B l₁ l₂ := by
  obtain ⟨E, κ, hE1, hκE, hκ0, hαp, hαm, hκdef, hk2, hk1⟩ := kappa_facts lam r hlam hr hr12
  have hLB := part2' lam r B l₁ l₂ hlam hr hB h1 h2
  rw [← hκdef] at hLB
  generalize biCost lam lam r B l₁ l₂ = bc at hLB ⊢
  obtain ⟨M, hM⟩ : ∃ M, M = (B * κ ^ 4 / 4) ^ (1 / 3 : ℝ) := ⟨_, rfl⟩
  rw [← hM] at hLB
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hM3 : M ^ 3 = B * κ ^ 4 / 4 := by
    rw [hM, show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.rpow_inv_natCast_pow (by positivity) (by norm_num)
  subst hρ3
  have hρ3p : 0 < ρ ^ 3 := by positivity
  obtain ⟨q, hq⟩ : ∃ q, q = lam * κ ^ 2 / ρ ^ 3 := ⟨_, rfl⟩
  have hq1 : q ≤ 1 := by
    rw [hq, div_le_one hρ3p]
    rw [le_div_iff₀ hlam] at hk2
    linarith
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  obtain ⟨ε, hε⟩ : ∃ ε, ε = ρ ^ 3 / (12 * lam) := ⟨_, rfl⟩
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  have hε1 : ε < 1 := by rw [hε, div_lt_one (by positivity)]; linarith
  have hqe : 1 ≤ q * (1 + ε) := by
    have hk1' := hk1
    rw [div_le_iff₀ (by positivity)] at hk1'
    have : q * (1 + ε) = (lam / ρ ^ 3 + 1 / 12) * κ ^ 2 := by
      rw [hq, hε]
      field_simp
      try ring
    linarith
  have hqe2 : 1 - ε ≤ q := by
    nlinarith [mul_le_mul_of_nonneg_right hqe (by linarith : (0:ℝ) ≤ 1 - ε),
      mul_nonneg hq0 (sq_nonneg ε)]
  have hcube : (1 - ε) ^ 3 ≤ q ^ 2 := by
    have a : (1 - ε) ^ 3 ≤ (1 - ε) ^ 2 :=
      pow_le_pow_of_le_one (by linarith) (by linarith) (by norm_num)
    have b : (1 - ε) ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (by linarith) hqe2 2
    linarith
  have hx3 : (2 * lam * M / ρ ^ 3) ^ 3 = 2 * B * lam / ρ ^ 3 * q ^ 2 := by
    have : (2 * lam * M / ρ ^ 3) ^ 3 = 8 * lam ^ 3 * M ^ 3 / ρ ^ 9 := by ring
    rw [this, hM3, hq]
    field_simp
    ring
  have hy3 : (T / ρ * (1 - ε)) ^ 3 = 2 * B * lam / ρ ^ 3 * (1 - ε) ^ 3 := by
    rw [mul_pow, div_pow, hT3]
  have hxy : T / ρ * (1 - ε) ≤ 2 * lam * M / ρ ^ 3 := by
    have hy0 : 0 ≤ T / ρ * (1 - ε) := by
      have : 0 ≤ 1 - ε := by linarith
      positivity
    rw [← pow_le_pow_iff_left₀ hy0 (by positivity) (by norm_num : (3:ℕ) ≠ 0), hx3, hy3]
    exact mul_le_mul_of_nonneg_left hcube (by positivity)
  have hbc : 2 * lam / ρ ^ 3 * (3 * M - B / 12 * κ ^ 2) ≤ bc := by
    have := mul_le_mul_of_nonneg_left hLB (by positivity : (0:ℝ) ≤ 2 * lam / ρ ^ 3)
    have e : 2 * lam / ρ ^ 3 * (ρ ^ 3 / (2 * lam) * bc) = bc := by field_simp
    linarith
  have hexp : 2 * lam / ρ ^ 3 * (3 * M - B / 12 * κ ^ 2)
      = 3 * (2 * lam * M / ρ ^ 3) - B / 6 * q := by
    rw [hq]; field_simp; ring
  have hy : 3 * (T / ρ * (1 - ε)) = 3 * T / ρ - T * ρ ^ 2 / (4 * lam) := by
    rw [hε]; field_simp; ring
  have hBq : B / 6 * q ≤ B / 6 := by nlinarith
  linarith

open LNChannels.RateBounds in
lemma upper_l (lam r B l E κ : ℝ) (hlam : 0 < lam) (hr : 0 < r) (hB : 0 < B) (hl : 0 < l)
    (hE1 : 1 < E) (hκ : κ = Real.log E)
    (hαp : LNChannels.Exact.alphaPlus lam lam r = E)
    (hαm : LNChannels.Exact.alphaMinus lam lam r = E⁻¹)
    (hk2 : κ ^ 2 ≤ r / lam) (hk1 : 1 / κ ^ 2 ≤ lam / r + 1 / 12) (hκ0 : 0 < κ) :
    biCost lam lam r B l l
      ≤ 2 * l + B * (2 * (lam / r + 1 / 12) / l ^ 2) - B / 6 + B * (r / lam * l ^ 2 / 72) := by
  rw [bicost_formula lam r B l l E hE1 hl hl hαp hαm]
  have hE0 : 0 < E := by linarith
  have hP : E ^ l = Real.exp (κ * l) := by rw [Real.rpow_def_of_pos hE0, hκ]
  rw [hP]
  obtain ⟨u, hu⟩ : ∃ u, u = κ * l := ⟨_, rfl⟩
  rw [← hu]
  have hu0 : 0 < u := by rw [hu]; positivity
  have hY := recip_upper u hu0
  have hX : (Real.exp u + Real.exp u) / ((Real.exp u - 1) * (Real.exp u - 1))
      = 2 / (Real.exp u + Real.exp (-u) - 2) := by
    have h1 : 1 < Real.exp u := Real.one_lt_exp_iff.mpr hu0
    rw [Real.exp_neg]
    generalize Real.exp u = P at *
    have hP0 : P ≠ 0 := by positivity
    have hden : P + P⁻¹ - 2 = (P - 1) ^ 2 / P := by field_simp; ring
    have hP1 : P - 1 ≠ 0 := by linarith
    rw [hden]
    field_simp
    ring
  rw [hX]
  have h2u : 2 / u ^ 2 ≤ 2 * (lam / r + 1 / 12) / l ^ 2 := by
    have e : 2 / u ^ 2 = 2 * (1 / κ ^ 2) / l ^ 2 := by rw [hu]; field_simp
    rw [e]
    gcongr
  have hu2 : u ^ 2 / 72 ≤ r / lam * l ^ 2 / 72 := by
    have e : u ^ 2 / 72 = κ ^ 2 * l ^ 2 / 72 := by rw [hu]; ring
    rw [e]
    gcongr
  have hYb := mul_le_mul_of_nonneg_left hY hB.le
  have hb1 := mul_le_mul_of_nonneg_left h2u hB.le
  have hb2 := mul_le_mul_of_nonneg_left hu2 hB.le
  have hd : B * (2 / u ^ 2 - 1 / 6 + u ^ 2 / 72) = B * (2 / u ^ 2) - B / 6 + B * (u ^ 2 / 72) := by ring
  linarith

open LNChannels.RateBounds in
lemma upper_bd (lam r B T ρ : ℝ) (hlam : 0 < lam) (hr : 0 < r) (hB : 0 < B)
    (hr12 : r < 12 * lam) (hρ : 0 < ρ) (hρ3 : ρ ^ 3 = r)
    (hT : 0 < T) (hT3 : T ^ 3 = 2 * B * lam) :
    biCost lam lam r B (T / ρ) (T / ρ)
      ≤ 3 * T / ρ - B / 6 + B * ρ ^ 2 / (6 * T ^ 2) + B * T ^ 2 * ρ / (72 * lam) := by
  obtain ⟨E, κ, hE1, hκE, hκ0, hαp, hαm, -, hk2, hk1⟩ := kappa_facts lam r hlam hr hr12
  have h := upper_l lam r B (T / ρ) E κ hlam hr hB (by positivity) hE1 hκE hαp hαm hk2 hk1 hκ0
  refine h.trans (le_of_eq ?_)
  have hBe : B = T ^ 3 / (2 * lam) := by field_simp; linarith
  subst hρ3
  rw [hBe]
  field_simp
  ring

end LNChSR3

namespace LNChAOC

lemma tangent (x y : ℝ) (hx : 1 < x) (hy : 1 < y) :
    0 ≤ 1 - y / x + (y - 1) ^ 3 / (y * (y + 1)) * (x / (x - 1) ^ 2 - y / (y - 1) ^ 2) := by
  have hx0 : x ≠ 0 := by positivity
  have hy0 : y ≠ 0 := by positivity
  have hx1 : x - 1 ≠ 0 := by linarith
  have hy1 : y - 1 ≠ 0 := by linarith
  have hy2 : y + 1 ≠ 0 := by positivity
  have key : 1 - y / x + (y - 1) ^ 3 / (y * (y + 1)) * (x / (x - 1) ^ 2 - y / (y - 1) ^ 2)
      = (x - y) ^ 2 * (2 * x * y - y - 1) / (x * (x - 1) ^ 2 * y * (y + 1)) := by
    field_simp
    ring
  rw [key]
  apply div_nonneg
  · apply mul_nonneg (sq_nonneg _)
    nlinarith [mul_pos (sub_pos.mpr hx) (sub_pos.mpr hy)]
  · have : 0 < x - 1 := by linarith
    positivity

lemma root_exists (c : ℝ) (hc : 0 < c) : ∃ y : ℝ, 1 < y ∧ (y - 1) ^ 3 = c * (y * (y + 1)) := by
  have hcont : ContinuousOn (fun y : ℝ => (y - 1) ^ 3 - c * (y * (y + 1))) (Set.Icc 1 (3 * c + 3)) := by
    fun_prop
  have hX : (3 * c + 3 - 1) ^ 3 - c * ((3 * c + 3) * ((3 * c + 3) + 1))
      = 18 * c ^ 3 + 33 * c ^ 2 + 24 * c + 8 := by ring
  have h0 : (0:ℝ) ∈ Set.Icc ((fun y : ℝ => (y - 1) ^ 3 - c * (y * (y + 1))) 1)
      ((fun y : ℝ => (y - 1) ^ 3 - c * (y * (y + 1))) (3 * c + 3)) := by
    simp only [Set.mem_Icc]
    constructor
    · nlinarith
    · rw [hX]; positivity
  obtain ⟨y, hyI, hy⟩ := intermediate_value_Icc (by linarith) hcont h0
  simp only at hy
  refine ⟨y, ?_, by linarith⟩
  rcases eq_or_lt_of_le hyI.1 with h | h
  · subst h
    norm_num at hy
    linarith
  · exact h

lemma kappa_basic (lam r : ℝ) (hlam : 0 < lam) (hr : 0 < r) :
    ∃ E κ : ℝ, 1 < E ∧ κ = Real.log E ∧ 0 < κ ∧
      LNChannels.Exact.alphaPlus lam lam r = E ∧ LNChannels.Exact.alphaMinus lam lam r = E⁻¹ := by
  obtain ⟨S, hSdef⟩ : ∃ S, S = √(r * (4 * lam + r)) := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hSdef]; exact Real.sqrt_nonneg _
  have hS2 : S ^ 2 = r * (4 * lam + r) := by rw [hSdef]; exact Real.sq_sqrt (by positivity)
  have hSlt : S < r + 2 * lam := by
    have hsq : S ^ 2 < (r + 2 * lam) ^ 2 := by rw [hS2]; nlinarith [sq_pos_of_pos hlam]
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
  obtain ⟨E, hEdef⟩ : ∃ E, E = (r + 2 * lam + S) / (2 * lam) := ⟨_, rfl⟩
  have hE1 : 1 < E := by rw [hEdef, lt_div_iff₀ (by positivity)]; linarith
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = Real.log E := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκdef]; exact Real.log_pos hE1
  have harg : (lam - lam) ^ 2 + r ^ 2 + 2 * r * (lam + lam) = r * (4 * lam + r) := by ring
  have hαp : LNChannels.Exact.alphaPlus lam lam r = E := by
    unfold LNChannels.Exact.alphaPlus
    rw [harg, ← hSdef, hEdef]; ring
  have hEinv : E⁻¹ = (2 * lam + r - S) / (2 * lam) := by
    rw [hEdef, inv_div, div_eq_div_iff (by linarith) (by positivity)]
    linear_combination hS2
  have hαm : LNChannels.Exact.alphaMinus lam lam r = E⁻¹ := by
    unfold LNChannels.Exact.alphaMinus
    rw [harg, ← hSdef, hEinv]; ring
  exact ⟨E, κ, hE1, hκdef, hκ0, hαp, hαm⟩

lemma diag_min (κ B y l s : ℝ) (hκ : 0 < κ) (hy : 1 < y)
    (hroot : (y - 1) ^ 3 = B * κ * (y * (y + 1))) (hl : Real.exp (κ * l) = y) (hs : 0 < s) :
    (l + l) + B * ((y + y) / ((y - 1) * (y - 1)))
      ≤ (s + s) + B * ((Real.exp (κ * s) + Real.exp (κ * s))
          / ((Real.exp (κ * s) - 1) * (Real.exp (κ * s) - 1))) := by
  have hM1 : 1 < Real.exp (κ * s) := Real.one_lt_exp_iff.mpr (by positivity)
  obtain ⟨M, hM⟩ : ∃ M, M = Real.exp (κ * s) := ⟨_, rfl⟩
  rw [← hM] at hM1 ⊢
  have hy0 : 0 < y := by linarith
  have hM0 : 0 < M := by linarith
  have hlog : κ * s - κ * l = Real.log (M / y) := by
    rw [Real.log_div hM0.ne' hy0.ne', hM, ← hl, Real.log_exp, Real.log_exp]
  have hlb : 1 - y / M ≤ κ * s - κ * l := by
    rw [hlog]
    have := Real.one_sub_inv_le_log_of_pos (div_pos hM0 hy0)
    rwa [inv_div] at this
  have hc : (y - 1) ^ 3 / (y * (y + 1)) = B * κ := by
    rw [div_eq_iff (by positivity), hroot]
  have ht := tangent M y hM1 hy
  rw [hc] at ht
  have e1 : (y + y) / ((y - 1) * (y - 1)) = 2 * (y / (y - 1) ^ 2) := by ring
  have e2 : (M + M) / ((M - 1) * (M - 1)) = 2 * (M / (M - 1) ^ 2) := by ring
  rw [e1, e2]
  have key : 0 ≤ κ * ((s - l) + B * (M / (M - 1) ^ 2 - y / (y - 1) ^ 2)) := by
    have e3 : κ * ((s - l) + B * (M / (M - 1) ^ 2 - y / (y - 1) ^ 2))
        = (κ * s - κ * l) + B * κ * (M / (M - 1) ^ 2 - y / (y - 1) ^ 2) := by ring
    rw [e3]; linarith
  have key2 : 0 ≤ (s - l) + B * (M / (M - 1) ^ 2 - y / (y - 1) ^ 2) := by
    by_contra hneg
    push_neg at hneg
    have := mul_neg_of_pos_of_neg hκ hneg
    linarith
  linarith

open LNChannels.RateBounds in
lemma exists_min (lam B r : ℝ) (hlam : 0 < lam) (hB : 0 < B) (hr : 0 < r) :
    ∃ l : ℝ, 0 < l ∧ (∀ u v : ℝ, 0 < u → 0 < v → biCost lam lam r B l l ≤ biCost lam lam r B u v) ∧
      ∀ E : ℝ, LNChannels.Exact.alphaPlus lam lam r = E →
        (Real.exp (Real.log E * l) - 1) ^ 3
          = B * Real.log E * (Real.exp (Real.log E * l) * (Real.exp (Real.log E * l) + 1)) := by
  obtain ⟨E, κ, hE1, hκE, hκ0, hαp, hαm⟩ := kappa_basic lam r hlam hr
  obtain ⟨y, hy1, hroot⟩ := root_exists (B * κ) (by positivity)
  have hy0 : 0 < y := by linarith
  refine ⟨Real.log y / κ, div_pos (Real.log_pos hy1) hκ0, ?_, ?_⟩
  · have hexp : Real.exp (κ * (Real.log y / κ)) = y := by
      rw [mul_div_cancel₀ _ hκ0.ne', Real.exp_log hy0]
    have hE0 : 0 < E := by linarith
    have hrp : ∀ s : ℝ, E ^ s = Real.exp (κ * s) := fun s => by rw [Real.rpow_def_of_pos hE0, hκE]
    have hl0 : 0 < Real.log y / κ := div_pos (Real.log_pos hy1) hκ0
    intro u v hu hv
    have huv : 0 < (u + v) / 2 := by positivity
    -- diagonal reduction
    have hdiag : biCost lam lam r B ((u + v) / 2) ((u + v) / 2) ≤ biCost lam lam r B u v := by
      rw [LNChSR3.bicost_formula lam r B _ _ E hE1 huv huv hαp hαm,
        LNChSR3.bicost_formula lam r B u v E hE1 hu hv hαp hαm]
      have hw : E ^ ((u + v) / 2) * E ^ ((u + v) / 2) = E ^ u * E ^ v := by
        rw [← Real.rpow_add hE0, ← Real.rpow_add hE0]; congr 1; ring
      have hw1 : 1 < E ^ ((u + v) / 2) := Real.one_lt_rpow hE1 huv
      have hK := LNChSR3.key_X (E ^ u) (E ^ v) (E ^ ((u + v) / 2))
        (Real.one_lt_rpow hE1 hu) (Real.one_lt_rpow hE1 hv) hw1 hw
      generalize E ^ ((u + v) / 2) = w at hw1 hK ⊢
      have hw0 : 0 < w := by linarith
      have hX : (w + w) / ((w - 1) * (w - 1)) = 2 / (w + w⁻¹ - 2) := by
        have hden : w + w⁻¹ - 2 = (w - 1) ^ 2 / w := by field_simp; ring
        have hw1' : w - 1 ≠ 0 := by linarith
        rw [hden]
        field_simp
        ring
      rw [hX]
      have hB' := mul_le_mul_of_nonneg_left hK hB.le
      linarith
    refine le_trans ?_ hdiag
    rw [LNChSR3.bicost_formula lam r B _ _ E hE1 hl0 hl0 hαp hαm,
      LNChSR3.bicost_formula lam r B _ _ E hE1 huv huv hαp hαm, hrp, hrp, hexp]
    exact diag_min κ B y _ _ hκ0 hy1 hroot hexp huv
  · intro E' hE'
    rw [hαp] at hE'
    subst hE'
    have hk : κ * (Real.log y / κ) = Real.log y := by field_simp
    rw [← hκE, hk, Real.exp_log hy0, hroot]

lemma D_eq (y c : ℝ) (hy : 1 < y) (h : (y - 1) ^ 3 = c * (y * (y + 1))) :
    c ^ 2 * (y + y⁻¹ - 2 + 4) = (y + y⁻¹ - 2) ^ 3 := by
  have hy0 : 0 < y := by linarith
  have e1 : y + y⁻¹ - 2 = (y - 1) ^ 2 / y := by field_simp; ring
  have e2 : y + y⁻¹ - 2 + 4 = (y + 1) ^ 2 / y := by field_simp; ring
  rw [e2, e1, div_pow, mul_div_assoc', div_eq_div_iff (by positivity) (by positivity)]
  have e3 : ((y - 1) ^ 2) ^ 3 = ((y - 1) ^ 3) ^ 2 := by ring
  rw [e3, h]
  ring

lemma u_upper (u c D : ℝ) (hu : 0 < u) (hc : 0 < c) (hD : u ^ 2 + u ^ 4 / 12 ≤ D)
    (h : c ^ 2 * (D + 4) = D ^ 3) : u ^ 3 ≤ 2 * c := by
  have hu4 : 0 ≤ u ^ 4 / 12 := by positivity
  have hDt : u ^ 2 ≤ D := by linarith
  have hD0 : 0 < D := lt_of_lt_of_le (by positivity) hDt
  have key : 4 * D ^ 3 - (u ^ 2) ^ 3 * (D + 4)
      = 4 * (D - u ^ 2) ^ 3 + D * u ^ 2 * (12 * D - 12 * u ^ 2 - (u ^ 2) ^ 2) := by ring
  have h1 : 0 ≤ 4 * (D - u ^ 2) ^ 3 := by
    have := sub_nonneg.mpr hDt
    positivity
  have h2 : 0 ≤ D * u ^ 2 * (12 * D - 12 * u ^ 2 - (u ^ 2) ^ 2) := by
    apply mul_nonneg (by positivity)
    have : (u ^ 2) ^ 2 = u ^ 4 := by ring
    rw [this]; linarith
  have hD4 : 0 < D + 4 := by linarith
  have h3 : (u ^ 2) ^ 3 * (D + 4) ≤ (4 * c ^ 2) * (D + 4) := by
    have : (4 * c ^ 2) * (D + 4) = 4 * D ^ 3 := by rw [mul_assoc, h]
    rw [this]; linarith
  have h4 : (u ^ 2) ^ 3 ≤ 4 * c ^ 2 := le_of_mul_le_mul_right h3 hD4
  by_contra hcon
  push_neg at hcon
  have h5 := mul_lt_mul'' hcon hcon (by positivity) (by positivity)
  have e : u ^ 3 * u ^ 3 = (u ^ 2) ^ 3 := by ring
  rw [e] at h5
  nlinarith

lemma u_lower (t c D : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (hc : 0 < c) (hD : 0 < D)
    (hDu : D * (12 - t) ≤ 12 * t) (h : c ^ 2 * (D + 4) = D ^ 3) :
    4 * c ^ 2 ≤ t ^ 3 + c ^ 2 * t ^ 2 / 12 := by
  have hw : 0 < 12 - t := by linarith
  obtain ⟨X, hX⟩ : ∃ X, X = D * (12 - t) := ⟨_, rfl⟩
  have hX0 : 0 < X := by rw [hX]; positivity
  have hX12 : X ≤ 12 * t := by rw [hX]; exact hDu
  have hF : X ^ 3 * (t + 6) ≤ 216 * t ^ 3 * X + 864 * t ^ 3 * (12 - t) := by
    have e : 216 * t ^ 3 * X + 864 * t ^ 3 * (12 - t) - X ^ 3 * (t + 6)
        = (12 * t - X) * ((t + 6) * (X ^ 2 + 12 * t * X + 144 * t ^ 2) - 216 * t ^ 3) := by ring
    have h1 : 0 ≤ 12 * t - X := by linarith
    have h2 : 0 ≤ (t + 6) * (X ^ 2 + 12 * t * X + 144 * t ^ 2) - 216 * t ^ 3 := by
      have e2 : (t + 6) * (X ^ 2 + 12 * t * X + 144 * t ^ 2) - 216 * t ^ 3
          = t * X ^ 2 + 12 * t ^ 2 * X + 6 * X ^ 2 + 72 * t * X + 72 * t ^ 2 * (12 - t) := by ring
      rw [e2]; positivity
    nlinarith [mul_nonneg h1 h2]
  have h3 : D ^ 3 * ((t + 6) * (12 - t) ^ 2) ≤ 216 * t ^ 3 * (D + 4) := by
    have e : X ^ 3 * (t + 6) = (12 - t) * (D ^ 3 * ((t + 6) * (12 - t) ^ 2)) := by rw [hX]; ring
    have e2 : 216 * t ^ 3 * X + 864 * t ^ 3 * (12 - t) = (12 - t) * (216 * t ^ 3 * (D + 4)) := by
      rw [hX]; ring
    rw [e, e2] at hF
    exact le_of_mul_le_mul_left hF hw
  rw [← h] at h3
  have h4 : c ^ 2 * ((t + 6) * (12 - t) ^ 2) ≤ 216 * t ^ 3 := by
    have e : c ^ 2 * (D + 4) * ((t + 6) * (12 - t) ^ 2) = (D + 4) * (c ^ 2 * ((t + 6) * (12 - t) ^ 2)) := by
      ring
    have e2 : 216 * t ^ 3 * (D + 4) = (D + 4) * (216 * t ^ 3) := by ring
    rw [e, e2] at h3
    exact le_of_mul_le_mul_left h3 (by linarith)
  have h5 : c ^ 2 * ((t + 6) * (12 - t) ^ 2) = 864 * c ^ 2 - 18 * (c ^ 2 * t ^ 2) + c ^ 2 * t ^ 3 := by
    ring
  rw [h5] at h4
  have : 0 ≤ c ^ 2 * t ^ 3 := by positivity
  linarith

lemma size_core (B κ l L q : ℝ) (hB : 0 < B) (hκ : 0 < κ) (hl : 0 < l) (hL : 0 < L)
    (hq12 : 1 / 12 < q) (hLq : L ^ 3 = 2 * B * q) (hk2 : κ ^ 2 * q ≤ 1)
    (hk1 : 1 ≤ (q + 1 / 12) * κ ^ 2)
    (hup : (κ * l) ^ 3 ≤ 2 * (B * κ))
    (hlo : 4 * (B * κ) ^ 2 ≤ ((κ * l) ^ 2) ^ 3 + (B * κ) ^ 2 * ((κ * l) ^ 2) ^ 2 / 12) :
    l - L ≤ B / (6 * L ^ 2) ∧ L - l ≤ 4 * B ^ 2 / (3 * L) := by
  have hq0 : 0 < q := by linarith
  have h1 : κ ^ 2 * l ^ 3 ≤ 2 * B := by
    have e : (κ * l) ^ 3 = κ * (κ ^ 2 * l ^ 3) := by ring
    rw [e] at hup
    have : κ * (κ ^ 2 * l ^ 3) ≤ κ * (2 * B) := by linarith
    exact le_of_mul_le_mul_left this hκ
  have hl3 : 0 < l ^ 3 := by positivity
  have h2 : l ^ 3 ≤ L ^ 3 + B / 6 := by
    have ha : l ^ 3 ≤ (q + 1 / 12) * (κ ^ 2 * l ^ 3) := by
      have := mul_le_mul_of_nonneg_right hk1 hl3.le
      nlinarith
    have hb := mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ q + 1 / 12)
    rw [hLq]; nlinarith
  have hL3 : B / 6 < L ^ 3 := by rw [hLq]; nlinarith
  have hl2 : l ≤ 2 * L := by
    by_contra hcon
    push_neg at hcon
    have := pow_lt_pow_left₀ hcon (by positivity) (by norm_num : (3:ℕ) ≠ 0)
    have e : (2 * L) ^ 3 = 8 * L ^ 3 := by ring
    rw [e] at this
    linarith
  constructor
  · rcases le_or_gt l L with h | h
    · have : 0 ≤ B / (6 * L ^ 2) := by positivity
      linarith
    · rw [le_div_iff₀ (by positivity)]
      have e : l ^ 3 - L ^ 3 - (l - L) * (3 * L ^ 2) = (l - L) ^ 2 * (l + 2 * L) := by ring
      have : 0 ≤ (l - L) ^ 2 * (l + 2 * L) := by positivity
      nlinarith
  · rcases le_or_gt L l with h | h
    · have : 0 ≤ 4 * B ^ 2 / (3 * L) := by positivity
      linarith
    · -- L^6 ≤ l^6 + B^2 l^4 / 12
      have hW : 4 * B ^ 2 ≤ κ ^ 4 * (l ^ 6 + B ^ 2 * l ^ 4 / 12) := by
        have e1 : 4 * (B * κ) ^ 2 = κ ^ 2 * (4 * B ^ 2) := by ring
        have e2 : ((κ * l) ^ 2) ^ 3 + (B * κ) ^ 2 * ((κ * l) ^ 2) ^ 2 / 12
            = κ ^ 2 * (κ ^ 4 * (l ^ 6 + B ^ 2 * l ^ 4 / 12)) := by ring
        rw [e1, e2] at hlo
        exact le_of_mul_le_mul_left hlo (by positivity)
      have hW0 : 0 ≤ l ^ 6 + B ^ 2 * l ^ 4 / 12 := by positivity
      have hkq : (κ ^ 2 * q) ^ 2 ≤ 1 := by
        have : 0 ≤ κ ^ 2 * q := by positivity
        nlinarith
      have hL6 : L ^ 6 ≤ l ^ 6 + B ^ 2 * l ^ 4 / 12 := by
        have e : L ^ 6 = q ^ 2 * (4 * B ^ 2) := by
          have : L ^ 6 = (L ^ 3) ^ 2 := by ring
          rw [this, hLq]; ring
        rw [e]
        have := mul_le_mul_of_nonneg_left hW (by positivity : (0:ℝ) ≤ q ^ 2)
        have e2 : q ^ 2 * (κ ^ 4 * (l ^ 6 + B ^ 2 * l ^ 4 / 12))
            = (κ ^ 2 * q) ^ 2 * (l ^ 6 + B ^ 2 * l ^ 4 / 12) := by ring
        rw [e2] at this
        nlinarith
      have hl4 : l ^ 4 ≤ 16 * L ^ 4 := by
        have := pow_le_pow_left₀ hl.le hl2 4
        have e : (2 * L) ^ 4 = 16 * L ^ 4 := by ring
        linarith
      have hl5 : l ^ 5 ≤ L ^ 5 := pow_le_pow_left₀ hl.le h.le 5
      have h6 : (L - l) * L ^ 5 ≤ L ^ 6 - l ^ 6 := by
        have e : L ^ 6 - l ^ 6 - (L - l) * L ^ 5 = l * (L ^ 5 - l ^ 5) := by ring
        have : 0 ≤ l * (L ^ 5 - l ^ 5) := mul_nonneg hl.le (by linarith)
        linarith
      have h7 : (L - l) * L ^ 5 ≤ B ^ 2 * (16 * L ^ 4) / 12 := by
        have := mul_le_mul_of_nonneg_left hl4 (sq_nonneg B)
        nlinarith
      rw [le_div_iff₀ (by positivity)]
      have h8 : ((L - l) * L) * L ^ 4 ≤ (4 * B ^ 2 / 3) * L ^ 4 := by
        have e : ((L - l) * L) * L ^ 4 = (L - l) * L ^ 5 := by ring
        rw [e]; linarith
      have h9 := le_of_mul_le_mul_right h8 (by positivity)
      nlinarith

open LNChannels.RateBounds in
lemma bounds_at (lam B r l T ρ : ℝ) (hlam : 0 < lam) (hB : 0 < B) (hr : 0 < r)
    (hrl : r < lam) (hsm : 4 * B ^ 2 * r < lam)
    (hρ : 0 < ρ) (hρ3 : ρ ^ 3 = r) (hρ1 : ρ ≤ 1) (hT : 0 < T) (hT3 : T ^ 3 = 2 * B * lam)
    (hl : 0 < l)
    (hmin : ∀ u v : ℝ, 0 < u → 0 < v → biCost lam lam r B l l ≤ biCost lam lam r B u v)
    (hroot : ∀ E : ℝ, LNChannels.Exact.alphaPlus lam lam r = E →
        (Real.exp (Real.log E * l) - 1) ^ 3
          = B * Real.log E * (Real.exp (Real.log E * l) * (Real.exp (Real.log E * l) + 1))) :
    |biCost lam lam r B l l - (3 * (T / ρ) - B / 6)|
        ≤ (T / (4 * lam) + B / (6 * T ^ 2) + B * T ^ 2 / (72 * lam)) * ρ ∧
      |l - T / ρ| ≤ (B / (6 * T ^ 2) + 4 * B ^ 2 / (3 * T)) * ρ := by
  have hr12 : r < 12 * lam := by linarith
  constructor
  · have hlow := LNChSR3.lower_bd lam r B l l T ρ hlam hr hB hl hl hr12 hρ hρ3 hT hT3
    have hup := (hmin (T / ρ) (T / ρ) (by positivity) (by positivity)).trans
      (LNChSR3.upper_bd lam r B T ρ hlam hr hB hr12 hρ hρ3 hT hT3)
    have hρρ : ρ ^ 2 ≤ ρ := pow_le_of_le_one hρ.le hρ1 (by norm_num)
    have a1 : T * ρ ^ 2 / (4 * lam) ≤ T * ρ / (4 * lam) := by gcongr
    have a2 : B * ρ ^ 2 / (6 * T ^ 2) ≤ B * ρ / (6 * T ^ 2) := by gcongr
    have hK : (T / (4 * lam) + B / (6 * T ^ 2) + B * T ^ 2 / (72 * lam)) * ρ
        = T * ρ / (4 * lam) + B * ρ / (6 * T ^ 2) + B * T ^ 2 * ρ / (72 * lam) := by ring
    have a3 : 0 ≤ B * ρ / (6 * T ^ 2) := by positivity
    have a4 : 0 ≤ B * T ^ 2 * ρ / (72 * lam) := by positivity
    have a5 : 0 ≤ T * ρ / (4 * lam) := by positivity
    have e3 : 3 * (T / ρ) = 3 * T / ρ := by ring
    rw [hK, abs_le, e3]
    constructor <;> linarith
  · obtain ⟨E, κ, hE1, hκE, hκ0, hαp, hαm, -, hk2, hk1⟩ := LNChSR3.kappa_facts lam r hlam hr hr12
    have hr' := hroot E hαp
    rw [← hκE] at hr'
    obtain ⟨u, hu⟩ : ∃ u, u = κ * l := ⟨_, rfl⟩
    rw [← hu] at hr'
    have hu0 : 0 < u := by rw [hu]; positivity
    obtain ⟨y, hy⟩ : ∃ y, y = Real.exp u := ⟨_, rfl⟩
    rw [← hy] at hr'
    have hy1 : 1 < y := by rw [hy]; exact Real.one_lt_exp_iff.mpr hu0
    have hDeq := D_eq y (B * κ) hy1 hr'
    have hcl := LNChSR3.cosh_lower u
    rw [Real.exp_neg, ← hy] at hcl
    have hc0 : 0 < B * κ := by positivity
    have hup := u_upper u (B * κ) _ hu0 hc0 hcl hDeq
    -- u < 1
    have hk4 : (2 * (B * κ)) ^ 2 < 1 := by
      have e : (2 * (B * κ)) ^ 2 = 4 * B ^ 2 * κ ^ 2 := by ring
      rw [e]
      have h1 := mul_le_mul_of_nonneg_left hk2 (by positivity : (0:ℝ) ≤ 4 * B ^ 2)
      have h2 : 4 * B ^ 2 * (r / lam) < 1 := by
        rw [← mul_div_assoc, div_lt_one hlam]; exact hsm
      linarith
    have hc1 : 2 * (B * κ) < 1 := by nlinarith
    have hu1 : u < 1 := by
      by_contra hcon
      push_neg at hcon
      have := one_le_pow₀ (n := 3) hcon
      linarith
    have hu12 : u ^ 2 < 12 := by nlinarith
    have hcu := LNChSR3.cosh_upper u hu12
    rw [Real.cosh_eq, Real.exp_neg, ← hy] at hcu
    have h12 : 0 < 12 - u ^ 2 := by linarith
    have h12' : 12 - u ^ 2 ≠ 0 := h12.ne'
    have hq : y + y⁻¹ - 2 ≤ 2 * (72 / (12 - u ^ 2)) - 12 := by linarith
    have he : 2 * (72 / (12 - u ^ 2)) - 12 = 12 * u ^ 2 / (12 - u ^ 2) := by field_simp; ring
    rw [he, le_div_iff₀ h12] at hq
    have hD0 : 0 < y + y⁻¹ - 2 := by
      have : 0 < u ^ 2 + u ^ 4 / 12 := by positivity
      linarith
    have hlo := u_lower (u ^ 2) (B * κ) _ (by positivity) (by nlinarith) hc0 hD0 hq hDeq
    rw [hu] at hup hlo
    have hq12 : 1 / 12 < lam / r := by rw [lt_div_iff₀ hr]; linarith
    have hLq : (T / ρ) ^ 3 = 2 * B * (lam / r) := by rw [div_pow, hT3, hρ3]; ring
    have hk2' : κ ^ 2 * (lam / r) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hk2 (by positivity : (0:ℝ) ≤ lam / r)
      have e : r / lam * (lam / r) = 1 := by field_simp
      linarith
    have hk1' : 1 ≤ (lam / r + 1 / 12) * κ ^ 2 := (div_le_iff₀ (by positivity)).mp hk1
    obtain ⟨s1, s2⟩ := size_core B κ l (T / ρ) (lam / r) hB hκ0 hl (by positivity) hq12 hLq hk2' hk1'
      hup hlo
    have e1 : B / (6 * (T / ρ) ^ 2) = B * ρ ^ 2 / (6 * T ^ 2) := by field_simp
    have e2 : 4 * B ^ 2 / (3 * (T / ρ)) = 4 * B ^ 2 * ρ / (3 * T) := by field_simp
    rw [e1] at s1
    rw [e2] at s2
    have hρρ : ρ ^ 2 ≤ ρ := pow_le_of_le_one hρ.le hρ1 (by norm_num)
    have a1 : B * ρ ^ 2 / (6 * T ^ 2) ≤ B * ρ / (6 * T ^ 2) := by gcongr
    have hK : (B / (6 * T ^ 2) + 4 * B ^ 2 / (3 * T)) * ρ
        = B * ρ / (6 * T ^ 2) + 4 * B ^ 2 * ρ / (3 * T) := by ring
    have a3 : 0 ≤ B * ρ / (6 * T ^ 2) := by positivity
    have a4 : 0 ≤ 4 * B ^ 2 * ρ / (3 * T) := by positivity
    rw [hK, abs_le]
    constructor <;> linarith

end LNChAOC

open LightningChannels.SymmetricCosts in
theorem solution (B rate : ℝ)
    (hB : 0 < B) (hRate : 0 < rate) :
    ∃ m : ℝ → ℝ,
      (∀ r : ℝ, 0 < r → IsGlobalMin B rate r (m r) (m r)) ∧
      ∃ Kcost Ksize δ : ℝ, 0 < Kcost ∧ 0 < Ksize ∧ 0 < δ ∧
        ∀ r : ℝ, 0 < r → r < δ →
          |LNChannels.RateBounds.biCost rate rate r B (m r) (m r) -
            (3 * (2 * B * rate / r) ^ (1 / 3 : ℝ) - B / 6)| ≤
              Kcost * r ^ (1 / 3 : ℝ) ∧
          |m r - (2 * B * rate / r) ^ (1 / 3 : ℝ)| ≤
              Ksize * r ^ (1 / 3 : ℝ) := by
  have hex : ∀ r : ℝ, ∃ l : ℝ, 0 < r → (0 < l ∧
      (∀ u v : ℝ, 0 < u → 0 < v → LNChannels.RateBounds.biCost rate rate r B l l
          ≤ LNChannels.RateBounds.biCost rate rate r B u v) ∧
      ∀ E : ℝ, LNChannels.Exact.alphaPlus rate rate r = E →
        (Real.exp (Real.log E * l) - 1) ^ 3
          = B * Real.log E * (Real.exp (Real.log E * l) * (Real.exp (Real.log E * l) + 1))) := by
    intro r
    by_cases hr : 0 < r
    · obtain ⟨l, h⟩ := LNChAOC.exists_min rate B r hRate hB hr
      exact ⟨l, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hr⟩
  choose m hm using hex
  refine ⟨m, ?_, ?_⟩
  · intro r hr
    obtain ⟨hl, hmin, -⟩ := hm r hr
    simp only [IsGlobalMin, positiveQuadrant, Set.mem_ofPred_eq]
    exact ⟨⟨hl, hl⟩, fun u v huv => hmin u v huv.1 huv.2⟩
  · obtain ⟨T, hTdef⟩ : ∃ T, T = (2 * B * rate) ^ (1 / 3 : ℝ) := ⟨_, rfl⟩
    have hT0 : 0 < T := by rw [hTdef]; positivity
    have hT3 : T ^ 3 = 2 * B * rate := by
      rw [hTdef, show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
      exact Real.rpow_inv_natCast_pow (by positivity) (by norm_num)
    refine ⟨T / (4 * rate) + B / (6 * T ^ 2) + B * T ^ 2 / (72 * rate),
      B / (6 * T ^ 2) + 4 * B ^ 2 / (3 * T), min (min 1 rate) (rate / (4 * B ^ 2)),
      by positivity, by positivity, by positivity, ?_⟩
    intro r hr0 hrδ
    have hr1 : r < 1 := lt_of_lt_of_le hrδ ((min_le_left _ _).trans (min_le_left _ _))
    have hrl : r < rate := lt_of_lt_of_le hrδ ((min_le_left _ _).trans (min_le_right _ _))
    have hsm' : r < rate / (4 * B ^ 2) := lt_of_lt_of_le hrδ (min_le_right _ _)
    have hsm : 4 * B ^ 2 * r < rate := by
      rw [lt_div_iff₀ (by positivity)] at hsm'; linarith
    obtain ⟨ρ, hρdef⟩ : ∃ ρ, ρ = r ^ (1 / 3 : ℝ) := ⟨_, rfl⟩
    have hρ0 : 0 < ρ := by rw [hρdef]; positivity
    have hρ3 : ρ ^ 3 = r := by
      rw [hρdef, show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
      exact Real.rpow_inv_natCast_pow hr0.le (by norm_num)
    have hρ1 : ρ ≤ 1 := by rw [hρdef]; exact Real.rpow_le_one hr0.le hr1.le (by norm_num)
    have hdiv : (2 * B * rate / r) ^ (1 / 3 : ℝ) = T / ρ := by
      rw [Real.div_rpow (by positivity) hr0.le, hTdef, hρdef]
    rw [hdiv, ← hρdef]
    obtain ⟨hl, hmin, hroot⟩ := hm r hr0
    exact LNChAOC.bounds_at rate B r (m r) T ρ hRate hB hr0 hrl hsm hρ0 hρ3 hρ1 hT0 hT3 hl hmin hroot
