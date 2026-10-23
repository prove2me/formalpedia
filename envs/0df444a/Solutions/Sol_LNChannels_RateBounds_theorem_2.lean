-- Prove2me | solution 1 for LNChannels.RateBounds.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T08:15:04.651195+00:00
-- url     : https://prove2.me/submissions/a1c4d4e7-4e3f-4620-b945-0b2e7fa15711

import Mathlib
import Definitions.Def_LNChannels_RateBounds_ClosedForms

set_option autoImplicit false

namespace LNChRB2

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

end LNChRB2

open LNChannels.RateBounds in
theorem solution (lam r B C : ℝ) (hlam : 0 < lam) (hr : 0 < r) (hB : 0 < B) :
    ((∃ m : ℝ, 0 < m ∧ LNChannels.Exact.uniCost lam r B m < lam * C / r) →
        Real.log (1 + B * Real.log (1 + r / lam)) < C) ∧
      (let κ := Real.log ((r + 2 * lam + √(r * (4 * lam + r))) / (2 * lam));
        (∃ l₁ l₂ : ℝ, 0 < l₁ ∧ 0 < l₂ ∧ biCost lam lam r B l₁ l₂ < 2 * C * lam / r) →
          3 * (B * κ ^ 4 / 4) ^ (1 / 3 : ℝ) - B / 12 * κ ^ 2 < C) := by
  refine ⟨LNChRB2.part1 lam r B C hlam hr hB, ?_⟩
  intro κ hex
  obtain ⟨l₁, l₂, h1, h2, hc⟩ := hex
  exact LNChRB2.part2 lam r B C l₁ l₂ hlam hr hB h1 h2 hc
