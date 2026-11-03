-- Prove2me | solution 1 for KyleProduction.Monopoly.trading_stage
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T04:48:40.23995+00:00
-- url     : https://prove2.me/submissions/33ff7b69-88d7-4824-b054-5bc757acc486

import Mathlib
import Definitions.Def_KyleProduction_Monopoly_Model
import Theorems.Thm_KyleProduction_Monopoly_market_maker_update
import Theorems.Thm_KyleProduction_Monopoly_insider_best_response

open MeasureTheory ProbabilityTheory

namespace Aux_ts
open KyleProduction.Monopoly

/-- Insider optimality at `q ≠ 0` forces `λ > 0` and the best-response coefficients. -/
theorem insider_coeffs (P : Params) (hS : P.Standing) (q : ℝ) (hq : q ≠ 0) (e : LinStrat)
    (h : InsiderOptimal P q e) :
    0 < e.lam ∧ e.α = -e.μ / (2 * e.lam) ∧ e.β = 1 / (2 * e.lam) := by
  have hpay := fun v => (insider_best_response P hS e v).1
  -- every real value is attained by `firmValue q`
  have hsurj : ∀ v : ℝ, firmValue q (v / q + q) = v := by
    intro v; unfold firmValue; field_simp; ring
  have hopt : ∀ v d : ℝ, insiderPayoff P e v d ≤ insiderPayoff P e v (demand e v) := by
    intro v d
    have := h (v / q + q) d
    rwa [hsurj] at this
  have hlam : 0 < e.lam := by
    by_contra hneg
    push_neg at hneg
    set v := e.μ + 1
    set d0 := demand e v
    set B := insiderPayoff P e v d0
    have h1 := hopt v (|B| + 1)
    rw [hpay v (|B| + 1)] at h1
    have : (v - e.μ - e.lam * (|B| + 1)) * (|B| + 1) ≥ |B| + 1 := by
      have hv : v - e.μ = 1 := by simp [v]
      have hB : 0 ≤ |B| := abs_nonneg B
      nlinarith [mul_nonneg (neg_nonneg.mpr hneg) (mul_nonneg (by linarith : (0:ℝ) ≤ |B| + 1)
        (by linarith : (0:ℝ) ≤ |B| + 1))]
    have := le_abs_self B
    linarith
  have hbr : ∀ v : ℝ, demand e v = -e.μ / (2 * e.lam) + v / (2 * e.lam) := by
    intro v
    exact ((insider_best_response P hS e v).2 hlam (demand e v)).1 (fun d' => hopt v d')
  have h0 := hbr 0
  have h1 := hbr 1
  simp only [demand] at h0 h1
  refine ⟨hlam, by simpa using h0, ?_⟩
  have : e.β = (e.α + e.β * 1) - e.α := by ring
  rw [this, h1, ← (by simpa using h0 : e.α = -e.μ / (2 * e.lam))]
  ring

end Aux_ts

open KyleProduction.Monopoly in
theorem solution (P : Params) (hS : P.Standing) (q : ℝ) (hq : 0 < q) (e : LinStrat) :
    IsLinEq P q e ↔ e = eqStrat P q := by
  obtain ⟨hSa, hSθ, hSu, hω, -⟩ := id hS
  have hv : 0 < postVar P := by unfold postVar; positivity
  set r := Real.sqrt P.Su with hr
  set t := Real.sqrt (postVar P) with ht
  have hr0 : 0 < r := Real.sqrt_pos.mpr hSu
  have ht0 : 0 < t := Real.sqrt_pos.mpr hv
  have hr2 : r ^ 2 = P.Su := Real.sq_sqrt hSu.le
  have ht2 : t ^ 2 = postVar P := Real.sq_sqrt hv.le
  set m := postMean P with hm
  constructor
  · rintro ⟨hI, hM⟩
    obtain ⟨hl, hα, hβ⟩ := Aux_ts.insider_coeffs P hS q hq.ne' e hI
    obtain ⟨hlam, hμ⟩ := (market_maker_update P hS q e).1 hM
    rw [← ht2, ← hr2] at hlam
    -- `λ = qt/(2r)`
    have hden : 0 < e.β ^ 2 * q ^ 2 * t ^ 2 + r ^ 2 := by positivity
    have hβl : e.β * (2 * e.lam) = 1 := by rw [hβ]; field_simp
    have hlam' : e.lam * (e.β ^ 2 * q ^ 2 * t ^ 2 + r ^ 2) = e.β * q ^ 2 * t ^ 2 := by
      rw [hlam]; field_simp
    have hsq : (2 * e.lam * r) ^ 2 = (q * t) ^ 2 := by
      -- multiply `hlam'` by `4 λ`
      have := congrArg (fun z => 4 * e.lam * z) hlam'
      have e1 : 4 * e.lam * (e.lam * (e.β ^ 2 * q ^ 2 * t ^ 2 + r ^ 2)) =
          (e.β * (2 * e.lam)) ^ 2 * q ^ 2 * t ^ 2 + 4 * e.lam ^ 2 * r ^ 2 := by ring
      have e2 : 4 * e.lam * (e.β * q ^ 2 * t ^ 2) = 2 * (e.β * (2 * e.lam)) * q ^ 2 * t ^ 2 := by
        ring
      rw [e1, e2, hβl] at this
      nlinarith [this]
    have hlr : 2 * e.lam * r = q * t := by
      have h1 : 0 < 2 * e.lam * r := by positivity
      have h2 : 0 < q * t := by positivity
      nlinarith [sq_nonneg (2 * e.lam * r - q * t), sq_nonneg (2 * e.lam * r + q * t)]
    have hlamv : e.lam = q / (2 * r) * t := by field_simp; linarith
    have hμv : e.μ = q * (m - q) := by
      have hαl : e.α * (2 * e.lam) = -e.μ := by rw [hα]; field_simp
      have : e.μ = q * (m - q) - (e.lam * e.α + e.lam * e.β * (q * (m - q))) := by
        rw [hμ]; ring
      have h3 : e.lam * e.β = 1 / 2 := by linarith [hβl]
      have h4 : e.lam * e.α = -e.μ / 2 := by linarith [hαl]
      rw [h3, h4] at this
      linarith
    cases e with
    | mk α β μ lam =>
      simp only at hα hβ hlamv hμv
      simp only [eqStrat, LinStrat.mk.injEq]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hα, hμv, hlamv, ← hr, ← ht, ← hm]; field_simp
      · rw [hβ, hlamv, ← hr, ← ht]; field_simp
      · rw [hμv, ← hm]
      · rw [hlamv, ← hr, ← ht]
  · rintro rfl
    have hlpos : 0 < (eqStrat P q).lam := by
      simp only [eqStrat]; rw [← hr, ← ht]; positivity
    refine ⟨?_, ?_⟩
    · intro a d
      set v := firmValue q a
      refine ((insider_best_response P hS (eqStrat P q) v).2 hlpos _).2 ?_ d
      simp only [demand, eqStrat]
      rw [← hr, ← ht, ← hm]
      field_simp
    · refine (market_maker_update P hS q (eqStrat P q)).2 ⟨?_, ?_⟩
      · simp only [eqStrat]
        rw [← hr, ← ht, ← ht2, ← hr2]
        field_simp
        ring
      · simp only [eqStrat]
        rw [← hr, ← ht, ← hm]
        field_simp
        ring
