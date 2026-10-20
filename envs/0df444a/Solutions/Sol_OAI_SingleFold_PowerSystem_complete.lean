-- Prove2me | solution 1 for OAI.SingleFold.PowerSystem.complete
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:36:56.345612+00:00
-- url     : https://prove2.me/submissions/e8673dac-5c3e-4205-80fd-51d2206ef3cc

import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell
import Definitions.Def_OAI_NumberTheory_SingleFold_Power
import Theorems.Thm_OAI_SingleFold_PellPower_ratio_bounds
import Theorems.Thm_OAI_SingleFold_PellAnalytics_quotient_error
import Theorems.Thm_OAI_SingleFold_PowerEstimate_input_bounds
import Theorems.Thm_OAI_SingleFold_PellPower_power_bounds

open OAI OAI.SingleFold OAI.SingleFold.PowerSystem
open PowerEstimate
variable {g : ℕ → ℕ} {δ : ℝ} {ell u₀ : ℕ}
variable (hδ : 0<δ) (hell : 1≤ell) (h₀ : 4≤u₀)
variable (hg : ∀ u, u₀≤u → δ*(Real.log (u:ℝ))^2<Real.log (g u:ℝ) ∧ Real.log (g u:ℝ)<(u:ℝ)*Real.log (u:ℝ))
include hδ hell h₀ hg
omit hδ hell h₀ hg in
theorem h49_pell_sum {a : ℕ} (ha : 1 < a) (m : ℕ) :
    (Pell.xn ha m)^2 + (Pell.yn ha m)^2 = 1 + a^2 * (Pell.yn ha m)^2 := by
  have h : Pell.xn ha m * Pell.xn ha m - (a*a-1) * Pell.yn ha m * Pell.yn ha m = 1 := Pell.pell_eq ha m
  obtain ⟨P, hP⟩ : ∃ P, P = Pell.xn ha m * Pell.xn ha m := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (a*a-1) * Pell.yn ha m * Pell.yn ha m := ⟨_, rfl⟩
  rw [← hP, ← hQ] at h
  have hPQ : P = 1 + Q := by omega
  rw [hP, hQ] at hPQ
  have ha2 : 1 ≤ a * a := by nlinarith
  zify [ha2] at hPQ ⊢
  linear_combination hPQ

omit hδ hell h₀ hg in
theorem h49_pell_div {a : ℕ} (ha : 1 < a) (m : ℕ) :
    Pell.yn ha m = m + (a - 1) * ((Pell.yn ha m - m) / (a - 1)) := by
  have hge := Pell.yn_ge_n ha m
  have hmod := Pell.yn_modEq_a_sub_one ha m
  have hdvd : (a - 1) ∣ Pell.yn ha m - m := (Nat.modEq_iff_dvd' hge).1 hmod.symm
  rw [Nat.mul_div_cancel' hdvd]; omega

theorem solution (hell' : 3<δ*(ell:ℝ)*Real.log 2) {b n : ℕ} (hb : 2≤b) :
    ∃ w, System g ell u₀ b n (b^n) w := by
  obtain ⟨hu0, hu1, hu2, hu3⟩ := PowerEstimate.input_bounds (ell := ell) (u₀ := u₀) (b := b) (n := n)
    (c := b^n) hell h₀
  set u := input ell u₀ b n (b^n) with hu
  have hu1' : 1 < u := by omega
  have hbu : 1 < b * u := by nlinarith
  set Y := Pell.yn hbu (n+1) with hY
  set y := Pell.yn hu1' (n+1) with hy
  have hYpos : 0 < Y := lt_of_lt_of_le (Nat.succ_pos n) (Pell.yn_ge_n hbu (n+1))
  have hypos : 0 < y := lt_of_lt_of_le (Nat.succ_pos n) (Pell.yn_ge_n hu1' (n+1))
  -- quotient
  have hrb := PellPower.ratio_bounds (b := b) (u := u) (by omega) hu1' n
  have hqe := PellAnalytics.quotient_error (b := b) (n := n) (c := b^n) (u := u) hu1 le_rfl
    (F := (Y:ℝ)) (H := (y:ℝ)) (by exact_mod_cast hypos) hrb.1 hrb.2
  have hyR : (0:ℝ) < y := by exact_mod_cast hypos
  have hlo : b^n * y ≤ Y := by
    have := hqe.1
    rw [sub_nonneg, le_div_iff₀ hyR] at this
    exact_mod_cast this
  have hhi : Y < (b^n + 1) * y := by
    have := hqe.2
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hyR] at this
    have : (Y:ℝ) < ((b^n + 1 : ℕ) : ℝ) * y := by push_cast; linarith
    exact_mod_cast this
  -- size bounds
  have hg' := hg u hu0
  have hlogu : 0 < Real.log (u:ℝ) := Real.log_pos (by exact_mod_cast hu1')
  have hYle : Y ≤ (2 * (b*u))^n := (PellPower.power_bounds hbu n).2
  have hyle : y ≤ (2 * u)^n := (PellPower.power_bounds hu1' n).2
  have hyY : (2*u)^n ≤ (2*(b*u))^n := Nat.pow_le_pow_left (by nlinarith) n
  have hcube : 2 * (b * u) ≤ u^3 := by
    have : b ≤ u := by omega
    have : 2 ≤ u := by omega
    calc 2 * (b * u) ≤ u * (u * u) := Nat.mul_le_mul (by omega) (Nat.mul_le_mul_right _ ‹b ≤ u›)
      _ = u^3 := by ring
  have hpowu : 2^(n*ell) ≤ u := by
    have h1 : (b^n + 1)^ell ≤ u := by
      have : (b^n+1)^ell ≤ (b^n+1)^ell*(n+1)*(b+1) := by
        calc (b^n+1)^ell = (b^n+1)^ell*1*1 := by ring
          _ ≤ (b^n+1)^ell*(n+1)*(b+1) := by gcongr <;> omega
      rw [hu]; unfold input; omega
    calc 2^(n*ell) = (2^n)^ell := by rw [pow_mul]
      _ ≤ (b^n+1)^ell := Nat.pow_le_pow_left (by have := Nat.pow_le_pow_left (show 2 ≤ b by omega) n; omega) _
      _ ≤ u := h1
  have hlogu2 : (n:ℝ) * ell * Real.log 2 ≤ Real.log u := by
    have := Real.log_le_log (by positivity) (show ((2:ℝ)^(n*ell)) ≤ (u:ℝ) by exact_mod_cast hpowu)
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hbig : Real.log (((2*(b*u))^n : ℕ) : ℝ) < Real.log (g u : ℝ) := by
    have e1 : Real.log (((2*(b*u))^n : ℕ) : ℝ) ≤ 3 * n * Real.log u := by
      push_cast
      rw [Real.log_pow]
      have : Real.log ((2:ℝ) * (b * u)) ≤ Real.log ((u:ℝ)^3) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hcube)
      rw [Real.log_pow] at this; push_cast at this
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have e2 : 3 * (n:ℝ) * Real.log u ≤ δ * (Real.log u)^2 := by
      have : 3 * (n:ℝ) ≤ δ * Real.log u := by
        have h3 : 3 * (n:ℝ) ≤ δ * ell * Real.log 2 * n := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
        have h4 : δ * ell * Real.log 2 * n ≤ δ * Real.log u := by
          have := mul_le_mul_of_nonneg_left hlogu2 hδ.le; nlinarith
        linarith
      nlinarith
    linarith [hg'.1]
  have hgpos : 0 < g u := by
    by_contra h0; push_neg at h0
    have : g u = 0 := by omega
    rw [this] at hg'; simp at hg'; nlinarith [hg'.1, sq_nonneg (Real.log u)]
  have hlt : (2*(b*u))^n < g u := by
    have := (Real.log_lt_log_iff (by positivity) (by exact_mod_cast hgpos)).1 hbig
    exact_mod_cast this
  refine ⟨![u, g u, Pell.xn hbu (n+1), Y, Pell.xn hu1' (n+1), y,
    (Y - (n+1)) / (b*u - 1), (y - (n+1)) / (u - 1), Y - b^n * y], ?_⟩
  unfold System
  refine ⟨hb, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (Pell.xn hbu (n+1))^2 + Y^2 = 1 + (b*u)^2 * Y^2
    rw [hY, h49_pell_sum hbu (n+1)]
  · show (Pell.xn hu1' (n+1))^2 + y^2 = 1 + u^2 * y^2
    rw [hy, h49_pell_sum hu1' (n+1)]
  · exact hYpos
  · show Y < g u; omega
  · exact hypos
  · show y < g u; omega
  · show Y = n + 1 + (b*u - 1) * ((Y - (n+1)) / (b*u - 1))
    exact h49_pell_div hbu (n+1)
  · show y = n + 1 + (u - 1) * ((y - (n+1)) / (u - 1))
    exact h49_pell_div hu1' (n+1)
  · show Y = b^n * y + (Y - b^n * y); omega
  · show Y - b^n * y < y
    have : (b^n+1)*y = b^n*y + y := by ring
    omega

