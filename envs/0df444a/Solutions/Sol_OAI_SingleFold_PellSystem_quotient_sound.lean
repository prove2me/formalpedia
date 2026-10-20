-- Prove2me | solution 1 for OAI.SingleFold.PellSystem.quotient_sound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:21:58.042694+00:00
-- url     : https://prove2.me/submissions/2ac9b366-3405-48be-b977-0fdcfac3113f

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

open OAI OAI.SingleFold
theorem h49_ratio {b u : ℕ} (hb : 1 < b) (hu : 1 < u) (hbu : 1 < b*u) (n : ℕ) :
    (b:ℝ)^n * (Pell.yn hu (n+1) : ℝ) ≤ (Pell.yn hbu (n+1) : ℝ) ∧
    (Pell.yn hbu (n+1) : ℝ) ≤ ((b:ℝ)^n * (1 + 1/(2*(u:ℝ)-1))^n) * (Pell.yn hu (n+1) : ℝ) := by
  set A : ℕ → ℝ := fun n => (Pell.yn hbu n : ℝ) with hAdef
  set B : ℕ → ℝ := fun n => (Pell.yn hu n : ℝ) with hBdef
  have hA : ∀ n, A (n+2) + A n = 2*((b:ℝ)*u) * A (n+1) := by
    intro n; simp only [hAdef]; exact_mod_cast Pell.yn_succ_succ hbu n
  have hB : ∀ n, B (n+2) + B n = 2*(u:ℝ) * B (n+1) := by
    intro n; simp only [hBdef]; exact_mod_cast Pell.yn_succ_succ hu n
  have hA0 : A 0 = 0 := by simp [hAdef]
  have hA1 : A 1 = 1 := by simp [hAdef]
  have hB0 : B 0 = 0 := by simp [hBdef]
  have hB1 : B 1 = 1 := by simp [hBdef]
  have hAnn : ∀ n, 0 ≤ A n := fun n => by simp [hAdef]
  have hBnn : ∀ n, 0 ≤ B n := fun n => by simp [hBdef]
  have hApos : ∀ n, 0 < A (n+1) := fun n => by
    simp only [hAdef]; exact_mod_cast (Pell.strictMono_y hbu (Nat.zero_lt_succ n)).trans_le' (by simp)
  have hBpos : ∀ n, 0 < B (n+1) := fun n => by
    simp only [hBdef]; exact_mod_cast (Pell.strictMono_y hu (Nat.zero_lt_succ n)).trans_le' (by simp)
  have hBmono : ∀ n, B n ≤ B (n+1) := fun n => by
    simp only [hBdef]; exact_mod_cast (Pell.strictMono_y hu (Nat.lt_succ_self n)).le
  have hb1 : (1:ℝ) < b := by exact_mod_cast hb
  have hu1 : (1:ℝ) < u := by exact_mod_cast hu
  have hP : ∀ n, (b:ℝ) * B (n+2) * A (n+1) ≤ A (n+2) * B (n+1) := by
    intro n
    induction n with
    | zero =>
      have h1 := hA 0; have h2 := hB 0
      simp only [zero_add] at h1 h2
      rw [hA0, hA1] at h1; rw [hB0, hB1] at h2
      rw [hA1, hB1]; nlinarith
    | succ n ih =>
      have h1 := hA (n+1); have h2 := hB (n+1)
      have e1 : A (n+1+2) = 2*((b:ℝ)*u) * A (n+2) - A (n+1) := by linarith
      have e2 : B (n+1+2) = 2*(u:ℝ) * B (n+2) - B (n+1) := by linarith
      rw [e1, e2]
      have hx : 0 ≤ B (n+2) * A (n+1) := mul_nonneg (hBnn _) (hAnn _)
      have hy : 0 ≤ A (n+2) * B (n+1) := mul_nonneg (hAnn _) (hBnn _)
      nlinarith
  have hL : ∀ n, (b:ℝ)^n * B (n+1) ≤ A (n+1) := by
    intro n
    induction n with
    | zero => simp [hA1, hB1]
    | succ n ih =>
      have hp := mul_le_mul_of_nonneg_left (hP n) (pow_nonneg (by linarith : (0:ℝ) ≤ b) n)
      have hq := mul_le_mul_of_nonneg_left ih (hAnn (n+2))
      have hpos := hApos n
      have : ((b:ℝ)^(n+1) * B (n+1+1) - A (n+1+1)) * A (n+1) ≤ 0 := by
        rw [pow_succ]; nlinarith
      nlinarith
  set c : ℝ := 1 + 1/(2*(u:ℝ)-1) with hc
  have h2u : 0 < 2*(u:ℝ)-1 := by linarith
  have hc2 : c * (2*(u:ℝ)-1) = 2*(u:ℝ) := by rw [hc]; field_simp; ring
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hU : ∀ n, A (n+1) ≤ ((b:ℝ)^n * c^n) * B (n+1) := by
    intro n
    induction n with
    | zero => simp [hA1, hB1]
    | succ n ih =>
      have h1 := hA n; have h2 := hB n
      have hA2 : A (n+2) ≤ 2*((b:ℝ)*u) * A (n+1) := by linarith [hAnn n]
      have hB2 : (2*(u:ℝ)-1) * B (n+1) ≤ B (n+2) := by linarith [hBmono n]
      have hk : 0 ≤ (b:ℝ)^n * c^n := by positivity
      have hb0 : (0:ℝ) ≤ b := by linarith
      have hbc : 0 ≤ (b:ℝ)^n * c^n * ((b:ℝ) * c) := by positivity
      calc A (n+1+1) ≤ 2*((b:ℝ)*u) * A (n+1) := hA2
        _ ≤ 2*((b:ℝ)*u) * (((b:ℝ)^n * c^n) * B (n+1)) :=
            mul_le_mul_of_nonneg_left ih (by positivity)
        _ = ((b:ℝ)^n * c^n * ((b:ℝ) * c)) * ((2*(u:ℝ)-1) * B (n+1)) := by
            linear_combination (-((b:ℝ)^n * c^n) * (b:ℝ) * B (n+1)) * hc2
        _ ≤ ((b:ℝ)^n * c^n * ((b:ℝ) * c)) * B (n+2) := mul_le_mul_of_nonneg_left hB2 hbc
        _ = ((b:ℝ)^(n+1) * c^(n+1)) * B (n+1+1) := by ring
  exact ⟨hL n, by have := hU n; rw [hc] at this; exact this⟩

theorem solution {b u n c r : ℕ} (hb : 2≤b) (hu : (c+1)*(n+1)+4≤u)
    (hdiv : Pell.yn (show 1<b*u by nlinarith) (n+1)=c*Pell.yn (show 1<u by nlinarith) (n+1)+r)
    (hr : r<Pell.yn (show 1<u by nlinarith) (n+1)) : c=b^n := by
  have hu1 : 1 < u := by nlinarith
  have hbu : 1 < b*u := by nlinarith
  obtain ⟨hlo, hhi⟩ := h49_ratio (by omega : 1 < b) hu1 hbu n
  set Y := Pell.yn hu1 (n+1) with hY
  set X := Pell.yn hbu (n+1) with hX
  have hdiv' : X = c * Y + r := hdiv
  have hr' : r < Y := hr
  have hYpos : 0 < Y := lt_of_le_of_lt (Nat.zero_le r) hr'
  have hlo' : b^n * Y ≤ X := by exact_mod_cast hlo
  have h1 : b^n < c + 1 := by
    have : b^n * Y < (c+1) * Y := by rw [add_mul, one_mul]; omega
    exact Nat.lt_of_mul_lt_mul_right this
  by_contra hne
  have hc : b^n + 1 ≤ c := by omega
  set p : ℝ := ((b^n : ℕ) : ℝ) with hp
  have hp1 : (1:ℝ) ≤ p := by rw [hp]; exact_mod_cast Nat.one_le_pow _ _ (by omega)
  have hYr : (0:ℝ) < Y := by exact_mod_cast hYpos
  set y : ℝ := (n:ℝ)/(2*(u:ℝ)-1) with hy
  have hu' : ((c+1)*(n+1)+4 : ℝ) ≤ u := by exact_mod_cast hu
  have hc' : p + 1 ≤ (c:ℝ) := by rw [hp]; exact_mod_cast hc
  have h2u : 0 < 2*(u:ℝ)-1 := by
    have : (0:ℝ) ≤ c := by positivity
    have : (0:ℝ) ≤ n := by positivity
    nlinarith
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hyp : y * (p+1) < 1 := by
    rw [hy, div_mul_eq_mul_div, div_lt_one h2u]
    have : (0:ℝ) ≤ n := by positivity
    nlinarith
  have hq : (1 + 1/(2*(u:ℝ)-1))^n ≤ Real.exp y := by
    calc (1 + 1/(2*(u:ℝ)-1))^n ≤ (Real.exp (1/(2*(u:ℝ)-1)))^n := by
          apply pow_le_pow_left₀ (by positivity)
          have := Real.add_one_le_exp (1/(2*(u:ℝ)-1)); linarith
      _ = Real.exp y := by rw [← Real.exp_nat_mul, hy]; ring_nf
  have hexp : Real.exp y * (1 - y) ≤ 1 := by
    have h1 := Real.add_one_le_exp (-y)
    have h2 : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
    have h3 := Real.exp_pos y
    nlinarith
  have hcY : (c:ℝ) * Y ≤ p * (1 + 1/(2*(u:ℝ)-1))^n * Y := by
    have : (c:ℝ) * Y ≤ X := by exact_mod_cast (show c * Y ≤ X by omega)
    rw [hp]; push_cast; linarith
  have hcq : (c:ℝ) ≤ p * (1 + 1/(2*(u:ℝ)-1))^n := le_of_mul_le_mul_right hcY hYr
  have hyl : 0 < 1 - y := by nlinarith
  have : (p+1) * (1-y) ≤ p := by
    calc (p+1) * (1-y) ≤ p * Real.exp y * (1-y) := by
          apply mul_le_mul_of_nonneg_right _ hyl.le
          calc p + 1 ≤ (c:ℝ) := hc'
            _ ≤ p * (1 + 1/(2*(u:ℝ)-1))^n := hcq
            _ ≤ p * Real.exp y := mul_le_mul_of_nonneg_left hq (by linarith)
      _ = p * (Real.exp y * (1-y)) := by ring
      _ ≤ p * 1 := mul_le_mul_of_nonneg_left hexp (by linarith)
      _ = p := mul_one p
  nlinarith

