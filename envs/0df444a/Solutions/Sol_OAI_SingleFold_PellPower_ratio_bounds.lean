-- Prove2me | solution 1 for OAI.SingleFold.PellPower.ratio_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:20:05.106092+00:00
-- url     : https://prove2.me/submissions/098fe796-db6f-40cd-ad5c-428349868c02

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

open OAI OAI.SingleFold OAI.SingleFold.PellPower
variable {a : ℕ} (ha : 1 < a)


theorem solution {b u : ℕ} (hb : 1 < b) (hu : 1 < u) (n : ℕ) :
    (b:ℝ)^n ≤ (Pell.yn (show 1 < b*u by nlinarith) (n+1):ℝ)/Pell.yn hu (n+1) ∧
    (Pell.yn (show 1 < b*u by nlinarith) (n+1):ℝ)/Pell.yn hu (n+1) ≤
      (b:ℝ)^n*(1+1/(2*u-1))^n := by
  have hbu : 1 < b*u := by nlinarith
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
  have hBp := hBpos n
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hBp]; exact hL n
  · rw [div_le_iff₀ hBp]
    have := hU n
    rw [hc] at this; exact this

