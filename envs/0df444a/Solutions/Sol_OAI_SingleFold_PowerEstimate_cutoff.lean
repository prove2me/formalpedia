-- Prove2me | solution 1 for OAI.SingleFold.PowerEstimate.cutoff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:24:39.055342+00:00
-- url     : https://prove2.me/submissions/026e50d4-888b-418b-b898-79ffe3fd8c95

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

open OAI OAI.SingleFold OAI.SingleFold.PowerEstimate


theorem solution {δ : ℝ} {ell u₀ b n : ℕ} (hδ : 0<δ) (hell : 1≤ell)
    (hell' : 3<δ*(ell:ℝ)*Real.log 2) (h₀ : 4≤u₀) (hb : 2≤b) :
    let u := input ell u₀ b n (b^n)
    Real.log (((2*(b*u))^n:ℕ):ℝ) < δ*(Real.log (u:ℝ))^2 := by
  intro u
  have hu_def : u = (b^n+1)^ell*(n+1)*(b+1)+u₀ := rfl
  have hpow : 2^(n*ell) ≤ (b^n+1)^ell := by
    rw [pow_mul]; apply Nat.pow_le_pow_left
    calc 2^n ≤ b^n := Nat.pow_le_pow_left hb n
      _ ≤ b^n+1 := Nat.le_succ _
  have hu1 : 2^(n*ell) ≤ u := by
    have : (b^n+1)^ell ≤ (b^n+1)^ell*(n+1)*(b+1) := by
      rw [mul_assoc]; exact Nat.le_mul_of_pos_right _ (by positivity)
    omega
  have hub : b + 5 ≤ u := by
    have : 1 ≤ (b^n+1)^ell := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have : (b+1) ≤ (b^n+1)^ell*(n+1)*(b+1) := by
      apply Nat.le_mul_of_pos_left; positivity
    omega
  have hu4 : (4:ℝ) ≤ u := by exact_mod_cast (show 4 ≤ u by omega)
  have hupos : (0:ℝ) < u := by linarith
  set L := Real.log (u:ℝ) with hL
  have hL0 : 0 < L := Real.log_pos (by linarith)
  have hLn : (n:ℝ) * ell * Real.log 2 ≤ L := by
    have : Real.log ((2:ℝ)^(n*ell)) ≤ L := Real.log_le_log (by positivity) (by exact_mod_cast hu1)
    rw [Real.log_pow] at this; push_cast at this; linarith
  have h2b : Real.log (2*(b:ℝ)) < 2 * L := by
    rw [hL, ← Real.log_rpow hupos]
    apply Real.log_lt_log (by have : (2:ℝ) ≤ b := by exact_mod_cast hb
                              positivity)
    have : (b:ℝ) + 5 ≤ u := by exact_mod_cast hub
    rw [show ((u:ℝ))^(2:ℝ) = (u:ℝ)^2 by norm_cast]
    nlinarith
  have hb0 : (0:ℝ) < b := by have : (2:ℝ) ≤ b := by exact_mod_cast hb
                             linarith
  have hlhs : Real.log (((2*(b*u))^n:ℕ):ℝ) = n * (Real.log (2*(b:ℝ)) + L) := by
    push_cast; rw [Real.log_pow, ← mul_assoc, Real.log_mul (by positivity) hupos.ne']
  rw [hlhs]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp; positivity
  · have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hdl : 3 * (n:ℝ) < δ * L := by
      have : δ * ((n:ℝ) * ell * Real.log 2) ≤ δ * L := mul_le_mul_of_nonneg_left hLn hδ.le
      nlinarith
    have : (n:ℝ) * (Real.log (2*(b:ℝ)) + L) < 3 * n * L := by nlinarith
    nlinarith

