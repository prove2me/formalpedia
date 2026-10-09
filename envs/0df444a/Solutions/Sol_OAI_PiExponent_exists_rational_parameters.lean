-- Prove2me | solution 1 for OAI.PiExponent.exists_rational_parameters
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T09:04:12.561464+00:00
-- url     : https://prove2.me/submissions/1b4b557a-fe44-4c25-8298-0cd1963dcc14

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic



theorem solution (ν : ℝ) (hν : 2 < ν) :
    ∃ θ A B C : ℚ,
      0 < (θ : ℝ) ∧ (θ : ℝ) < A ∧ (A : ℝ) < B ∧ (B : ℝ) < 1 ∧
      ν * ((A : ℝ) - θ) > 1 - θ ∧
      1 < (C : ℝ) ∧ (B : ℝ) < 1 / C ∧
      (B : ℝ) < C * θ ∧ (C : ℝ) * θ < 1 := by
  have hνpos : 0 < ν := by linarith
  have hdiv : 1 / ν < (1 / 2 : ℝ) :=
    (div_lt_iff₀ hνpos).2 (by linarith)
  obtain ⟨b, hbl, hbu⟩ := exists_rat_btwn (show (1 / 2 : ℝ) < 1 - 1 / ν by linarith)
  have hbpos : 0 < (b : ℝ) := by linarith
  have hb1 : (b : ℝ) < 1 := by
    have := one_div_pos.mpr hνpos
    linarith
  have hνb : ν * (b : ℝ) < ν - 1 := calc
    _ < ν * (1 - 1 / ν) := mul_lt_mul_of_pos_left hbu hνpos
    _ = ν - 1 := by field_simp
  have hcoeff : 0 < ν * (1 - (b : ℝ)) - 1 := by nlinarith
  have hδtop : 0 < min (1 : ℝ) ((2 * (b : ℝ) - 1) / ((b : ℝ) * b)) :=
    lt_min (by norm_num) (div_pos (by linarith) (mul_pos hbpos hbpos))
  obtain ⟨δ, hδpos, hδtop⟩ := exists_rat_btwn hδtop
  have hδ1 : (δ : ℝ) < 1 := lt_of_lt_of_le hδtop (min_le_left _ _)
  have hδsmall : (δ : ℝ) < (2 * (b : ℝ) - 1) / ((b : ℝ) * b) :=
    lt_of_lt_of_le hδtop (min_le_right _ _)
  have hδprod : (δ : ℝ) * ((b : ℝ) * b) < 2 * (b : ℝ) - 1 :=
    (lt_div_iff₀ (mul_pos hbpos hbpos)).mp hδsmall
  let θ : ℚ := 1 - δ
  let A : ℚ := 1 - b * δ
  have hθcast : (θ : ℝ) = 1 - (δ : ℝ) := by simp [θ]
  have hAcast : (A : ℝ) = 1 - (b : ℝ) * δ := by simp [A]
  have hθpos : 0 < (θ : ℝ) := by rw [hθcast]; linarith
  have hθA : (θ : ℝ) < A := by
    rw [hθcast, hAcast]
    nlinarith [mul_pos (sub_pos.mpr hb1) hδpos]
  have hApos : 0 < (A : ℝ) := lt_trans hθpos hθA
  have hA1 : (A : ℝ) < 1 := by
    rw [hAcast]
    nlinarith [mul_pos hbpos hδpos]
  have hAsq : (A : ℝ) ^ 2 < θ := by
    rw [hAcast, hθcast]
    nlinarith [mul_pos hδpos (sub_pos.mpr hδprod)]
  have hgap : 1 - (θ : ℝ) < ν * ((A : ℝ) - θ) := by
    rw [hAcast, hθcast]
    nlinarith [mul_pos hcoeff hδpos]
  have hCinterval : (A : ℝ) / θ < 1 / A := by
    apply (div_lt_div_iff₀ hθpos hApos).2
    nlinarith
  obtain ⟨C, hClo, hChi⟩ := exists_rat_btwn hCinterval
  have hC1 : 1 < (C : ℝ) := by
    have : (1 : ℝ) < (A : ℝ) / θ := (lt_div_iff₀ hθpos).2 (by simpa using hθA)
    exact lt_trans this hClo
  have hCpos : 0 < (C : ℝ) := by linarith
  have hACθ : (A : ℝ) < (C : ℝ) * θ := (div_lt_iff₀ hθpos).mp hClo
  have hCA : (C : ℝ) * A < 1 := (lt_div_iff₀ hApos).mp hChi
  have hAinvC : (A : ℝ) < 1 / C := (lt_div_iff₀ hCpos).2 (by nlinarith)
  have hCθ1 : (C : ℝ) * θ < 1 := by nlinarith [mul_lt_mul_of_pos_left hθA hCpos]
  have hBinterval : (A : ℝ) < min (1 / (C : ℝ)) ((C : ℝ) * θ) :=
    lt_min hAinvC hACθ
  obtain ⟨B, hBlo, hBhi⟩ := exists_rat_btwn hBinterval
  have hBinv : (B : ℝ) < 1 / C := lt_of_lt_of_le hBhi (min_le_left _ _)
  have hBCθ : (B : ℝ) < (C : ℝ) * θ := lt_of_lt_of_le hBhi (min_le_right _ _)
  exact ⟨θ, A, B, C, hθpos, hθA, hBlo, lt_trans hBCθ hCθ1,
    hgap, hC1, hBinv, hBCθ, hCθ1⟩

#print axioms solution
