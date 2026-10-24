-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.nonzero_gaussian_integer_scaled_norm_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:09:13.378058+00:00
-- url     : https://prove2.me/submissions/3fb18772-a00e-40c3-9c1c-95b3dd4f3822

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem solution
    {z : Complex} (hz : z ≠ 0) (D : Nat) (hD : 0 < D)
    (a b : Int)
    (hscale : (D : Complex) * z = (a : Complex) + Complex.I * (b : Complex)) :
    1 ≤ (D : Real) * ‖z‖ ∧
      -(Real.log (D : Real)) ≤ Real.log ‖z‖ := by
  let w : Complex := (a : Complex) + Complex.I * (b : Complex)
  have hw : w ≠ 0 := by
    change ((a : Complex) + Complex.I * (b : Complex)) ≠ 0
    rw [← hscale]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)) hz
  have hcoord : ∀ n : Int, n ≠ 0 → (1 : Real) ≤ (n : Real) ^ 2 := by
    intro n hn
    rcases lt_or_gt_of_ne hn with hn' | hn'
    · have hle : n ≤ -1 := by omega
      have hle' : (n : Real) ≤ -1 := by exact_mod_cast hle
      nlinarith
    · have hge : 1 ≤ n := by omega
      have hge' : (1 : Real) ≤ (n : Real) := by exact_mod_cast hge
      nlinarith
  have hsum : (1 : Real) ≤ (a : Real) ^ 2 + (b : Real) ^ 2 := by
    by_cases ha : a = 0
    · by_cases hb : b = 0
      · exact False.elim (hw (by simp [w, ha, hb]))
      · have hb' := hcoord b hb
        nlinarith [sq_nonneg (a : Real)]
    · have ha' := hcoord a ha
      nlinarith [sq_nonneg (b : Real)]
  have hformula : Complex.normSq w = (a : Real) ^ 2 + (b : Real) ^ 2 := by
    dsimp [w]
    rw [show (a : Complex) = ((a : Real) : Complex) by simp,
      show (b : Complex) = ((b : Real) : Complex) by simp,
      mul_comm Complex.I ((b : Real) : Complex)]
    exact Complex.normSq_add_mul_I _ _
  have hw_norm : (1 : Real) ≤ ‖w‖ := by
    have hsquare : (1 : Real) ≤ ‖w‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, hformula]
      exact hsum
    nlinarith [norm_nonneg w]
  have hscaled : (D : Real) * ‖z‖ = ‖w‖ := by
    have h := congrArg norm hscale
    dsimp [w] at h ⊢
    simpa using h
  have hfirst : (1 : Real) ≤ (D : Real) * ‖z‖ := by
    rw [hscaled]
    exact hw_norm
  have hDreal : (0 : Real) < D := by exact_mod_cast hD
  have hnorm_lower : (D : Real)⁻¹ ≤ ‖z‖ := by
    rw [← one_div]
    apply (div_le_iff₀ hDreal).2
    nlinarith [hfirst]
  have hlog := Real.log_le_log (inv_pos.mpr hDreal) hnorm_lower
  rw [Real.log_inv] at hlog
  exact ⟨hfirst, hlog⟩