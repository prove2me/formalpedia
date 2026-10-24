-- Prove2me | solution 1 for LevyStochCalc.norm_le_sum_abs_apply_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:08:14.33301+00:00
-- url     : https://prove2.me/submissions/abeebf93-6684-4bc0-935e-dfbd3a6eaff6

import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_CoordDerivative
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_TaylorTwoVector
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.MeanValue

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CoordDerivative.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
open ContinuousLinearMap
variable {n : ℕ}
section Coord
variable {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
  {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
/-- A vector of `Fin n → ℝ` is the sum of its coordinate multiples of the standard basis. -/
theorem LevyStochCalc.sum_single_eq (x : Fin n → ℝ) : ∑ p, (x p) • (Pi.single p 1 : Fin n → ℝ) = x := by
  have h : ∀ p : Fin n, (x p) • (Pi.single p 1 : Fin n → ℝ) = Pi.single p (x p) := by
    intro p
    funext i
    by_cases hi : i = p
    · subst hi; simp
    · simp [hi]
  simp only [h]
  exact Finset.univ_sum_single x
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc in
/-- The operator norm of a functional on `Fin n → ℝ` is at most the sum of the absolute values of
its coordinates. -/
theorem solution (A : (Fin n → ℝ) →L[ℝ] ℝ) :
    ‖A‖ ≤ ∑ p, |A (Pi.single p 1)| := by
  refine A.opNorm_le_bound (Finset.sum_nonneg fun p _ => abs_nonneg _) fun x => ?_
  have hx : A x = ∑ p, x p * A (Pi.single p 1) := by
    conv_lhs => rw [← LevyStochCalc.sum_single_eq x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun p _ => by rw [map_smul]; simp
  rw [Real.norm_eq_abs, hx]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [abs_mul]
  have h1 : |x p| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm x p
  calc |x p| * |A (Pi.single p 1)|
      ≤ ‖x‖ * |A (Pi.single p 1)| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ = |A (Pi.single p 1)| * ‖x‖ := by ring
