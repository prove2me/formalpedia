-- Prove2me | solution 1 for LevyStochCalc.abs_sub_taylor_two_le_affine_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:34:22.921925+00:00
-- url     : https://prove2.me/submissions/ab36ef7a-b309-4642-a22e-1cdc54b512b6

import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_TaylorTwoVector
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Theorems.Thm_LevyStochCalc_abs_sub_taylor_two_le_modulus_normed_408915f

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/TaylorTwoModulus.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc in
/-- **Second-order Taylor against an affine modulus.** If the second derivative satisfies
`‖f'' z − f'' w‖ ≤ A + K‖z − w‖`, the second-order Taylor remainder is at most
`A‖y − x‖² + K‖y − x‖³`. -/
theorem solution {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {f'' : E → E →L[ℝ] E →L[ℝ] ℝ} {A K : ℝ} (hA0 : 0 ≤ A) (hK0 : 0 ≤ K)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hf'' : ∀ z w, ‖f'' z - f'' w‖ ≤ A + K * ‖z - w‖) (x y : E) :
    |f y - f x - f' x (y - x) - f'' x (y - x) (y - x) / 2|
      ≤ A * ‖y - x‖ ^ 2 + K * ‖y - x‖ ^ 3 := by
  have hM0 : (0 : ℝ) ≤ A + K * ‖y - x‖ := by positivity
  have hM : ∀ z ∈ segment ℝ x y, ‖f'' z - f'' x‖ ≤ A + K * ‖y - x‖ := by
    intro z hz
    rw [segment_eq_image' ℝ x y] at hz
    obtain ⟨θ, hθ, rfl⟩ := hz
    have hnorm : ‖x + θ • (y - x) - x‖ = θ * ‖y - x‖ := by
      have hsub : x + θ • (y - x) - x = θ • (y - x) := by module
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1]
    refine (hf'' _ x).trans ?_
    rw [hnorm]
    have : K * (θ * ‖y - x‖) ≤ K * ‖y - x‖ := by
      refine mul_le_mul_of_nonneg_left ?_ hK0
      nlinarith [norm_nonneg (y - x), hθ.1, hθ.2]
    linarith
  have hmain := LevyStochCalc.abs_sub_taylor_two_le_modulus_normed_408915f hM0 hf hf' hM
  refine hmain.trans (le_of_eq ?_)
  ring
