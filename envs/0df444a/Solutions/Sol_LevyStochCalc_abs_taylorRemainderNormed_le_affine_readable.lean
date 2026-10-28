-- Prove2me | solution 1 for LevyStochCalc.abs_taylorRemainderNormed_le_affine_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:21:48.254549+00:00
-- url     : https://prove2.me/submissions/973b6fc1-73a6-4dec-94cf-a9150d2a06b4

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_TaylorTwoModulus
import Theorems.Thm_LevyStochCalc_abs_sub_taylor_two_le_affine_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/TaylorTwoModulus.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- **Telescoped second-order Taylor expansion against an affine modulus.** -/
theorem solution {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {f'' : E → E →L[ℝ] E →L[ℝ] ℝ} {A K : ℝ} (hA0 : 0 ≤ A) (hK0 : 0 ≤ K)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hf'' : ∀ z w, ‖f'' z - f'' w‖ ≤ A + K * ‖z - w‖) (x : ℕ → E) (m : ℕ) :
    |LevyStochCalc.taylorRemainderNormed f f' f'' x m|
      ≤ A * ∑ i ∈ Finset.range m, ‖x (i + 1) - x i‖ ^ 2
        + K * ∑ i ∈ Finset.range m, ‖x (i + 1) - x i‖ ^ 3 := by
  unfold LevyStochCalc.taylorRemainderNormed
  have htel : f (x m) - f (x 0) = ∑ i ∈ Finset.range m, (f (x (i + 1)) - f (x i)) :=
    (Finset.sum_range_sub (fun i => f (x i)) m).symm
  rw [htel, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have heq : f (x (i + 1)) - f (x i)
      - (f' (x i) (x (i + 1) - x i) + f'' (x i) (x (i + 1) - x i) (x (i + 1) - x i) / 2)
      = f (x (i + 1)) - f (x i) - f' (x i) (x (i + 1) - x i)
        - f'' (x i) (x (i + 1) - x i) (x (i + 1) - x i) / 2 := by ring
  rw [heq]
  exact LevyStochCalc.abs_sub_taylor_two_le_affine_readable hA0 hK0 hf hf' hf'' (x i) (x (i + 1))
