-- Prove2me | solution 1 for LevyStochCalc.abs_sub_taylor_one_le_modulus_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:18:31.34701+00:00
-- url     : https://prove2.me/submissions/3e0e0593-e568-4f1f-8592-3bf446bc63c2

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_TaylorTwoModulus

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/TaylorTwoModulus.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
/-- **First-order Taylor against an oscillation bound.** -/
theorem solution {f f' : ℝ → ℝ} {M : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) {x y : ℝ}
    (hM : ∀ w ∈ Set.uIcc x y, |f' w - f' x| ≤ M) :
    |f y - f x - f' x * (y - x)| ≤ M * |y - x| := by
  have hconv : Convex ℝ (Set.uIcc x y) := convex_uIcc x y
  have hg : ∀ w ∈ Set.uIcc x y, HasDerivWithinAt (fun z => f z - f x - f' x * (z - x))
      (f' w - f' x) (Set.uIcc x y) w := by
    intro w _
    have hA : HasDerivAt (fun z : ℝ => f z - f x) (f' w) w := (hf w).sub_const (f x)
    have hB : HasDerivAt (fun z : ℝ => z - x) (1 : ℝ) w := (hasDerivAt_id w).sub_const x
    have hC : HasDerivAt (fun z : ℝ => f' x * (z - x)) (f' x * 1) w := hB.const_mul (f' x)
    have h1 : HasDerivAt (fun z : ℝ => f z - f x - f' x * (z - x)) (f' w - f' x * 1) w :=
      hA.sub hC
    rw [mul_one] at h1
    exact h1.hasDerivWithinAt
  have hbound : ∀ w ∈ Set.uIcc x y, ‖f' w - f' x‖ ≤ M := by
    intro w hw
    rw [Real.norm_eq_abs]
    exact hM w hw
  have hmain := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hg hbound hconv
    Set.left_mem_uIcc Set.right_mem_uIcc
  simpa [Real.norm_eq_abs] using hmain
