-- Prove2me | solution 1 for LevyStochCalc.abs_sub_taylor_two_le_modulus_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:19:12.462626+00:00
-- url     : https://prove2.me/submissions/25128a34-2a08-482b-a4ca-75750c85338d

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_TaylorTwo
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_TaylorTwoModulus
import Theorems.Thm_LevyStochCalc_abs_sub_taylor_one_le_modulus_readable

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/TaylorTwo.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
/-- On the segment between `x` and `y`, no point is further from `x` than `y` is. -/
theorem LevyStochCalc.abs_sub_le_of_mem_uIcc {x y w : ℝ} (hw : w ∈ Set.uIcc x y) : |w - x| ≤ |y - x| := by
  rcases Set.mem_uIcc.mp hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ w - x),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ y - x)]
    linarith
  · rw [abs_of_nonpos (by linarith : w - x ≤ 0), abs_of_nonpos (by linarith : y - x ≤ 0)]
    linarith
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/TaylorTwoModulus.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
/-- **Second-order Taylor against an oscillation bound.** -/
theorem solution {f f' f'' : ℝ → ℝ} {M : ℝ} (hM0 : 0 ≤ M)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    {x y : ℝ} (hM : ∀ w ∈ Set.uIcc x y, |f'' w - f'' x| ≤ M) :
    |f y - f x - f' x * (y - x) - f'' x * (y - x) ^ 2 / 2| ≤ M * |y - x| ^ 2 := by
  have hconv : Convex ℝ (Set.uIcc x y) := convex_uIcc x y
  have hstep1 : ∀ w ∈ Set.uIcc x y, |f' w - f' x - f'' x * (w - x)| ≤ M * |y - x| := by
    intro w hw
    have hsub : Set.uIcc x w ⊆ Set.uIcc x y := Set.uIcc_subset_uIcc Set.left_mem_uIcc hw
    have hloc := LevyStochCalc.abs_sub_taylor_one_le_modulus_readable (f := f') (f' := f'') hf'
      (x := x) (y := w) (fun u hu => hM u (hsub hu))
    exact hloc.trans (mul_le_mul_of_nonneg_left (LevyStochCalc.abs_sub_le_of_mem_uIcc hw) hM0)
  have hF : ∀ w ∈ Set.uIcc x y, HasDerivWithinAt
      (fun z => f z - f x - f' x * (z - x) - f'' x * (z - x) ^ 2 / 2)
      (f' w - f' x - f'' x * (w - x)) (Set.uIcc x y) w := by
    intro w _
    have hA : HasDerivAt (fun z : ℝ => f z - f x) (f' w) w := (hf w).sub_const (f x)
    have hB : HasDerivAt (fun z : ℝ => z - x) (1 : ℝ) w := (hasDerivAt_id w).sub_const x
    have hC : HasDerivAt (fun z : ℝ => f' x * (z - x)) (f' x * 1) w := hB.const_mul (f' x)
    have hD : HasDerivAt (fun z : ℝ => (z - x) ^ 2) (2 * (w - x)) w := by
      have h : HasDerivAt (fun z : ℝ => (z - x) * (z - x)) (1 * (w - x) + (w - x) * 1) w :=
        hB.mul hB
      have hfun : (fun z : ℝ => (z - x) * (z - x)) = fun z : ℝ => (z - x) ^ 2 := by
        funext z; ring
      rw [hfun] at h
      convert h using 1
      ring
    have hE : HasDerivAt (fun z : ℝ => f'' x * (z - x) ^ 2 / 2)
        (f'' x * (2 * (w - x)) / 2) w := (hD.const_mul (f'' x)).div_const 2
    have h1 := (hA.sub hC).sub hE
    have heq : f' w - f' x * 1 - f'' x * (2 * (w - x)) / 2
        = f' w - f' x - f'' x * (w - x) := by ring
    rw [heq] at h1
    exact h1.hasDerivWithinAt
  have hmain := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hF
    (fun w hw => by rw [Real.norm_eq_abs]; exact hstep1 w hw) hconv
    Set.left_mem_uIcc Set.right_mem_uIcc
  simp only [Real.norm_eq_abs] at hmain
  have h0 : f x - f x - f' x * (x - x) - f'' x * (x - x) ^ 2 / 2 = 0 := by ring
  rw [h0, sub_zero] at hmain
  calc |f y - f x - f' x * (y - x) - f'' x * (y - x) ^ 2 / 2|
      ≤ M * |y - x| * |y - x| := hmain
    _ = M * |y - x| ^ 2 := by ring
