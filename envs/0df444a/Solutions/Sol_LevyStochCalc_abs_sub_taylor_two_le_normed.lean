-- Prove2me | solution 1 for LevyStochCalc.abs_sub_taylor_two_le_normed
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T06:00:17.003866+00:00
-- url     : https://prove2.me/submissions/9366a11f-da7a-4f24-bd54-ad2ace6dd1e5

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Mul

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Second-order Taylor bound with a Lipschitz second derivative

For a twice-differentiable real function whose second derivative is `K`-Lipschitz, the
second-order Taylor polynomial approximates the function to within `K|y − x|³`.

## Main statements

* `LevyStochCalc.abs_sub_taylor_one_le` — the first-order Taylor remainder bound.
* `LevyStochCalc.abs_sub_taylor_two_le` — the second-order Taylor remainder bound.
* `LevyStochCalc.abs_sub_sum_taylor_two_le` — the telescoped form along a sequence.
* `LevyStochCalc.taylorRemainder` — the telescoped remainder as a function of the sequence.
* `LevyStochCalc.abs_taylorRemainder_le` — its bound.
-/

namespace AuxT

/-- On the segment between `x` and `y`, no point is further from `x` than `y` is. -/
theorem abs_sub_le_of_mem_uIcc {x y w : ℝ} (hw : w ∈ Set.uIcc x y) : |w - x| ≤ |y - x| := by
  rcases Set.mem_uIcc.mp hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ w - x),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ y - x)]
    linarith
  · rw [abs_of_nonpos (by linarith : w - x ≤ 0), abs_of_nonpos (by linarith : y - x ≤ 0)]
    linarith
/-- **First-order Taylor remainder for a Lipschitz derivative.** -/
theorem abs_sub_taylor_one_le {f f' : ℝ → ℝ} {K : ℝ} (hK0 : 0 ≤ K)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ u v : ℝ, |f' u - f' v| ≤ K * |u - v|)
    (x y : ℝ) : |f y - f x - f' x * (y - x)| ≤ K * |y - x| * |y - x| := by
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
  have hbound : ∀ w ∈ Set.uIcc x y, ‖f' w - f' x‖ ≤ K * |y - x| := by
    intro w hw
    rw [Real.norm_eq_abs]
    exact (hf' w x).trans (mul_le_mul_of_nonneg_left (abs_sub_le_of_mem_uIcc hw) hK0)
  have hmain := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hg hbound hconv
    Set.left_mem_uIcc Set.right_mem_uIcc
  simpa [Real.norm_eq_abs] using hmain
end AuxT

open AuxT in
theorem taylor1d {f f' f'' : ℝ → ℝ} {K : ℝ} (hK0 : 0 ≤ K)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : ∀ u v : ℝ, |f'' u - f'' v| ≤ K * |u - v|) (x y : ℝ) :
    |f y - f x - f' x * (y - x) - f'' x * (y - x) ^ 2 / 2| ≤ K * |y - x| ^ 3 := by
  have hconv : Convex ℝ (Set.uIcc x y) := convex_uIcc x y
  have hg : ∀ w ∈ Set.uIcc x y, HasDerivWithinAt
      (fun z => f z - f x - f' x * (z - x) - f'' x * (z - x) ^ 2 / 2)
      (f' w - f' x - f'' x * (w - x)) (Set.uIcc x y) w := by
    intro w _
    have hB : HasDerivAt (fun z : ℝ => z - x) (1 : ℝ) w := (hasDerivAt_id w).sub_const x
    have hC : HasDerivAt (fun z : ℝ => f' x * (z - x)) (f' x * 1) w := hB.const_mul (f' x)
    have hD : HasDerivAt (fun z : ℝ => (z - x) ^ 2) (((2:ℕ):ℝ) * (w - x) ^ (2 - 1) * 1) w :=
      hB.pow 2
    have hE : HasDerivAt (fun z : ℝ => f'' x * (z - x) ^ 2 / 2)
        (f'' x * (((2:ℕ):ℝ) * (w - x) ^ (2 - 1) * 1) / 2) w := (hD.const_mul (f'' x)).div_const 2
    have h1 := (((hf w).sub_const (f x)).sub hC).sub hE
    have h2 : HasDerivAt (fun z => f z - f x - f' x * (z - x) - f'' x * (z - x) ^ 2 / 2)
        (f' w - f' x * 1 - f'' x * (((2:ℕ):ℝ) * (w - x) ^ (2 - 1) * 1) / 2) w := h1
    exact (h2.congr_deriv (by push_cast; ring)).hasDerivWithinAt
  have hbound : ∀ w ∈ Set.uIcc x y, ‖f' w - f' x - f'' x * (w - x)‖ ≤ K * |y - x| ^ 2 := by
    intro w hw
    rw [Real.norm_eq_abs]
    have h := abs_sub_taylor_one_le hK0 hf' hf'' x w
    have hw' := abs_sub_le_of_mem_uIcc hw
    have h0 : 0 ≤ |w - x| := abs_nonneg _
    calc |f' w - f' x - f'' x * (w - x)| ≤ K * |w - x| * |w - x| := h
      _ ≤ K * |y - x| * |y - x| := by gcongr
      _ = K * |y - x| ^ 2 := by ring
  have hmain := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hg hbound hconv
    Set.left_mem_uIcc Set.right_mem_uIcc
  simp only [Real.norm_eq_abs, sub_self, mul_zero, zero_pow two_ne_zero, zero_div, sub_zero] at hmain
  calc |f y - f x - f' x * (y - x) - f'' x * (y - x) ^ 2 / 2| ≤ K * |y - x| ^ 2 * |y - x| := hmain
    _ = K * |y - x| ^ 3 := by ring

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem solution {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {f'' : E → E →L[ℝ] E →L[ℝ] ℝ} {K : ℝ} (hK0 : 0 ≤ K)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hf'' : ∀ z w, ‖f'' z - f'' w‖ ≤ K * ‖z - w‖) (x y : E) :
    |f y - f x - f' x (y - x) - f'' x (y - x) (y - x) / 2| ≤ K * ‖y - x‖ ^ 3 := by
  set v := y - x with hv
  have hl : ∀ s : ℝ, HasDerivAt (fun s : ℝ => x + s • v) v s := fun s => by
    simpa using ((hasDerivAt_id s).smul_const v).const_add x
  have hg : ∀ s : ℝ, HasDerivAt (fun s : ℝ => f (x + s • v)) (f' (x + s • v) v) s :=
    fun s => (hf _).comp_hasDerivAt s (hl s)
  have hg' : ∀ s : ℝ, HasDerivAt (fun s : ℝ => f' (x + s • v) v) (f'' (x + s • v) v v) s := by
    intro s
    have h1 := (hf' (x + s • v)).comp_hasDerivAt s (hl s)
    have h2 := h1.clm_apply (hasDerivAt_const s v)
    simpa using h2
  have hL : ∀ u w : ℝ, |f'' (x + u • v) v v - f'' (x + w • v) v v| ≤
      (K * ‖v‖ ^ 3) * |u - w| := by
    intro u w
    have e : f'' (x + u • v) v v - f'' (x + w • v) v v = (f'' (x + u • v) - f'' (x + w • v)) v v := by
      simp
    rw [e, ← Real.norm_eq_abs]
    have e2 : (x + u • v) - (x + w • v) = (u - w) • v := by
      rw [add_sub_add_left_eq_sub, sub_smul]
    calc ‖(f'' (x + u • v) - f'' (x + w • v)) v v‖
        ≤ ‖f'' (x + u • v) - f'' (x + w • v)‖ * ‖v‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ K * ‖(x + u • v) - (x + w • v)‖ * ‖v‖ * ‖v‖ := by gcongr; exact hf'' _ _
      _ = (K * ‖v‖ ^ 3) * |u - w| := by
          rw [e2, norm_smul, Real.norm_eq_abs]; ring
  have h := taylor1d (mul_nonneg hK0 (by positivity)) hg hg' hL 0 1
  have hy : x + (1:ℝ) • v = y := by rw [one_smul, hv, add_sub_cancel]
  simp only [zero_smul, add_zero, sub_zero, one_pow, mul_one, abs_one, hy] at h
  exact h
end
