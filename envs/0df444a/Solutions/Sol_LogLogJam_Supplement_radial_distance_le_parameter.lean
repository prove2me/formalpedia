-- Prove2me | solution 1 for LogLogJam.Supplement.radial_distance_le_parameter
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:18:18.868831+00:00
-- url     : https://prove2.me/submissions/6c8e81a5-f537-44ba-a4dd-8095eb650eca

import Mathlib



/-- The square root of one minus the equal-angle squeezed-state fidelity in
Eq. (179) is at most the error in the squeezing parameter, at all energies. -/
theorem solution (r s : ℝ) :
    Real.sqrt (1 - 1 / Real.cosh (r - s)) ≤ |r - s| := by
  let t := r - s
  change Real.sqrt (1 - 1 / Real.cosh t) ≤ |t|
  have hd (x : ℝ) : HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
    have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'
    have heq : Real.tanh = Real.sinh / Real.cosh :=
      funext (fun y => Real.tanh_eq_sinh_div_cosh y)
    have hnum : Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x = 1 := by
      nlinarith [Real.cosh_sq_sub_sinh_sq x]
    rw [heq]
    simpa only [hnum] using h
  have ht : |Real.tanh t| ≤ |t| := by
    have h := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x _ => (hd x).hasDerivWithinAt) (C := 1)
      (fun x _ => by
        rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
        apply (div_le_iff₀ (by positivity : 0 < Real.cosh x ^ 2)).2
        nlinarith [Real.one_le_cosh x])
      (Set.mem_univ (0 : ℝ)) (Set.mem_univ t)
    simpa [Real.norm_eq_abs] using h
  have hs : 1 - 1 / Real.cosh t ≤ Real.tanh t ^ 2 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [(Real.cosh_pos t).ne']
    nlinarith [Real.cosh_sq_sub_sinh_sq t, Real.one_le_cosh t]
  exact (Real.sqrt_le_sqrt hs).trans (by simpa only [Real.sqrt_sq_eq_abs] using ht)
