-- Prove2me | solution 1 for MartOT.Opt.d_strictAnti
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:26:10.160851+00:00
-- url     : https://prove2.me/submissions/b6744c06-a368-496f-909e-24620f3175be

import Mathlib

set_option autoImplicit false

theorem solution (h : ℝ → ℝ) (hd : Differentiable ℝ h)
    (hconv : StrictConvexOn ℝ Set.univ (deriv h)) (ym yp y' l : ℝ)
    (hym : ym < y') (hyp : y' < yp) (hl0 : 0 < l) (hl1 : l < 1)
    (hcomb : l * yp + (1 - l) * ym = y') :
    StrictAnti (fun t : ℝ => l * h (yp - t) + (1 - l) * h (ym - t) - h (y' - t)) := by
  have hder : ∀ (y t : ℝ), HasDerivAt (fun t : ℝ => h (y - t)) (-(deriv h (y - t))) t := by
    intro y t
    have h1 := HasDerivAt.comp t (hd (y - t)).hasDerivAt ((hasDerivAt_id t).const_sub y)
    have h2 : deriv h (y - t) * (-1) = -(deriv h (y - t)) := by ring
    rw [h2] at h1
    exact h1
  have hfd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => l * h (yp - t) + (1 - l) * h (ym - t) - h (y' - t))
      (l * (-(deriv h (yp - t))) + (1 - l) * (-(deriv h (ym - t))) - (-(deriv h (y' - t)))) t := by
    intro t
    exact (((hder yp t).const_mul l).add ((hder ym t).const_mul (1 - l))).sub (hder y' t)
  apply strictAnti_of_deriv_neg
  intro t
  rw [(hfd t).deriv]
  have hne : ym - t ≠ yp - t := by intro h; linarith
  have := hconv.2 (Set.mem_univ (ym - t)) (Set.mem_univ (yp - t)) hne
    (by linarith : 0 < 1 - l) hl0 (by ring)
  have e : (1 - l) • (ym - t) + l • (yp - t) = y' - t := by
    simp only [smul_eq_mul]; linarith
  rw [e] at this
  simp only [smul_eq_mul] at this
  linarith
