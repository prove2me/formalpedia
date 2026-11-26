-- Prove2me | solution 1 for MasulloRH.gaussian_window_affine_cell_error_of_curvature
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T21:37:58.165819+00:00
-- url     : https://prove2.me/submissions/b22c1afb-d0d3-4e54-9fce-a8d763f2081a

import Definitions.Def_MasulloRH_NineShiftWindows
import Theorems.Thm_MasulloRH_scalar_curvature_endpoint_bound
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.Linarith

open Set MasulloRH.NineShift

theorem solution (f : ℝ → ℝ) (g : ℝ → ℂ) (j : ℤ) (p : Row) (M A E : ℝ)
    (hf : ContDiff ℝ 2 f) (hM : 0 ≤ M)
    (hdd : ∀ x ∈ Icc (grid j : ℝ) (grid (j+1) : ℝ), |deriv (deriv f) x| ≤ M)
    (hl : |f (grid j) - (value p.l : ℝ)| ≤ A)
    (hr : |f (grid (j+1)) - (value p.r : ℝ)| ≤ A)
    (he : ∀ x ∈ Icc (grid j : ℝ) (grid (j+1) : ℝ), ‖g x - (f x : ℂ)‖ ≤ E)
    (hp : A + M/2048 + E ≤ (value p.e : ℝ)) : Approx g j p := by
  intro s hs hs1
  let l : ℝ := grid j
  let r : ℝ := grid (j+1)
  let x : ℝ := l+s/16
  let a : ℝ := value p.l
  let b : ℝ := value p.r
  let slope := 16*(b-a)
  let chord (y : ℝ) := a+slope*(y-l)
  have hstep : r=l+1/16 := by dsimp [r,l,grid];push_cast;ring
  have hx : x ∈ Icc l r := ⟨by dsimp [x];linarith,by dsimp [x];linarith⟩
  have hc (y : ℝ) : HasDerivAt chord slope y := by
    have h := ((hasDerivAt_id y).sub_const l).const_mul slope
    simpa [chord] using h.const_add a
  have h1 (y : ℝ) := (hf.differentiable (by decide) y).hasDerivAt.sub (hc y)
  have h2 (y : ℝ) := (hf.differentiable_deriv_two y).hasDerivAt.sub_const slope
  have h := MasulloRH.scalar_curvature_endpoint_bound (fun y => f y-chord y)
    (fun y => deriv f y-slope) (deriv (deriv f)) l r M A hM h1 h2 hdd
    (by simpa [chord,l,a] using hl)
    (by have e : chord r=b := by rw [hstep];dsimp [chord,slope];ring
        simpa only [e,b,r] using hr) x hx
  have hline : chord x = line p s := by dsimp [chord,slope,x,a,b,line];ring
  have htri := dist_triangle (g x) (f x : ℂ) (chord x : ℂ)
  simp only [dist_eq_norm] at htri
  rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at htri
  change ‖g x - (line p s : ℂ)‖ ≤ _
  rw [← hline]
  rw [hstep,add_sub_cancel_left] at h
  linarith only [htri,he x hx,h,hp]
