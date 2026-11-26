-- Prove2me | solution 1 for MasulloRH.theta_grid_affine_enclosure_of_checked_intervals
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T21:42:13.612125+00:00
-- url     : https://prove2.me/submissions/b8435149-45e8-4dfc-bcce-781160502e46

import Theorems.Thm_MasulloRH_gaussian_window_affine_cell_error_of_curvature
import Theorems.Thm_MasulloRH_central_theta_interval_sound
import Theorems.Thm_MasulloRH_central_interval_arithmetic_sound
import Theorems.Thm_MasulloRH_theta_gaussian_truncation_error
import Theorems.Thm_MasulloRH_theta_reflection
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set MasulloRH MasulloRH.NineShift MasulloRH.CentralInterval MasulloRH.InteriorEvaluator
open MasulloRH.GaussianApproximation MasulloRH.HeightTwoCurvature
private abbrev ok := MasulloRH.central_interval_arithmetic_sound

private theorem single_error (b : Bool) (z : ℝ) :
    ‖theta z - (thetaSix b z : ℂ)‖ ≤ thetaTail b z := by
  let y := arg b z
  let S (x : ℝ) : ℝ := 2 * ∑ k ∈ Finset.range 6,
    let t := ((k : ℝ) + 1) * Real.exp x
    Real.exp (-Real.pi*t^2) - 3*Real.exp (-Real.pi*(2*t)^2) + 2*Real.exp (-Real.pi*(4*t)^2)
  have h := MasulloRH.theta_gaussian_truncation_error y 6
  have h' : ‖theta y - (S y : ℂ)‖ ≤
      12 * Real.exp (-Real.pi * (Real.exp y)^2 * 49) /
        (1 - Real.exp (-Real.pi * (Real.exp y)^2 * 15)) := by
    simpa only [S, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_sum,
      Nat.cast_ofNat, show (6 + 1 : ℝ)^2 = 49 by norm_num,
      show (2*6+3 : ℝ) = 15 by norm_num] using h
  have heq : theta z = (factor b z : ℂ) * theta y := by
    cases b
    · simp [factor, y, arg]
    · exact MasulloRH.theta_reflection z
  have hp : 0 ≤ factor b z := by
    cases b
    · exact zero_le_one
    · exact div_nonneg (Real.exp_pos _).le (by norm_num)
  change ‖theta z - ((factor b z * S y : ℝ) : ℂ)‖ ≤ _
  rw [heq, Complex.ofReal_mul, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hp]
  exact mul_le_mul_of_nonneg_left h' hp


private theorem abs_box {v : Box} {x : ℝ} (hx : Covers v x) : |x| ≤ (mag v : ℝ) := by
  rw [abs_le]
  unfold mag
  push_cast
  exact ⟨by linarith [le_max_left (-(v.1:ℝ)) (v.2:ℝ),hx.1],
         hx.2.trans (le_max_right _ _)⟩

private theorem err_box {v : Box} {x : ℝ} (hx : Covers v x) (n : ℤ) :
    |x-(value n : ℝ)| ≤ (deviation v n : ℝ) :=
  abs_box (ok.sub_ok hx (ok.point_ok _))

theorem solution (j : ℤ) (p : Row) (h : thetaCheck j p = true) : Approx theta j p := by
  let b := refl j
  let d := params b (cellB j)
  let v (n : ℤ) := thetaV (params b (point (grid n)))
  let A := max (deviation (v j) p.l) (deviation (v (j+1)) p.r)
  have ht : 0 < tailDen d ∧ A + mag (thetaD b d)/2048 + tailU d ≤ value p.e :=
    of_decide_eq_true h
  have ep (n : ℤ) : Covers (v n) (thetaSix b (grid n)) :=
    (MasulloRH.central_theta_interval_sound b _ _ (ok.point_ok (grid n))).1
  have atx (x : ℝ) (hx : x ∈ Icc (grid j : ℝ) (grid (j+1) : ℝ)) :=
    MasulloRH.central_theta_interval_sound b (cellB j) x (show Covers (cellB j) x from hx)
  have hlmem : (grid j : ℝ) ∈ Icc (grid j : ℝ) (grid (j+1) : ℝ) := by
    refine ⟨le_rfl,?_⟩;unfold grid;push_cast;linarith
  have hM := (abs_nonneg _).trans (abs_box (atx _ hlmem).2.1)
  apply MasulloRH.gaussian_window_affine_cell_error_of_curvature (thetaSix b) theta j p
    (mag (thetaD b d) : ℝ) (A : ℝ) (tailU d : ℝ) _ hM
  · exact fun x hx => abs_box (atx x hx).2.1
  · exact (err_box (ep j) p.l).trans (by exact_mod_cast le_max_left (deviation (v j) p.l) (deviation (v (j+1)) p.r))
  · exact (err_box (ep (j+1)) p.r).trans (by exact_mod_cast le_max_right (deviation (v j) p.l) (deviation (v (j+1)) p.r))
  · intro x hx
    exact (single_error b x).trans ((atx x hx).2.2 ht.1)
  · exact_mod_cast ht.2
  · cases b <;> unfold thetaSix factor arg <;> simp only [Bool.false_eq_true,↓reduceIte] <;> fun_prop
