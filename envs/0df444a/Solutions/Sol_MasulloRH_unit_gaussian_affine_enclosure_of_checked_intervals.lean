-- Prove2me | solution 1 for MasulloRH.unit_gaussian_affine_enclosure_of_checked_intervals
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T21:42:14.902287+00:00
-- url     : https://prove2.me/submissions/c9d724ba-c011-4096-ad3b-af3584d41956

import Theorems.Thm_MasulloRH_gaussian_window_affine_cell_error_of_curvature
import Theorems.Thm_MasulloRH_central_interval_arithmetic_sound
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

open Set MasulloRH MasulloRH.NineShift MasulloRH.CentralInterval MasulloRH.GaussianApproximation
private abbrev ok := MasulloRH.central_interval_arithmetic_sound

private theorem abs_box {v : Box} {x : ℝ} (hx : Covers v x) : |x| ≤ (mag v : ℝ) := by
  rw [abs_le]
  unfold mag
  push_cast
  exact ⟨by linarith [le_max_left (-(v.1:ℝ)) (v.2:ℝ),hx.1],
         hx.2.trans (le_max_right _ _)⟩

private theorem err_box {v : Box} {x : ℝ} (hx : Covers v x) (n : ℤ) :
    |x-(value n : ℝ)| ≤ (deviation v n : ℝ) :=
  abs_box (ok.sub_ok hx (ok.point_ok _))

private noncomputable def u (x : ℝ) := (1/Real.sqrt Real.pi)*Real.exp (-x^2)
private theorem cf : Covers unitFactor (1/Real.sqrt Real.pi) := by
  have pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hl : (56418958354/100000000000:ℝ) ≤ 1/Real.sqrt Real.pi := by
    apply (le_div_iff₀ pos).2
    have h : Real.sqrt Real.pi ≤ 1/(56418958354/100000000000:ℝ) :=
      (Real.sqrt_le_left (by norm_num)).2 (Real.pi_lt_d20.le.trans (by norm_num))
    linarith
  have hu : 1/Real.sqrt Real.pi ≤ (56418958356/100000000000:ℝ) := by
    apply (div_le_iff₀ pos).2
    have h : 1/(56418958356/100000000000:ℝ) ≤ Real.sqrt Real.pi :=
      Real.le_sqrt_of_sq_le ((by norm_num : (1/(56418958356/100000000000:ℝ))^2 ≤ 3.14159265358979323846).trans Real.pi_gt_d20.le)
    linarith
  dsimp [Covers,unitFactor]; push_cast; exact ⟨hl,hu⟩
private theorem val_ok {z : Box} {x : ℝ} (hx : Covers z x) : Covers (uv z) (u x) :=
  ok.mul_ok cf (ok.exp_ok (ok.neg_ok (ok.sq_ok hx)))
private theorem der (x : ℝ) : HasDerivAt u ((-2*x)*u x) x := by
  have h : HasDerivAt (fun y : ℝ => -y^2) (-2*x) x := by
    apply ((hasDerivAt_id x).pow 2).neg.congr_deriv
    simp
  apply (h.exp.const_mul (1/Real.sqrt Real.pi)).congr_deriv
  unfold u;ring
private theorem dd (x : ℝ) : deriv (deriv u) x = (4*x^2-2)*u x := by
  rw [show deriv u = fun y => (-2*y)*u y from funext fun y => (der y).deriv]
  have h := ((hasDerivAt_id x).const_mul (-2)).mul (der x)
  calc
    _ = (-2*1)*u x+(-2*x)*((-2*x)*u x) := h.deriv
    _ = _ := by ring
private theorem pulse_eq (x : ℝ) : pulse 0 x = (u x:ℂ) := by
  unfold pulse u
  push_cast
  simp
theorem solution (j : ℤ) (p : Row) (h : pulseCheck j p = true) : Approx (pulse 0) j p := by
  let v (n : ℤ) := uv (point (grid n))
  let A := max (deviation (v j) p.l) (deviation (v (j+1)) p.r)
  have ht : A + mag (ud (cellB j))/2048 ≤ value p.e := of_decide_eq_true h
  have ep (n : ℤ) : Covers (v n) (u (grid n)) := val_ok (ok.point_ok _)
  have atx (x : ℝ) (hx : x ∈ Icc (grid j : ℝ) (grid (j+1) : ℝ)) :
      Covers (ud (cellB j)) (deriv (deriv u) x) := by
    rw [dd]
    have hbox : Covers (cellB j) x := hx
    exact ok.mul_ok (ok.sub_ok (ok.mul_ok (ok.point_ok 4) (ok.sq_ok hbox)) (ok.point_ok 2)) (val_ok hbox)
  have hlmem : (grid j : ℝ) ∈ Icc (grid j : ℝ) (grid (j+1) : ℝ) := by
    refine ⟨le_rfl,?_⟩;unfold grid;push_cast;linarith
  apply MasulloRH.gaussian_window_affine_cell_error_of_curvature u (pulse 0) j p
    (mag (ud (cellB j)) : ℝ) (A:ℝ) 0 (by unfold u;fun_prop)
    ((abs_nonneg _).trans (abs_box (atx _ hlmem)))
  · exact fun x hx => abs_box (atx x hx)
  · exact (err_box (ep j) p.l).trans (by exact_mod_cast le_max_left (deviation (v j) p.l) (deviation (v (j+1)) p.r))
  · exact (err_box (ep (j+1)) p.r).trans (by exact_mod_cast le_max_right (deviation (v j) p.l) (deviation (v (j+1)) p.r))
  · intro x _;simp [pulse_eq]
  · rw [add_zero];exact_mod_cast ht
