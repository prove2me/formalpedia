-- Prove2me | solution 1 for MasulloRH.quarter_shift_residual_sixth_derivative_cell_bound
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T00:12:05.570111+00:00
-- url     : https://prove2.me/submissions/4c1b5e31-a491-4174-a625-1709eb78dc52

import Theorems.Thm_MasulloRH_quarter_shift_residual_sample_and_truncation_bounds
import Theorems.Thm_MasulloRH_sixth_order_theta_derivative_intervals
import Theorems.Thm_MasulloRH_sixth_order_unit_gaussian_derivative_intervals
import Theorems.Thm_MasulloRH_even_derivative_endpoint_interpolation_bound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set MasulloRH MasulloRH.ThetaDerivativeCertificate MasulloRH.CentralInterval

private theorem chain (k : ℤ) (n : ℕ) (hn : n < 6) (x y : ℝ) :
    HasDerivAt (fun t => selectedJet k n (t-y)) (selectedJet k (n+1) (x-y)) x := by
  by_cases h : active k = true
  · simp only [selectedJet,if_pos h]
    simpa [Function.comp_def] using ((sixth_order_theta_derivative_intervals.1 (branch k) n hn (x-y)).comp x
      ((hasDerivAt_id x).sub_const y))
  · simpa [selectedJet,h] using hasDerivAt_const x (0:ℝ)

private theorem net_der (j : ℤ) (k : ℕ) (hk : k < 6) (x : ℝ) :
    HasDerivAt (residualJet j k) (residualJet j (k+1) x) x := by
  have hs := HasDerivAt.fun_sum (u:=Finset.univ) (fun (i : Fin 25) _ =>
    (chain (j-offset i) k hk x (shift i)).const_mul (coeff i:ℝ))
  exact (sixth_order_unit_gaussian_derivative_intervals.1 k hk x).sub hs

private theorem abs_box {v : Box} {x : ℝ} (hx : Covers v x) : |x| ≤ (mag v : ℝ) := by
  rw [abs_le]
  unfold mag
  push_cast
  exact ⟨by linarith [le_max_left (-(v.1:ℝ)) (v.2:ℝ),hx.1],hx.2.trans (le_max_right _ _)⟩

theorem solution (j : ℤ) (hj : -112 ≤ j) (hk : j < 112) (x : ℝ)
    (hx : x ∈ Icc (centerQ j:ℝ) (centerQ (j+1):ℝ)) : ‖err x‖ ≤ (capQ j:ℝ) := by
  obtain ⟨samples,tail⟩ := quarter_shift_residual_sample_and_truncation_bounds j hj hk
  have ends (i : ℕ) (hi : i < 3) :
      |residualJet j (2*i) (centerQ j)| ≤ (budgetQ j i:ℝ) ∧
      |residualJet j (2*i) (centerQ (j+1))| ≤ (budgetQ j i:ℝ) := by
    have hl : Covers (samplingBox j (2*i)) (centerQ j:ℝ) := by
      simp [samplingBox,show 2*i≠6 by omega,show (2*i)%2=0 by omega,point,Covers]
    have hr : Covers (samplingBox j (2*i+1)) (centerQ (j+1):ℝ) := by
      simp [samplingBox,show 2*i+1≠6 by omega,show (2*i+1)%2=1 by omega,point,Covers]
    have el := abs_box (samples (2*i) (by omega) _ hl)
    have er := abs_box (samples (2*i+1) (by omega) _ hr)
    rw [show orderFor (2*i)=2*i by unfold orderFor;omega] at el
    rw [show orderFor (2*i+1)=2*i by unfold orderFor;omega] at er
    rw [budgetQ,if_neg (by omega),Rat.cast_max]
    exact ⟨el.trans (le_max_left _ _),er.trans (le_max_right _ _)⟩
  have last (t : ℝ) (ht : t ∈ Icc (centerQ j:ℝ) (centerQ (j+1):ℝ)) :
      |residualJet j (2*3) t| ≤ (budgetQ j 3:ℝ) := by
    exact abs_box (samples 6 (by decide) t ht)
  have h := even_derivative_endpoint_interpolation_bound 3 (residualJet j) (fun i => (budgetQ j i:ℝ))
    (centerQ j) (centerQ (j+1)) (fun k h => net_der j k h) ends last x hx
  have spacing : ((centerQ (j+1):ℝ)-(centerQ j:ℝ))^2/8=1/2048 := by
    unfold centerQ;push_cast;ring
  rw [spacing] at h
  have hsur : |residualJet j 0 x| ≤ ((majorant (1/2048:ℚ) (budgetQ j) 3 0:ℚ):ℝ) := by
    simpa [majorant] using h
  calc ‖err x‖ = ‖(err x-(residualJet j 0 x:ℂ))+(residualJet j 0 x:ℂ)‖ := by rw [sub_add_cancel]
       _ ≤ ‖err x-(residualJet j 0 x:ℂ)‖+‖(residualJet j 0 x:ℂ)‖ := norm_add_le _ _
       _ ≤ _ := by
         rw [Complex.norm_real,Real.norm_eq_abs,capQ,Rat.cast_add]
         linarith only [tail x hx,hsur]
