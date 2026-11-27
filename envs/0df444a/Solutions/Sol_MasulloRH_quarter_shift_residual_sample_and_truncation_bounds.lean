-- Prove2me | solution 1 for MasulloRH.quarter_shift_residual_sample_and_truncation_bounds
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T00:10:55.237273+00:00
-- url     : https://prove2.me/submissions/d79aef7d-bce6-4f89-8d8d-49a296ac0290

import Theorems.Thm_MasulloRH_quarter_shift_theta_derivative_table_first_quarter
import Theorems.Thm_MasulloRH_quarter_shift_theta_derivative_table_second_quarter
import Theorems.Thm_MasulloRH_quarter_shift_theta_derivative_table_third_quarter
import Theorems.Thm_MasulloRH_quarter_shift_theta_derivative_table_fourth_quarter
import Theorems.Thm_MasulloRH_quarter_shift_gaussian_derivative_and_weight_tables
import Theorems.Thm_MasulloRH_sixth_order_theta_derivative_intervals
import Theorems.Thm_MasulloRH_sixth_order_unit_gaussian_derivative_intervals
import Theorems.Thm_MasulloRH_central_interval_arithmetic_sound
import Theorems.Thm_MasulloRH_theta_norm_le_dyadic_on_tails
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set MasulloRH MasulloRH.ThetaDerivativeCertificate MasulloRH.CentralInterval
open MasulloRH.GaussianApproximation MasulloRH.InteriorEvaluator
private abbrev ok := MasulloRH.central_interval_arithmetic_sound

private theorem transfers {v w : Box} {x : ℝ} (h : fits v w = true) (hx : Covers v x) :
    Covers w x := by
  obtain ⟨h1,h2⟩ := of_decide_eq_true h
  exact ⟨(Rat.cast_le.mpr h1).trans hx.1,hx.2.trans (Rat.cast_le.mpr h2)⟩

private theorem theta_table (j : ℤ) (h : active j = true) : thetaCheck j = true := by
  have hr : -48 ≤ j ∧ j < 24 := of_decide_eq_true h
  by_cases a : j < -30
  · exact quarter_shift_theta_derivative_table_first_quarter _ hr.1 a
  by_cases b : j < -12
  · exact quarter_shift_theta_derivative_table_second_quarter _ (by omega) b
  by_cases c : j < 6
  · exact quarter_shift_theta_derivative_table_third_quarter _ (by omega) c
  exact quarter_shift_theta_derivative_table_fourth_quarter _ (by omega) hr.2

private theorem theta_sample (j : ℤ) (k : ℕ) (hk : k < 7) (x : ℝ) (hx : Covers (samplingBox j k) x) :
    Covers (col (thetaRow j) k) (selectedJet j (orderFor k) x) := by
  by_cases h : active j = true
  · have hb := (Bool.and_eq_true_iff.mp (theta_table j h)).1
    have hfit := List.all_eq_true.mp hb k (List.mem_range.mpr hk)
    rw [selectedJet,if_pos h]
    exact transfers hfit (sixth_order_theta_derivative_intervals.2.1 _ _ _ _ hx)
  · simp [selectedJet,thetaRow,h,col,zeroRow,decoded,Covers]

private theorem moved (j : ℤ) (i : Fin 25) (k : ℕ) (x : ℝ) (hx : Covers (samplingBox j k) x) :
    Covers (samplingBox (j-offset i) k) (x-(shift i:ℝ)) := by
  by_cases h : k=6
  · simp only [samplingBox,h,if_pos,cellBox,centerQ,Covers,shift] at hx ⊢
    push_cast at hx ⊢
    constructor <;> linarith only [hx.1,hx.2]
  · simp only [samplingBox,h,point,centerQ,Covers,shift] at hx ⊢
    push_cast at hx ⊢
    constructor <;> linarith only [hx.1,hx.2]

private theorem theta_tail (j : ℤ) (x : ℝ) (hx : Covers (cellBox j) x) :
    ‖theta x-(selectedJet j 0 x:ℂ)‖ ≤ (tailQ (thetaRow j):ℝ) := by
  by_cases h : active j = true
  · have hd : 0 < tailDen (params (branch j) (cellBox j)) ∧
        tailU (params (branch j) (cellBox j)) ≤ tailQ (thetaRow j) :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp (theta_table j h)).2
    rw [selectedJet,if_pos h]
    exact (sixth_order_theta_derivative_intervals.2.2 _ _ _ hx hd.1).trans (Rat.cast_le.mpr hd.2)
  · have hn : ¬(-48 ≤ j ∧ j < 24) := fun hh => h (decide_eq_true hh)
    have ht : x ≤ -3 ∨ 3/2 ≤ x := by
      change (centerQ j:ℝ) ≤ x ∧ x ≤ (centerQ (j+1):ℝ) at hx
      unfold centerQ at hx
      push_cast at hx
      by_cases hj : j < -48
      · left;have hcast : (j:ℝ) ≤ -49 := by exact_mod_cast (show j ≤ -49 by omega)
        linarith only [hx.2,hcast]
      · right;have hcast : (24:ℝ) ≤ j := by exact_mod_cast (show 24 ≤ j by omega)
        linarith only [hx.1,hcast]
    simpa [selectedJet,thetaRow,h,zeroRow,tailQ,ThetaDerivativeCertificate.S] using
      (theta_norm_le_dyadic_on_tails x ht).trans (by norm_num : (1:ℝ)/2^64 ≤ 1/10000000000)

theorem solution (j : ℤ) (hj : -112 ≤ j) (hk : j < 112) :
    (∀ k < 7, ∀ x : ℝ, Covers (samplingBox j k) x →
      Covers (netBox j k) (residualJet j (orderFor k) x)) ∧
    (∀ x : ℝ, Covers (cellBox j) x →
      ‖err x-(residualJet j 0 x:ℂ)‖ ≤ (tailSumQ j:ℝ)) := by
  constructor
  · intro k h x hx
    have hc := (Bool.and_eq_true_iff.mp (quarter_shift_gaussian_derivative_and_weight_tables j hj hk)).1
    have hfit := List.all_eq_true.mp hc k (List.mem_range.mpr h)
    apply ok.sub_ok (transfers hfit (sixth_order_unit_gaussian_derivative_intervals.2.1 _ _ _ hx))
    apply ok.sum_ok
    intro i
    exact ok.mul_ok (ok.point_ok _) (theta_sample _ k h _ (moved j i k x hx))
  · intro x hx
    let a (i : Fin 25) : ℝ := coeff i
    let v (i : Fin 25) : ℂ := theta (x-(shift i:ℝ))
    let u (i : Fin 25) : ℝ := selectedJet (j-offset i) 0 (x-(shift i:ℝ))
    have ha (i : Fin 25) : 0 ≤ a i := by
      change 0 ≤ (coeff i:ℝ)
      exact_mod_cast (show ∀ i : Fin 25, 0 ≤ coeff i by decide +kernel) i
    have ht (i : Fin 25) : ‖v i-(u i:ℂ)‖ ≤ (tailQ (thetaRow (j-offset i)):ℝ) :=
      theta_tail _ _ (moved j i 6 x hx)
    have hz : ‖∑ i : Fin 25, (a i:ℂ)*(v i-(u i:ℂ))‖ ≤
        ∑ i : Fin 25, a i*(tailQ (thetaRow (j-offset i)):ℝ) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (ha i)]
      exact mul_le_mul_of_nonneg_left (ht i) (ha i)
    have he : err x-(residualJet j 0 x:ℂ) = -(∑ i : Fin 25, (a i:ℂ)*(v i-(u i:ℂ))) := by
      dsimp only [err,GaussianApproximation.residual,residualJet,v,u,a]
      rw [sixth_order_unit_gaussian_derivative_intervals.2.2]
      simp only [Complex.ofReal_sub,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_ratCast,
        mul_sub,Finset.sum_sub_distrib]
      ring
    rw [he,norm_neg]
    simpa only [tailSumQ,Rat.cast_sum,Rat.cast_mul,a] using hz
