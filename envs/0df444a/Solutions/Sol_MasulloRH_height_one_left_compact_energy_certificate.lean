-- Prove2me | solution 1 for MasulloRH.height_one_left_compact_energy_certificate
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T17:47:44.604854+00:00
-- url     : https://prove2.me/submissions/2e6f9a8d-e150-423f-bcc4-a2a7ce7eb05b

import Definitions.Def_MasulloRH_GaussianThetaApproximation
import Theorems.Thm_MasulloRH_height_one_left_outer_compact_energy_certificate
import Theorems.Thm_MasulloRH_height_one_left_inner_compact_energy_certificate
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open MeasureTheory Set MasulloRH.GaussianApproximation
set_option autoImplicit false

namespace N1LeftQuarterComposition

theorem left_budget_of_two_adjacent_integrals (f : ℝ → ℝ)
    (hOuter : IntegrableOn f (Icc (-4 : ℝ) (-1/4)) ∧
      (∫ x : ℝ in Icc (-4 : ℝ) (-1/4), f x) ≤ (1/320 : ℝ))
    (hInner : IntegrableOn f (Icc (-1/4 : ℝ) 0) ∧
      (∫ x : ℝ in Icc (-1/4 : ℝ) 0, f x) ≤ (7/8000 : ℝ)) :
    IntegrableOn f (Icc (-4 : ℝ) 0) ∧
      (∫ x : ℝ in Icc (-4 : ℝ) 0, f x) ≤ (1/250 : ℝ) := by
  have hL : IntervalIntegrable f volume (-4 : ℝ) (-1/4) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).2 hOuter.1
  have hR : IntervalIntegrable f volume (-1/4 : ℝ) 0 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).2 hInner.1
  have hI : IntegrableOn f (Icc (-4 : ℝ) 0) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).1 (hL.trans hR)
  have h := intervalIntegral.integral_add_adjacent_intervals hL hR
  rw [intervalIntegral.integral_of_le (by norm_num : (-4 : ℝ) ≤ -1/4),
    intervalIntegral.integral_of_le (by norm_num : (-1/4 : ℝ) ≤ 0),
    intervalIntegral.integral_of_le (by norm_num : (-4 : ℝ) ≤ 0)] at h
  simp only [← integral_Icc_eq_integral_Ioc] at h
  exact ⟨hI, by linarith only [h, hOuter.2, hInner.2]⟩
end N1LeftQuarterComposition

theorem solution :
    IntegrableOn (fun x : ℝ =>
      Real.exp (2*(3/4)*x + 2*(7/32)*|x|) *
        ‖residual 1 (fun _ : Fin 1 => (73/50 : ℂ))
          (fun _ : Fin 1 => (3/4 : ℝ)) x‖^2) (Set.Icc (-4) 0) ∧
    (∫ x : ℝ in Set.Icc (-4) 0,
      Real.exp (2*(3/4)*x + 2*(7/32)*|x|) *
        ‖residual 1 (fun _ : Fin 1 => (73/50 : ℂ))
          (fun _ : Fin 1 => (3/4 : ℝ)) x‖^2) ≤ (1/250 : ℝ) := by
  exact N1LeftQuarterComposition.left_budget_of_two_adjacent_integrals _
    MasulloRH.height_one_left_outer_compact_energy_certificate
    MasulloRH.height_one_left_inner_compact_energy_certificate

#print axioms solution
