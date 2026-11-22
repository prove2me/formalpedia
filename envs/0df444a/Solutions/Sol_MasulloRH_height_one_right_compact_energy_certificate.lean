-- Prove2me | solution 1 for MasulloRH.height_one_right_compact_energy_certificate
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T17:48:41.827879+00:00
-- url     : https://prove2.me/submissions/74277057-7c2f-49ae-a3a1-177201dee5f0

import Definitions.Def_MasulloRH_GaussianThetaApproximation
import Theorems.Thm_MasulloRH_height_one_zero_to_half_energy_certificate
import Theorems.Thm_MasulloRH_height_one_half_to_four_energy_certificate
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Set
set_option autoImplicit false

namespace N1RightCompositionProof

theorem right_budget_of_two_adjacent_integrals (f : ℝ → ℝ)
    (hl : IntegrableOn f (Icc (0 : ℝ) (1/2)) ∧
      (∫ x : ℝ in Icc (0 : ℝ) (1/2), f x) ≤ (11/5000 : ℝ))
    (hr : IntegrableOn f (Icc (1/2 : ℝ) 4) ∧
      (∫ x : ℝ in Icc (1/2 : ℝ) 4, f x) ≤ (7/2500 : ℝ)) :
    IntegrableOn f (Icc (0 : ℝ) 4) ∧
      (∫ x : ℝ in Icc (0 : ℝ) 4, f x) ≤ (1/200 : ℝ) := by
  have hL : IntervalIntegrable f volume (0 : ℝ) (1/2) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).2 hl.1
  have hR : IntervalIntegrable f volume (1/2 : ℝ) 4 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).2 hr.1
  have hI : IntegrableOn f (Icc (0 : ℝ) 4) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).1 (hL.trans hR)
  have h := intervalIntegral.integral_add_adjacent_intervals hL hR
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1/2),
    intervalIntegral.integral_of_le (by norm_num : (1/2 : ℝ) ≤ 4),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 4)] at h
  simp only [← integral_Icc_eq_integral_Ioc] at h
  exact ⟨hI, by linarith only [h, hl.2, hr.2]⟩
end N1RightCompositionProof

theorem solution :
    MeasureTheory.IntegrableOn (fun x : ℝ =>
      Real.exp (2 * (3 / 4 : ℝ) * x + 2 * (7 / 32 : ℝ) * |x|) *
      ‖MasulloRH.GaussianApproximation.residual 1
        (fun _ : Fin 1 => (73 / 50 : ℂ))
        (fun _ : Fin 1 => (3 / 4 : ℝ)) x‖ ^ 2) (Set.Icc (0 : ℝ) 4) ∧
    (∫ x : ℝ in Set.Icc (0 : ℝ) 4,
      Real.exp (2 * (3 / 4 : ℝ) * x + 2 * (7 / 32 : ℝ) * |x|) *
      ‖MasulloRH.GaussianApproximation.residual 1
        (fun _ : Fin 1 => (73 / 50 : ℂ))
        (fun _ : Fin 1 => (3 / 4 : ℝ)) x‖ ^ 2) ≤ (1 / 200 : ℝ) :=
  N1RightCompositionProof.right_budget_of_two_adjacent_integrals
    (fun x : ℝ => Real.exp (2 * (3 / 4 : ℝ) * x + 2 * (7 / 32 : ℝ) * |x|) *
      ‖MasulloRH.GaussianApproximation.residual 1
        (fun _ : Fin 1 => (73 / 50 : ℂ))
        (fun _ : Fin 1 => (3 / 4 : ℝ)) x‖ ^ 2)
    MasulloRH.height_one_zero_to_half_energy_certificate
    MasulloRH.height_one_half_to_four_energy_certificate
