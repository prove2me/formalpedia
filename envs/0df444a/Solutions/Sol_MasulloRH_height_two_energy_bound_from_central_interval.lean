-- Prove2me | solution 1 for MasulloRH.height_two_energy_bound_from_central_interval
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T13:33:08.230863+00:00
-- url     : https://prove2.me/submissions/8c91966d-7882-4e87-ab74-bbc5e4f97c41

import Theorems.Thm_MasulloRH_height_two_curvature_tail_rows
import Theorems.Thm_MasulloRH_height_two_residual_exterior_bound
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MasulloRH MasulloRH.GaussianApproximation MasulloRH.HeightTwoCurvature MeasureTheory Set

theorem solution :
    let R := residual 2 HeightTwoWitness.coeffs HeightTwoWitness.shifts
    let F := fun x : ℝ => Real.exp (2*(3/4)*x+2*(11/48)*|x|)*‖R x‖^2
    Integrable F ∧ energy (3/4) (11/48) R ≤ (∫ x : ℝ in Icc (-23/8) (7/2), F x) +
      13/800000000 + 1/10000000000 := by
  let R := residual 2 HeightTwoWitness.coeffs HeightTwoWitness.shifts
  let F := fun x : ℝ => Real.exp (2*(3/4)*x+2*(11/48)*|x|)*‖R x‖^2
  change Integrable F ∧ energy (3/4) (11/48) R ≤ (∫ x : ℝ in Icc (-23/8) (7/2), F x) + 13/800000000 + 1/10000000000
  obtain ⟨hi, _, hfar⟩ := MasulloRH.height_two_residual_exterior_bound
  change Integrable F at hi
  refine ⟨hi,?_⟩
  change energy (3/4) (11/48) R - (∫ x : ℝ in Icc (-4) 4, F x) ≤ 1/10000000000 at hfar
  have hstep (j : ℕ) : edge (j+1) - edge j = 1/128 := by simp [edge]; ring
  have seg (a n : ℕ) (h : ∀ j < n, a+j < 1024 ∧ (a+j < 144 ∨ 960 ≤ a+j)) :
      (∫ x in edge a..edge (a+n), F x) ≤ (n:ℝ)/128/100000000 := by
    let e (j : ℕ) := edge (a+j)
    have hz : e 0 = edge a := by simp [e]
    rw [←hz]
    change (∫ x in e 0..e n, F x) ≤ _
    rw [← intervalIntegral.sum_integral_adjacent_intervals (fun _ _ => hi.intervalIntegrable)]
    calc
      _ ≤ ∑ _j ∈ Finset.range n, (1/128 : ℝ) * (1/100000000) := by
        apply Finset.sum_le_sum
        intro j hj
        have hs : e (j+1)-e j = 1/128 := by simpa only [e,Nat.add_assoc] using hstep (a+j)
        have inc : e j ≤ e (j+1) := by linarith
        obtain ⟨hj',hside⟩ := h j (Finset.mem_range.mp hj)
        calc
          _ ≤ ∫ _ in e j..e (j+1), (1/100000000:ℝ) := by
            apply intervalIntegral.integral_mono_on inc hi.intervalIntegrable intervalIntegrable_const
            intro x hx
            apply (MasulloRH.height_two_curvature_tail_rows (a+j) hj' hside).2 x
            simpa only [e,Nat.add_assoc] using hx
          _ = _ := by rw [intervalIntegral.integral_const,hs]; simp
      _ = _ := by simp; ring
  have l := seg 0 144 (by intro j hj; omega)
  have r := seg 960 64 (by intro j hj; omega)
  norm_num [edge] at l r
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (hi.intervalIntegrable : IntervalIntegrable F volume (-4:ℝ) (-23/8))
    (hi.intervalIntegrable : IntervalIntegrable F volume (-23/8:ℝ) (7/2))
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (hi.intervalIntegrable : IntervalIntegrable F volume (-4:ℝ) (7/2))
    (hi.intervalIntegrable : IntervalIntegrable F volume (7/2:ℝ) 4)
  rw [integral_Icc_eq_integral_Ioc, ←intervalIntegral.integral_of_le (by norm_num)] at hfar ⊢
  linarith
