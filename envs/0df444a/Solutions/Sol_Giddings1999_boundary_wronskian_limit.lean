-- Prove2me | solution 1 for Giddings1999.boundary_wronskian_limit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T09:39:49.611386+00:00
-- url     : https://prove2.me/submissions/eae4e3c7-3228-49b0-af00-53c488c9e218

import Mathlib
import Definitions.Def_Giddings1999_AdSModes

open Real Filter Topology
open Giddings1999

theorem solution (d : ℕ) (hd : 1 ≤ d) (m R : ℝ) :
    Tendsto (fun r => tan r ^ (d - 1) *
        (cos r ^ twoHMinus d m R * deriv (fun s => cos s ^ twoHPlus d m R) r
          - cos r ^ twoHPlus d m R * deriv (fun s => cos s ^ twoHMinus d m R) r))
      (𝓝[<] (π / 2)) (𝓝 (-2 * nu d m R)) := by
  set a := twoHMinus d m R
  set b := twoHPlus d m R
  have hab : a + b = d := by simp only [a, b, twoHMinus, twoHPlus]; ring
  have hba : b - a = 2 * nu d m R := by simp only [a, b, twoHMinus, twoHPlus]; ring
  have key : ∀ r ∈ Set.Ioo 0 (π / 2), tan r ^ (d - 1) *
        (cos r ^ a * deriv (fun s => cos s ^ b) r - cos r ^ b * deriv (fun s => cos s ^ a) r)
        = -2 * nu d m R * sin r ^ d := by
    intro r hr
    have hc : 0 < cos r := cos_pos_of_mem_Ioo ⟨by linarith [hr.1, pi_pos], hr.2⟩
    have hD : ∀ e : ℝ, deriv (fun s => cos s ^ e) r = e * cos r ^ (e - 1) * (-sin r) := by
      intro e
      rw [((hasDerivAt_cos r).rpow_const (Or.inl hc.ne')).deriv]; ring
    rw [hD, hD]
    have e1 : cos r ^ a * cos r ^ (b - 1) = cos r ^ ((d:ℝ) - 1) := by
      rw [← rpow_add hc]; congr 1; linarith
    have e2 : cos r ^ b * cos r ^ (a - 1) = cos r ^ ((d:ℝ) - 1) := by
      rw [← rpow_add hc]; congr 1; linarith
    have e3 : cos r ^ ((d:ℝ) - 1) = cos r ^ (d - 1) := by
      rw [← rpow_natCast]; congr 1; push_cast [hd]; ring
    have e4 : tan r ^ (d - 1) * cos r ^ (d - 1) = sin r ^ (d - 1) := by
      rw [tan_eq_sin_div_cos, div_pow, div_mul_cancel₀]; exact pow_ne_zero _ hc.ne'
    have e5 : sin r ^ d = sin r ^ (d - 1) * sin r := by
      rw [← pow_succ]; congr 1; omega
    calc tan r ^ (d - 1) * (cos r ^ a * (b * cos r ^ (b - 1) * -sin r) -
          cos r ^ b * (a * cos r ^ (a - 1) * -sin r))
        = -(b - a) * (tan r ^ (d - 1) * cos r ^ ((d:ℝ) - 1)) * sin r := by
          linear_combination (tan r ^ (d - 1) * (-sin r) * b) * e1 - (tan r ^ (d - 1) * (-sin r) * a) * e2
      _ = -2 * nu d m R * sin r ^ d := by rw [e3, e4, e5, hba]; ring
  have hlim : Tendsto (fun r => -2 * nu d m R * sin r ^ d) (𝓝[<] (π / 2)) (𝓝 (-2 * nu d m R)) := by
    have hcont : Continuous (fun r : ℝ => -2 * nu d m R * sin r ^ d) := by fun_prop
    have := (hcont.tendsto (π / 2)).mono_left
      (nhdsWithin_le_nhds (s := Set.Iio (π/2)))
    simpa using this
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < π / 2 by positivity)] with r hr
  exact (key r hr).symm
