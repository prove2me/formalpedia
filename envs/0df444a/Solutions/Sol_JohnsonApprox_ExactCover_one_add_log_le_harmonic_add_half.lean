-- Prove2me | solution 1 for JohnsonApprox.ExactCover.one_add_log_le_harmonic_add_half
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T22:21:12.470506+00:00
-- url     : https://prove2.me/submissions/d23e7c46-9483-4678-b800-bf6e7244c157

import Mathlib

/-- `2 log t ≤ t - 1/t` for `t ≥ 1`: the difference vanishes at `t = 1` and has
derivative `(1 - 1/t)^2 ≥ 0`. -/
private theorem two_log_le (t : ℝ) (ht : 1 ≤ t) : 2 * Real.log t ≤ t - 1 / t := by
  have hder : ∀ x : ℝ, 0 < x →
      HasDerivAt (fun y : ℝ => y - y⁻¹ - 2 * Real.log y) (1 - -(x ^ 2)⁻¹ - 2 * x⁻¹) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    exact ((hasDerivAt_id x).sub (hasDerivAt_inv hx0)).sub
      ((Real.hasDerivAt_log hx0).const_mul 2)
  have hcont : ContinuousOn (fun y : ℝ => y - y⁻¹ - 2 * Real.log y) (Set.Ici 1) := by
    intro x hx
    have hx0 : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one (Set.mem_Ici.mp hx)
    exact ((hder x hx0).continuousAt).continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun y : ℝ => y - y⁻¹ - 2 * Real.log y)
      (interior (Set.Ici (1:ℝ))) := by
    intro x hx
    rw [interior_Ici] at hx
    have hx0 : (0:ℝ) < x := lt_trans zero_lt_one hx
    exact ((hder x hx0).differentiableAt).differentiableWithinAt
  have hmono : MonotoneOn (fun y : ℝ => y - y⁻¹ - 2 * Real.log y) (Set.Ici 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 1) hcont hdiff ?_
    intro x hx
    rw [interior_Ici] at hx
    have hx0 : (0:ℝ) < x := lt_trans zero_lt_one hx
    rw [(hder x hx0).deriv]
    have hsq : (1 - x⁻¹) ^ 2 = 1 - -(x ^ 2) ⁻¹ - 2 * x⁻¹ := by
      have hx0' : x ≠ 0 := ne_of_gt hx0
      field_simp
      ring
    rw [← hsq]
    exact sq_nonneg _
  have hle : (1:ℝ) - (1:ℝ)⁻¹ - 2 * Real.log 1 ≤ t - t⁻¹ - 2 * Real.log t :=
    hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  norm_num at hle
  rw [one_div]
  linarith

theorem solution (k : ℕ) (hk : 1 ≤ k) :
    1 + Real.log k ≤ (harmonic k : ℝ) + 1 / 2 := by
  have main : ∀ n : ℕ, Real.log ((n : ℝ) + 1) + 1 / 2 + 1 / (2 * ((n : ℝ) + 1))
      ≤ (harmonic (n + 1) : ℝ) := by
    intro n
    induction n with
    | zero => norm_num [harmonic]
    | succ n ih =>
      have hn1 : (0:ℝ) < (n : ℝ) + 1 := by positivity
      have hn2 : (0:ℝ) < (n : ℝ) + 2 := by positivity
      have hharm : (harmonic (n + 1 + 1) : ℝ) = (harmonic (n + 1) : ℝ) + 1 / ((n : ℝ) + 2) := by
        rw [harmonic_succ]
        push_cast
        ring
      have ht : (1:ℝ) ≤ ((n : ℝ) + 2) / ((n : ℝ) + 1) := by
        rw [le_div_iff₀ hn1]; linarith
      have hkey := two_log_le (((n : ℝ) + 2) / ((n : ℝ) + 1)) ht
      rw [Real.log_div (by linarith) (by linarith)] at hkey
      have hrhs : ((n : ℝ) + 2) / ((n : ℝ) + 1) - 1 / (((n : ℝ) + 2) / ((n : ℝ) + 1))
          = 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 2) := by
        field_simp
        ring
      rw [hrhs] at hkey
      have e1 : 1 / (2 * ((n:ℝ) + 1)) = (1 / ((n:ℝ) + 1)) / 2 := by
        rw [div_div, mul_comm]
      have e2 : 1 / (2 * ((n:ℝ) + 2)) = (1 / ((n:ℝ) + 2)) / 2 := by
        rw [div_div, mul_comm]
      rw [e1] at ih
      have hstep : Real.log ((n : ℝ) + 2) + 1 / 2 + 1 / (2 * ((n : ℝ) + 2))
          ≤ (harmonic (n + 1 + 1) : ℝ) := by
        rw [hharm, e2]
        linarith
      push_cast
      rw [show (n:ℝ) + 1 + 1 = (n:ℝ) + 2 by ring]
      exact hstep
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have h := main n
  have hpos : 0 < 1 / (2 * ((n:ℝ) + 1)) := by positivity
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  linarith
