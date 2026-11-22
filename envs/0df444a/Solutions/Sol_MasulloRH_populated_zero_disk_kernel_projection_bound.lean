-- Prove2me | solution 1 for MasulloRH.populated_zero_disk_kernel_projection_bound
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T12:41:55.180304+00:00
-- url     : https://prove2.me/submissions/3e322450-7678-4b87-a03c-2932418b4429

import Mathlib
open Metric MeromorphicOn
open scoped InnerProductSpace
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (F : H → ℂ → ℂ) (c : ℂ) (k : H)
    (eval : ∀ g, F g c = ⟪k, g⟫_ℂ)
    (r R M : ℝ) (N : ℕ) (hr : 0 < r) (hR : r < R) (hM : 1 ≤ M)
    (analytic : ∀ g ∈ U, ‖g‖ = 1 → AnalyticOnNhd ℂ (F g) (closedBall c R))
    (bound : ∀ g ∈ U, ‖g‖ = 1 → ∀ z ∈ sphere c R, ‖F g z‖ ≤ M)
    (zeros : ∀ g ∈ U, ‖g‖ = 1 → F g c ≠ 0 →
      (N : ℤ) ≤ ∑ᶠ z, divisor (F g) (closedBall c r) z) :
    ‖U.starProjection k‖ ≤ M * Real.exp (-(N : ℝ) * Real.log (R / r)) := by
  let v := U.starProjection k
  have vm : v ∈ U := U.starProjection_apply_mem k
  have hm : 0 < M := by linarith
  change ‖v‖ ≤ _
  by_cases hv : v = 0
  · rw [hv, norm_zero]; positivity
  have hp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let g : H := ((‖v‖⁻¹ : ℝ) : ℂ) • v
  have gm : g ∈ U := U.smul_mem _ vm
  have gn : ‖g‖ = 1 := by simp [g, norm_smul, abs_of_pos hp, hp.ne']
  have ie : ⟪k,g⟫_ℂ = ⟪v,g⟫_ℂ := by
    have h := Submodule.starProjection_inner_eq_zero (K := U) k g gm
    rw [inner_sub_left, sub_eq_zero] at h
    exact h
  have ge : ‖F g c‖ = ‖v‖ := by
    rw [eval, ie]
    simp only [g, inner_smul_right, inner_self_eq_norm_sq_to_K, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hp, norm_pow]
    field_simp
    change ‖((‖v‖ : ℝ) : ℂ)‖ ^ 2 = ‖v‖ ^ 2
    simp
  have gz : F g c ≠ 0 := by intro h; rw [h, norm_zero] at ge; linarith
  have rp := hr.trans hR
  have a₀ : AnalyticOnNhd ℂ (F g) (closedBall c |R|) := by
    simpa [abs_of_pos rp] using analytic g gm gn
  have a := a₀.sum_divisor_le (r := r) (R := R) (M := M)
    (by simpa [abs_of_pos hr] using hr)
    (by simpa [abs_of_pos hr, abs_of_pos rp] using hR)
    hM gz (by simpa [abs_of_pos rp] using bound g gm gn)
  rw [abs_of_pos hr] at a
  have z := zeros g gm gn gz
  have zz : (N : ℝ) ≤ ((∑ᶠ u, divisor (F g) (closedBall c r) u : ℤ) : ℝ) := by
    exact_mod_cast z
  have lg := Real.log_pos ((one_lt_div hr).2 hR)
  have e := (le_div_iff₀ lg).mp (zz.trans a)
  rw [ge, Real.log_div hm.ne' hp.ne'] at e
  calc
    ‖v‖ = Real.exp (Real.log ‖v‖) := (Real.exp_log hp).symm
    _ ≤ Real.exp (Real.log M + -(N:ℝ)*Real.log (R/r)) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [Real.exp_add, Real.exp_log hm]
