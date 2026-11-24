-- Prove2me | solution 1 for GlobalTheory.ExpDivision.hasTemperateGrowth_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:06:19.728787+00:00
-- url     : https://prove2.me/submissions/96fd69fd-b5a8-4aaf-ad9a-312f93e022cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityAsSumExpMinusOne
import Theorems.Thm_GlobalTheory_ExpDivision_hasTemperateGrowth_of_closed
import Theorems.Thm_GlobalTheory_ExpDivision_hasTemperateGrowth_deriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.ExpDivision
namespace GlobalTheory.ExpDivision
theorem _root_.solution {E g : ℝ → ℂ} (hE : E.HasTemperateGrowth)
    (h0 : ∀ x, E x ≠ 0) {N : ℕ} {M : ℝ} (hM : ∀ x, ‖(E x)⁻¹‖ ≤ M * (1 + ‖x‖) ^ N)
    (hg : g.HasTemperateGrowth) : (fun x => g x / E x).HasTemperateGrowth := by
  have hEd : Differentiable ℝ E := hE.1.differentiable (by simp)
  refine hasTemperateGrowth_of_closed
    {f | ∃ (m : ℕ) (u : ℝ → ℂ), u.HasTemperateGrowth ∧ f = fun x => u x / E x ^ m} ?_ ?_ ?_
    ⟨1, g, hg, by simp⟩
  · rintro f ⟨m, u, hu, rfl⟩
    have hud : Differentiable ℝ u := hu.1.differentiable (by simp)
    exact hud.div (hEd.pow m) fun x => pow_ne_zero _ (h0 x)
  · rintro f ⟨m, u, hu, rfl⟩
    have hud : Differentiable ℝ u := hu.1.differentiable (by simp)
    have hp : (fun x => E x ^ m).HasTemperateGrowth := hE.pow m
    have hpd : Differentiable ℝ (fun x => E x ^ m) := hp.1.differentiable (by simp)
    refine ⟨m * 2, fun x => deriv u x * E x ^ m - u x * deriv (fun x => E x ^ m) x,
      ((hasTemperateGrowth_deriv hu).mul hp).sub (hu.mul (hasTemperateGrowth_deriv hp)), ?_⟩
    funext x
    rw [pow_mul]
    exact deriv_fun_div (hud x) (hpd x) (pow_ne_zero _ (h0 x))
  · rintro f ⟨m, u, hu, rfl⟩
    obtain ⟨k, C, h⟩ := hu.2 0
    refine ⟨k + N * m, C * M ^ m, fun x => ?_⟩
    have h1 : ‖u x‖ ≤ C * (1 + ‖x‖) ^ k := by simpa using h x
    have h2 := hM x
    have h3 : 0 ≤ C * (1 + ‖x‖) ^ k := (norm_nonneg _).trans h1
    calc ‖u x / E x ^ m‖ = ‖u x‖ * ‖(E x)⁻¹‖ ^ m := by
          rw [div_eq_mul_inv, norm_mul, ← inv_pow, norm_pow]
      _ ≤ (C * (1 + ‖x‖) ^ k) * (M * (1 + ‖x‖) ^ N) ^ m := by gcongr
      _ = _ := by rw [mul_pow, ← pow_mul, pow_add]; ring
end GlobalTheory.ExpDivision
