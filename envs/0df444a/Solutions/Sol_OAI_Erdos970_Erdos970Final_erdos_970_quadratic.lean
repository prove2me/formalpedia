-- Prove2me | solution 1 for OAI.Erdos970.Erdos970Final.erdos_970_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:36:15.621544+00:00
-- url     : https://prove2.me/submissions/fe36660a-dfab-480d-8c21-a51b5e342716

import Mathlib
import Definitions.Def_Jacobsthal
import Theorems.Thm_OAIJacobsthal_exists_jacobsthal_bound_le_sq_div_loglog_sq

theorem solution : OAI.Erdos970.NumberTheoryLean.Targets.JacobsthalQuadratic := by
  obtain ⟨C₀, hC₀, H⟩ := OAIJacobsthal.exists_jacobsthal_bound_le_sq_div_loglog_sq
  have h3 : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have hδ : 0 < Real.log (Real.log 3) := Real.log_pos h3
  refine ⟨C₀ / (Real.log (Real.log 3)) ^ 2, by positivity, fun k hk => ?_⟩
  obtain ⟨m, hm, hle⟩ := H k hk
  refine ⟨m, hm, hle.trans ?_⟩
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h3k : Real.log 3 ≤ Real.log (3 * (k : ℝ)) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hL : Real.log (Real.log 3) ≤ Real.log (Real.log (3 * (k : ℝ))) :=
    Real.log_le_log (by linarith) h3k
  have hsq : (Real.log (Real.log 3)) ^ 2 ≤ (Real.log (Real.log (3 * (k : ℝ)))) ^ 2 :=
    pow_le_pow_left₀ hδ.le hL 2
  have hnum : 0 ≤ C₀ * (k : ℝ) ^ 2 := by positivity
  calc C₀ * (k : ℝ) ^ 2 / (Real.log (Real.log (3 * (k : ℝ)))) ^ 2
      ≤ C₀ * (k : ℝ) ^ 2 / (Real.log (Real.log 3)) ^ 2 :=
        div_le_div_of_nonneg_left hnum (by positivity) hsq
    _ = C₀ / (Real.log (Real.log 3)) ^ 2 * (k : ℝ) ^ 2 := by ring
