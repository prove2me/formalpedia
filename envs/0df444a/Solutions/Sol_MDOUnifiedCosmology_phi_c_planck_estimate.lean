-- Prove2me | solution 1 for MDOUnifiedCosmology.phi_c_planck_estimate
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:13:34.529879+00:00
-- url     : https://prove2.me/submissions/d612f19d-8f6a-4cd7-b252-740910cf7bbc

import Definitions.Def_MDOUnifiedCosmology_model
open MDOUnifiedCosmology Set

theorem solution :
    1.3 < Real.sqrt (0.27 / (Real.pi * 0.05)) ∧ Real.sqrt (0.27 / (Real.pi * 0.05)) < 1.32 := by
  have hp := Real.pi_pos
  have hsq := Real.sq_sqrt (show 0 ≤ 0.27 / (Real.pi * 0.05) by positivity)
  have hlo : (1.3 : ℝ)^2 < 0.27 / (Real.pi * 0.05) := by
    apply (lt_div_iff₀ (by positivity)).mpr
    nlinarith [Real.pi_lt_d2]
  have hhi : 0.27 / (Real.pi * 0.05) < (1.32 : ℝ)^2 := by
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith [Real.pi_gt_d2]
  constructor <;> nlinarith [Real.sqrt_nonneg (0.27 / (Real.pi * 0.05))]


