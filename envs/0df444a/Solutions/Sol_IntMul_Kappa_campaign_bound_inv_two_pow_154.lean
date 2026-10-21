-- Prove2me | solution 1 for IntMul.Kappa.campaign_bound_inv_two_pow_154
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T21:09:41.740487+00:00
-- url     : https://prove2.me/submissions/9503f71e-86f6-4505-9eb3-1ecf9d8ca9ec

import Definitions.Def_IntMul_MultitapeModel
import Theorems.Thm_IntMul_OpenAI_R154_machine
import Theorems.Thm_IntMul_OpenAI_R154_params_eventually
import Theorems.Thm_IntMul_OpenAI_R154_kappaBound_of_table

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- `KappaBound (2⁻¹⁵⁴)` from the machine milestone, the parameter bounds and the reduction. -/
theorem solution : IntMul.KappaBound ((1 / 2 ^ 154) : ℝ) := by
  obtain ⟨M, hcorr, C₀, hC₀, A, n₁, ht⟩ := IntMul.OpenAI.R154.machine
  obtain ⟨n₂, hp⟩ := IntMul.OpenAI.R154.params_eventually
  exact IntMul.OpenAI.R154.kappaBound_of_table M hcorr (max n₁ n₂) A C₀ hC₀
    IntMul.OpenAI.Glue.VP (fun n => (IntMul.OpenAI.R154.dP n : ℝ))
    (fun n => (IntMul.OpenAI.R154.KP n : ℝ)) (fun n => (IntMul.OpenAI.R154.ℓP n : ℝ))
    (fun n => (IntMul.OpenAI.R154.αP n : ℝ))
    (fun n hn => (hp n (le_of_max_le_right hn)).1)
    (fun n hn => (hp n (le_of_max_le_right hn)).2.1)
    (fun n hn => (hp n (le_of_max_le_right hn)).2.2.1)
    (fun n hn => (hp n (le_of_max_le_right hn)).2.2.2.1)
    (fun n hn => (hp n (le_of_max_le_right hn)).2.2.2.2.1)
    (fun n hn => (hp n (le_of_max_le_right hn)).2.2.2.2.2.1)
    (fun n _ => Nat.cast_nonneg _)
    (fun n hn => (hp n (le_of_max_le_right hn)).2.2.2.2.2.2.1)
    (fun n _ => Nat.cast_nonneg _)
    (fun n hn => (hp n (le_of_max_le_right hn)).2.2.2.2.2.2.2)
    (fun n hn => ht n (le_of_max_le_left hn))
