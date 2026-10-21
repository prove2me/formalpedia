-- Prove2me | solution 1 for IntMul.Kappa.campaign_bound_inv_two_pow_129
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-20T14:00:25.222892+00:00
-- url     : https://prove2.me/submissions/6e7b35f3-45ad-4e98-8c5d-3c0f10568ad9

import Definitions.Def_IntMul_MultitapeModel
import Theorems.Thm_IntMul_OpenAI_R129_machine
import Theorems.Thm_IntMul_OpenAI_R129_params_eventually
import Theorems.Thm_IntMul_OpenAI_R129_kappaBound_of_table

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- `KappaBound (2⁻¹²⁹)` from the machine milestone, the parameter bounds and the reduction. -/
theorem solution : IntMul.KappaBound ((1 / 2 ^ 129) : ℝ) := by
  obtain ⟨M, hcorr, C₀, hC₀, A, n₁, ht⟩ := IntMul.OpenAI.R129.machine
  obtain ⟨n₂, hp⟩ := IntMul.OpenAI.R129.params_eventually
  exact IntMul.OpenAI.R129.kappaBound_of_table M hcorr (max n₁ n₂) A C₀ hC₀
    IntMul.OpenAI.Glue.VP (fun n => (IntMul.OpenAI.R129.dP n : ℝ))
    (fun n => (IntMul.OpenAI.R129.KP n : ℝ)) (fun n => (IntMul.OpenAI.R129.ℓP n : ℝ))
    (fun n => (IntMul.OpenAI.R129.αP n : ℝ))
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

