-- Prove2me | solution 1 for GlobalTheory.T.indep_over_padic_of_indep_mod_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:10:06.08582+00:00
-- url     : https://prove2.me/submissions/c0590d67-4055-49c9-a134-190c69c24144

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IndepOverPadicOfIndepModPrime
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IndepOverPadicOfIndepModPrimeStatement
import Theorems.Thm_GlobalTheory_indep_over_Ql_of_indep_mod_l


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (d : ℕ) (ι : Type) (w : Fin d → ι → ℂ_[l]) (γ : ι → ℝ), (∀ a i, ‖w a i‖ ≤ γ i) → (∀ n : Fin d → ℕ, (∀ i, ‖∑ a, (n a : ℂ_[l]) * w a i‖ ≤ ‖(l : ℂ_[l])‖ * γ i) → ∀ a, l ∣ n a) → ∀ c : Fin d → ℚ_[l], (∀ i, ∑ a, algebraMap ℚ_[l] ℂ_[l] (c a) * w a i = 0) → c = 0 := by
  first | exact @GlobalTheory.indep_over_Ql_of_indep_mod_l | exact GlobalTheory.indep_over_Ql_of_indep_mod_l | (intros; apply GlobalTheory.indep_over_Ql_of_indep_mod_l <;> assumption)
end _root_.GlobalTheory.T
