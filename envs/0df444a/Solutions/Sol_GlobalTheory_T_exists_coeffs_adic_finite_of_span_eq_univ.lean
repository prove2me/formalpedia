-- Prove2me | solution 1 for GlobalTheory.T.exists_coeffs_adic_finite_of_span_eq_univ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:15:48.963058+00:00
-- url     : https://prove2.me/submissions/076e2706-e22a-48c4-9c58-2f2cd13f780e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdicCoeffsTendstoZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdicCoeffsTendstoZeroStatement
import Theorems.Thm_GlobalTheory_adic_coeffs_tendsto_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (M : Type) [AddCommGroup M] [Module R M] (r : ℕ) (s : Fin r → M), Submodule.span R (Set.range s) = ⊤ → ∀ (X : Type) (z : X → M), (∀ n : ℕ, {χ | z χ ∉ (maximalIdeal R ^ n • ⊤ : Submodule R M)}.Finite) → ∃ c : X → Fin r → R, (∀ χ, z χ = ∑ j, c χ j • s j) ∧ ∀ n : ℕ, {χ | ¬ ∀ j, c χ j ∈ maximalIdeal R ^ n}.Finite := by
  first | exact @GlobalTheory.adic_coeffs_tendsto_zero | exact GlobalTheory.adic_coeffs_tendsto_zero | (intros; apply GlobalTheory.adic_coeffs_tendsto_zero <;> assumption)
end _root_.GlobalTheory.T
