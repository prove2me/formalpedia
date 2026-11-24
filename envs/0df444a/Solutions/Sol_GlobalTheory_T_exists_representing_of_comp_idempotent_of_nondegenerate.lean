-- Prove2me | solution 1 for GlobalTheory.T.exists_representing_of_comp_idempotent_of_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:06:08.576935+00:00
-- url     : https://prove2.me/submissions/ae7fc5c3-c6e9-441e-9c7a-d487f2b77e4a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FunctionalFixedByIdempotentRepresented
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FunctionalFixedByIdempotentRepresentedStatement
import Theorems.Thm_GlobalTheory_functional_fixed_by_idempotent_represented


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ), (∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) → (∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0) → ∀ (P P' : Module.End ℂ V), P ∘ₗ P = P → FiniteDimensional ℂ (LinearMap.range P) → (∀ φ ψ, B (P φ) ψ = B φ (P' ψ)) → ∀ f : V →ₗ[ℂ] ℂ, f ∘ₗ P = f → ∃ ψ, ∀ φ, B φ ψ = f φ := by
  first | exact @GlobalTheory.functional_fixed_by_idempotent_represented | exact GlobalTheory.functional_fixed_by_idempotent_represented | (intros; apply GlobalTheory.functional_fixed_by_idempotent_represented <;> assumption)
end _root_.GlobalTheory.T
