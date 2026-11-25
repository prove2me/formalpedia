-- Prove2me | solution 1 for GlobalTheory.T.simultaneous_eigenbasis_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:24:17.345022+00:00
-- url     : https://prove2.me/submissions/cc8d6b7e-6240-4436-9f21-6da42d381919

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SimultaneousEigenbasisIntegral
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SimultaneousEigenbasisIntegralStatement
import Theorems.Thm_GlobalTheory_exists_generator_eigenform


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
theorem _root_.solution : ∀ (R : Subring ℂ) [IsPrincipalIdealRing R] {g : ℕ} {V : Type} [AddCommGroup V] [Module R V]
    (b : Module.Basis (Fin g) R V) (ψ : V →ₗ[R] (Fin g → ℂ)), (LinearIndependent ℂ fun k ↦ ψ (b k)) →
    ∀ {J : Type} (T : J → V →ₗ[R] V) (lam : J → Fin g → ℂ), (∀ a v j, ψ (T a v) j = lam a j * ψ v j) →
    (∀ j k, j ≠ k → ∃ a, lam a j ≠ lam a k) → (∀ a j, ∃ x ∈ R, ∃ y ∈ R, y ≠ 0 ∧ lam a j * y = x) → ∀ i : Fin g,
    ∃ (e : V →ₗ[R] R) (c : ℂ), c ≠ 0 ∧ (∀ v, ((e v : R) : ℂ) = c * ψ v i) ∧
      ∀ (e' : V →ₗ[R] R) (c' : ℂ), (∀ v, ((e' v : R) : ℂ) = c' * ψ v i) → ∃ t : R, e' = t • e := by
  first | exact @GlobalTheory.exists_generator_eigenform | exact GlobalTheory.exists_generator_eigenform | (intros; apply GlobalTheory.exists_generator_eigenform <;> assumption)
end _root_.GlobalTheory.T
