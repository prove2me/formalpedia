-- Prove2me | solution 1 for GlobalTheory.T.pow_sub_creation_vacuum_fock_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:24:39.347374+00:00
-- url     : https://prove2.me/submissions/4bc0fc69-028d-4315-938b-2cb3d0c8cc13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowSubCreationVacuumFockBound
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowSubCreationVacuumFockBoundStatement
import Theorems.Thm_GlobalTheory_pow_vacuum_fock_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (T H : Type) [AddCommGroup T] [Module ℂ T] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Φ : T →ₗ[ℂ] H) (a c : Module.End ℂ T) (s : ℝ) (v : T), 0 ≤ s → (∀ x y, inner ℂ (Φ (c x)) (Φ y) = inner ℂ (Φ x) (Φ (a y))) → a * c - c * a = (s : ℂ) • 1 → a v = 0 → (∀ K : Submodule ℂ T, v ∈ K → (∀ x ∈ K, c x ∈ K) → ∀ k : ℕ, ((c - a) ^ k) v ∈ K) ∧ ∀ k : ℕ, ‖Φ (((c - a) ^ k) v)‖ ^ 2 ≤ ‖Φ v‖ ^ 2 * (2 * s) ^ k * k.factorial := by
  first | exact @GlobalTheory.pow_vacuum_fock_bound | exact GlobalTheory.pow_vacuum_fock_bound | (intros; apply GlobalTheory.pow_vacuum_fock_bound <;> assumption)
end _root_.GlobalTheory.T
