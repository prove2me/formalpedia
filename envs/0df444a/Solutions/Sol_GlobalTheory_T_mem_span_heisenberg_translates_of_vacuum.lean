-- Prove2me | solution 1 for GlobalTheory.T.mem_span_heisenberg_translates_of_vacuum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:33:27.351676+00:00
-- url     : https://prove2.me/submissions/ac95fe7c-7a21-4112-8727-336423b044e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSpanHeisenbergTranslatesOfVacuum
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSpanHeisenbergTranslatesOfVacuumStatement
import Theorems.Thm_GlobalTheory_HeisVacuum_mem_span_translates_vacuum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X M : Type) [AddCommGroup X] [AddCommGroup M] [Module ℂ M] (β : X → X → ℂ) (ρ : X → M →ₗ[ℂ] M) (Λ : AddSubgroup X) (e : M), (∀ x y z, β (x + y) z = β x z * β y z) → (∀ x y z, β x (y + z) = β x y * β x z) → (∀ x, β x x = 1) → (∀ v, ρ 0 v = v) → (∀ x y v, ρ x (ρ y v) = β x y • ρ (x + y) v) → (∀ x, x ∈ Λ ↔ ∀ a ∈ Λ, β x a ^ 2 = 1) → (∀ N : ℕ, 0 < N → ∀ x : X, ∃ y : X, N • y = x) → (∀ N : ℕ, 0 < N → ∃ R : Set X, R.Finite ∧ ∀ t ∈ Λ, ∃ r ∈ R, ∃ u ∈ Λ, t = r + N • u) → e ≠ 0 → (∀ u ∈ Λ, ∃ ε : ℂ, ρ u e = ε • e) → (∀ u ∈ Λ, ρ (2 • u) e = e) → (∀ v : M, (∀ u ∈ Λ, ∀ ε : ℂ, ρ u e = ε • e → ρ u v = ε • v) → ∃ c : ℂ, v = c • e) → ∀ v : M, (∃ N : ℕ, 0 < N ∧ ∀ u ∈ Λ, ρ (N • u) v = v) → v ∈ Submodule.span ℂ (Set.range fun x => ρ x e) := by
  first | exact @GlobalTheory.HeisVacuum.mem_span_translates_vacuum | exact GlobalTheory.HeisVacuum.mem_span_translates_vacuum | (intros; apply GlobalTheory.HeisVacuum.mem_span_translates_vacuum <;> assumption)
end _root_.GlobalTheory.T
