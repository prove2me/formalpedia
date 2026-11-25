-- Prove2me | solution 1 for GlobalTheory.T.relIndex_annihilators_duality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:24:17.384489+00:00
-- url     : https://prove2.me/submissions/c9b58b75-b563-466e-b7da-5e869b371b27

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RelIndexAnnihilatorsDuality
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RelIndexAnnihilatorsDualityStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_IndexDuality_relIndex_annihilator_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (A₀ A P₀ P : AddSubgroup (Fin n → k)), IsCompact (A₀ : Set (Fin n → k)) → IsOpen (A₀ : Set (Fin n → k)) → IsCompact (A : Set (Fin n → k)) → IsOpen (A : Set (Fin n → k)) → A₀ ≤ A → (∀ ξ, ξ ∈ P₀ ↔ ∀ a ∈ A₀, ψ (ξ ⬝ᵥ a) = 1) → (∀ ξ, ξ ∈ P ↔ ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1) → P.relIndex P₀ = A₀.relIndex A := by
  first | exact @GlobalTheory.CompanionTheory.IndexDuality.relIndex_annihilator_eq | exact GlobalTheory.CompanionTheory.IndexDuality.relIndex_annihilator_eq | (intros; apply GlobalTheory.CompanionTheory.IndexDuality.relIndex_annihilator_eq <;> assumption)
end _root_.GlobalTheory.T
