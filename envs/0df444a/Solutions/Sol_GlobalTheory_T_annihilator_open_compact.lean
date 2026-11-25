-- Prove2me | solution 1 for GlobalTheory.T.annihilator_open_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:12:22.738422+00:00
-- url     : https://prove2.me/submissions/f50871c5-8f14-4a6b-832f-0bb24942f4db

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AnnihilatorOpenCompact
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AnnihilatorOpenCompactStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_CharPerp_perp_isOpen_isCompact


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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (A : AddSubgroup (Fin n → k)), IsCompact (A : Set (Fin n → k)) → IsOpen (A : Set (Fin n → k)) → IsOpen {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} ∧ IsCompact {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} := by
  first | exact @GlobalTheory.CompanionTheory.CharPerp.perp_isOpen_isCompact | exact GlobalTheory.CompanionTheory.CharPerp.perp_isOpen_isCompact | (intros; apply GlobalTheory.CompanionTheory.CharPerp.perp_isOpen_isCompact <;> assumption)
end _root_.GlobalTheory.T
