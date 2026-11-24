-- Prove2me | solution 1 for GlobalTheory.T.annihilator_compact_within_nhds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:02:43.883567+00:00
-- url     : https://prove2.me/submissions/7caa8c6f-633f-455e-957e-112d1329c029

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AnnihilatorCompactWithinNhds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AnnihilatorCompactWithinNhdsStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_CharDual_exists_compact_annihilator_subset


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (S : Set (Fin n → k)), S ∈ nhds (0 : Fin n → k) → ∃ Ξ : AddSubgroup (Fin n → k), IsCompact (Ξ : Set (Fin n → k)) ∧ ∀ t : Fin n → k, (∀ ξ ∈ Ξ, ψ (ξ ⬝ᵥ t) = 1) → t ∈ S := by
  first | exact @GlobalTheory.CompanionTheory.CharDual.exists_compact_annihilator_subset | exact GlobalTheory.CompanionTheory.CharDual.exists_compact_annihilator_subset | (intros; apply GlobalTheory.CompanionTheory.CharDual.exists_compact_annihilator_subset <;> assumption)
end _root_.GlobalTheory.T
