-- Prove2me | solution 1 for GlobalTheory.T.lattice_annihilator_within_nhds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:23:24.811782+00:00
-- url     : https://prove2.me/submissions/db782652-7eae-49f3-b34b-7e6685fea492

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticeAnnihilatorWithinNhds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticeAnnihilatorWithinNhdsStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_AnnihShrink_exists_compact_open_annihilator_subset


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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (U : Set (Fin n → k)), U ∈ nhds (0 : Fin n → k) → ∃ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) ∧ IsOpen (A : Set (Fin n → k)) ∧ {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} ⊆ U := by
  first | exact @GlobalTheory.CompanionTheory.AnnihShrink.exists_compact_open_annihilator_subset | exact GlobalTheory.CompanionTheory.AnnihShrink.exists_compact_open_annihilator_subset | (intros; apply GlobalTheory.CompanionTheory.AnnihShrink.exists_compact_open_annihilator_subset <;> assumption)
end _root_.GlobalTheory.T
