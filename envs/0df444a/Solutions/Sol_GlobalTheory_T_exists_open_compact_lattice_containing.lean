-- Prove2me | solution 1 for GlobalTheory.T.exists_open_compact_lattice_containing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:16:58.571677+00:00
-- url     : https://prove2.me/submissions/a4c671cd-01b8-4a29-a382-e0c3523152d1

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOpenCompactLatticeContaining
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOpenCompactLatticeContainingStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalLattice_exists_compact_open_addSubgroup


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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (K : Set (Fin n → k)), IsCompact K → ∃ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) ∧ IsOpen (A : Set (Fin n → k)) ∧ K ⊆ A := by
  first | exact @GlobalTheory.CompanionTheory.LocalLattice.exists_compact_open_addSubgroup | exact GlobalTheory.CompanionTheory.LocalLattice.exists_compact_open_addSubgroup | (intros; apply GlobalTheory.CompanionTheory.LocalLattice.exists_compact_open_addSubgroup <;> assumption)
end _root_.GlobalTheory.T
