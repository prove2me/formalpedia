-- Prove2me | solution 1 for GlobalTheory.T.exists_coset_reps_open_in_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:21:51.85636+00:00
-- url     : https://prove2.me/submissions/f549dbb3-ea1d-479d-99e7-4cf348d49014

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCosetRepsOpenInCompact
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCosetRepsOpenInCompactStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Topology_exists_finset_transversal_of_isCompact_of_isOpen


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
theorem _root_.solution : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] (A L : AddSubgroup X), IsCompact (A : Set X) → IsOpen (L : Set X) → L ≤ A → ∃ T : Finset X, (∀ t ∈ T, t ∈ A) ∧ (∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ L) := by
  first | exact @GlobalTheory.CompanionTheory.Topology.exists_finset_transversal_of_isCompact_of_isOpen | exact GlobalTheory.CompanionTheory.Topology.exists_finset_transversal_of_isCompact_of_isOpen | (intros; apply GlobalTheory.CompanionTheory.Topology.exists_finset_transversal_of_isCompact_of_isOpen <;> assumption)
end _root_.GlobalTheory.T
