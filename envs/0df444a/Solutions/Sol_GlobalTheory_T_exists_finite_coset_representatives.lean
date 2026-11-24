-- Prove2me | solution 1 for GlobalTheory.T.exists_finite_coset_representatives
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:08:05.300702+00:00
-- url     : https://prove2.me/submissions/184ab063-5ecd-4b2b-9334-962eb42b11e8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteCosetRepresentatives
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteCosetRepresentativesStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_OpenSubgroupTransversal_main


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
theorem _root_.solution : ∀ {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] (A H : AddSubgroup X), IsCompact (A : Set X) → IsOpen (H : Set X) → H ≤ A → ∃ T : Finset X, (∀ t ∈ T, t ∈ A) ∧ ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H := by
  first | exact @GlobalTheory.CompanionTheory.OpenSubgroupTransversal.main | exact GlobalTheory.CompanionTheory.OpenSubgroupTransversal.main | (intros; apply GlobalTheory.CompanionTheory.OpenSubgroupTransversal.main <;> assumption)
end _root_.GlobalTheory.T
