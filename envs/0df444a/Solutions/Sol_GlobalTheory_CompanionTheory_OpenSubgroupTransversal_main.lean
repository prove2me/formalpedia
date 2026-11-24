-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.OpenSubgroupTransversal.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:13:59.297347+00:00
-- url     : https://prove2.me/submissions/659004ec-e40b-4e6e-b858-5b0e33990f5a

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteCosetRepresentatives
import Theorems.Thm_GlobalTheory_CompanionTheory_OpenSubgroupTransversal_finite_transversal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.OpenSubgroupTransversal
namespace GlobalTheory.CompanionTheory.OpenSubgroupTransversal
theorem _root_.solution : ∀ {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X]
    (A H : AddSubgroup X), IsCompact (A : Set X) → IsOpen (H : Set X) → H ≤ A →
    ∃ T : Finset X, (∀ t ∈ T, t ∈ A) ∧ ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H :=
  fun A H hA hH hHA => GlobalTheory.CompanionTheory.OpenSubgroupTransversal.finite_transversal A H hA hH hHA
end GlobalTheory.CompanionTheory.OpenSubgroupTransversal
