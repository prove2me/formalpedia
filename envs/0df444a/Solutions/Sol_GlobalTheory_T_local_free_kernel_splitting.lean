-- Prove2me | solution 1 for GlobalTheory.T.local_free_kernel_splitting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:18:20.23491+00:00
-- url     : https://prove2.me/submissions/03c885ac-18cd-4bab-9ddc-d8c3ada40126

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalFreeKernelSplitting
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalFreeKernelSplittingStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalSplit_exists_idempotent_of_residueField


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A Q P : Type) [CommRing A] [IsLocalRing A] [AddCommGroup Q] [Module A Q] [AddCommGroup P] [Module A P] [Module.Finite A Q] [Module.Free A Q] [Module.Finite A P] [Module.Free A P] (d : Q →ₗ[A] P), ∃ r : P →ₗ[A] Q, (r ∘ₗ d ∘ₗ r ∘ₗ d = r ∘ₗ d) ∧ Module.Free A (LinearMap.ker (r ∘ₗ d)) ∧ Module.Finite A (LinearMap.ker (r ∘ₗ d)) ∧ Module.finrank A (LinearMap.ker (r ∘ₗ d)) = Module.finrank (IsLocalRing.ResidueField A) (LinearMap.ker (d.baseChange (IsLocalRing.ResidueField A))) := by
  first | exact @GlobalTheory.CompanionTheory.LocalSplit.exists_idempotent_of_residueField | exact GlobalTheory.CompanionTheory.LocalSplit.exists_idempotent_of_residueField | (intros; apply GlobalTheory.CompanionTheory.LocalSplit.exists_idempotent_of_residueField <;> assumption)
end _root_.GlobalTheory.T
