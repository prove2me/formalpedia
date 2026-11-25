-- Prove2me | solution 1 for GlobalTheory.T.exists_joint_eigenvector_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:19:44.681527+00:00
-- url     : https://prove2.me/submissions/81b4235f-150b-4579-aa1b-e00e90ed4994

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsJointEigenvectorNonzero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsJointEigenvectorNonzeroStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_LinAlg_exists_joint_eigenvector_combination_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ι J : Type) [Fintype J] (H : ι → Module.End ℂ W), (∀ i i', Commute (H i) (H i')) → ∀ (c : J → ℂ) (s : J → ι) (v : W) (m : ℕ), Module.finrank ℂ W ≤ m → ((∑ j, c j • H (s j)) ^ m) v ≠ 0 → ∃ v₀ : W, v₀ ≠ 0 ∧ ∃ χ : ι → ℂ, (∀ i, H i v₀ = χ i • v₀) ∧ ∑ j, c j * χ (s j) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.LinAlg.exists_joint_eigenvector_combination_ne_zero | exact GlobalTheory.CompanionTheory.LinAlg.exists_joint_eigenvector_combination_ne_zero | (intros; apply GlobalTheory.CompanionTheory.LinAlg.exists_joint_eigenvector_combination_ne_zero <;> assumption)
end _root_.GlobalTheory.T
