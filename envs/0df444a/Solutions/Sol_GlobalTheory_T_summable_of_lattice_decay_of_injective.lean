-- Prove2me | solution 1 for GlobalTheory.T.summable_of_lattice_decay_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:33:54.753149+00:00
-- url     : https://prove2.me/submissions/c8b03254-1ccc-4911-b940-0637648fefaa

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SummableOfLatticeDecay
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SummableOfLatticeDecayStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_LatticeCount_summable_of_lattice_decay


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (ι : Type) (d : ℕ) (w : ι → ℂ) (f : ι → Fin d → ℝ), Function.Injective f → ∀ (N : ℕ), 0 < N → ∀ (C : ℝ), (∀ i, ‖w i‖ * ∏ k, (1 + f i k ^ 2) ≤ C) → (∀ i, w i ≠ 0 → ∀ k, ∃ n : ℤ, (N : ℝ) * f i k = n) → Summable w := by
  first | exact @GlobalTheory.CompanionTheory.LatticeCount.summable_of_lattice_decay | exact GlobalTheory.CompanionTheory.LatticeCount.summable_of_lattice_decay | (intros; apply GlobalTheory.CompanionTheory.LatticeCount.summable_of_lattice_decay <;> assumption)
end _root_.GlobalTheory.T
