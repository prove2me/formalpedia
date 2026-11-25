-- Prove2me | solution 1 for GlobalTheory.T.lattice_sum_decay_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:22:45.104804+00:00
-- url     : https://prove2.me/submissions/395604a6-bb70-40f1-ad78-a018e084432f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticeSumDecayBound
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticeSumDecayBoundStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Count_tsum_le_prod_of_injOn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ENNReal
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {S P : Type} [Fintype P] (m : S → P → ℤ) (b : P → ℝ), (∀ p, 0 < b p) → ∀ (h : S → ℝ≥0∞), Set.InjOn m {ξ | h ξ ≠ 0} → (∀ ξ, h ξ ≤ ∏ p, ENNReal.ofReal (((1 + |(m ξ p : ℝ)| / b p) ^ 2)⁻¹)) → ∑' ξ, h ξ ≤ ∏ p, ENNReal.ofReal (1 + 2 * b p) := by
  first | exact @GlobalTheory.CompanionTheory.Count.tsum_le_prod_of_injOn | exact GlobalTheory.CompanionTheory.Count.tsum_le_prod_of_injOn | (intros; apply GlobalTheory.CompanionTheory.Count.tsum_le_prod_of_injOn <;> assumption)
end _root_.GlobalTheory.T
