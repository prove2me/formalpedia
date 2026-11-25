-- Prove2me | solution 1 for GlobalTheory.UnipotentInvariant.exists_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:48:06.275948+00:00
-- url     : https://prove2.me/submissions/9c13e403-b799-454f-8913-43d7f29e516d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ProdLeadMinorDiagonal
import Theorems.Thm_GlobalTheory_UnipotentInvariant_exists_cleared

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
open GlobalTheory
open GlobalTheory.UnipotentInvariant
variable {K : Type*} [Field K] {p : ℕ}
namespace GlobalTheory.UnipotentInvariant
theorem _root_.solution (M : Matrix (Fin p) (Fin p) K) (hM : ∀ i, leadMinor i M ≠ 0) :
    ∃ d : Fin p → K, ∀ f, BiInvariant f → f (diagonal d) = f M := by
  obtain ⟨M', h, hz⟩ := exists_cleared M hM p
  refine ⟨fun i => M' i i, fun f hf => ?_⟩
  rw [← h f hf]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · rw [diagonal_apply_ne _ hij, hz i j hij (Or.inl i.isLt)]
end GlobalTheory.UnipotentInvariant
