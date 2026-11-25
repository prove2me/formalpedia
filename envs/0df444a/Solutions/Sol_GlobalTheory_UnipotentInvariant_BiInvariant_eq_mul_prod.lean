-- Prove2me | solution 1 for GlobalTheory.UnipotentInvariant.BiInvariant.eq_mul_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:25:02.423128+00:00
-- url     : https://prove2.me/submissions/2e7acc1c-a7b0-4abd-b885-8f8659dcf314

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ProdLeadMinorDiagonal
import Theorems.Thm_GlobalTheory_UnipotentInvariant_biInvariant_leadMinor
import Theorems.Thm_GlobalTheory_UnipotentInvariant_exists_diagonal
import Theorems.Thm_GlobalTheory_UnipotentInvariant_prod_leadMinor_diagonal

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
namespace BiInvariant
theorem _root_.solution {f : Matrix (Fin p) (Fin p) K → K} (hf : BiInvariant f)
    (c : Fin p → ℕ)
    (hd : ∀ d, f (diagonal d) = f 1 * ∏ a, d a ^ ∑ i ∈ Finset.Ici a, c i)
    (M : Matrix (Fin p) (Fin p) K) (hM : ∀ i, leadMinor i M ≠ 0) :
    f M = f 1 * ∏ i, leadMinor i M ^ c i := by
  obtain ⟨d, h⟩ := exists_diagonal M hM
  rw [← h f hf, hd, ← prod_leadMinor_diagonal]
  simp only [h _ (biInvariant_leadMinor _)]
end BiInvariant
end GlobalTheory.UnipotentInvariant
