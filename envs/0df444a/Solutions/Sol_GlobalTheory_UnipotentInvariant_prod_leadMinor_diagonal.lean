-- Prove2me | solution 1 for GlobalTheory.UnipotentInvariant.prod_leadMinor_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:49:53.164229+00:00
-- url     : https://prove2.me/submissions/076740c2-ae67-4b61-9c88-50c7feb7df2e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ProdLeadMinorDiagonal
import Theorems.Thm_GlobalTheory_UnipotentInvariant_leadMinor_diagonal

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
theorem _root_.solution (d : Fin p → K) (c : Fin p → ℕ) :
    ∏ i, leadMinor i (diagonal d) ^ c i = ∏ a, d a ^ ∑ i ∈ Finset.Ici a, c i := by
  simp only [leadMinor_diagonal, ← Finset.prod_pow, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_comm' ?_
  intro x y
  simp
end GlobalTheory.UnipotentInvariant
