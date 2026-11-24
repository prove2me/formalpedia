-- Prove2me | solution 1 for GlobalTheory.T.prod_le_rev_eq_prod_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:20:27.743867+00:00
-- url     : https://prove2.me/submissions/ad7dc4fc-2e09-4a97-aa0d-747f3303a218

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProdLeRevEqProdGe
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProdLeRevEqProdGeStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FinReversal_prod_filter_le_rev


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
theorem _root_.solution : ∀ {M : Type*} [CommMonoid M] (h : ℕ) (f : Fin h → M) (j : Fin h), ∏ a ∈ Finset.univ.filter (fun a => a ≤ j), f (Fin.rev a) = ∏ i ∈ Finset.univ.filter (fun i => Fin.rev j ≤ i), f i := by
  first | exact @GlobalTheory.CompanionTheory.FinReversal.prod_filter_le_rev | exact GlobalTheory.CompanionTheory.FinReversal.prod_filter_le_rev | (intros; apply GlobalTheory.CompanionTheory.FinReversal.prod_filter_le_rev <;> assumption)
end _root_.GlobalTheory.T
