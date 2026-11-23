-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EntrywiseCount.card_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:30.004701+00:00
-- url     : https://prove2.me/submissions/2493f452-5260-4b98-8f9f-e0d5f2b81b8c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProdEntrywiseLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EntrywiseCount
namespace GlobalTheory.CompanionTheory.EntrywiseCount
theorem _root_.solution (n r : ℕ) (hr : r ≤ n) :
    (univ.filter (fun i : Fin n => (i : ℕ) < r)).card = r := by
  have h : (univ.filter (fun i : Fin n => (i : ℕ) < r)).card
      = ((range n).filter (fun i => i < r)).card := by
    rw [Finset.card_filter, Finset.card_filter]
    exact Fin.sum_univ_eq_sum_range (fun i => if i < r then 1 else 0) n
  rw [h]
  have : (range n).filter (fun i => i < r) = range r := by
    ext x
    simp only [mem_filter, mem_range]
    omega
  rw [this, card_range]
end GlobalTheory.CompanionTheory.EntrywiseCount
