-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinReversal.prod_filter_le_rev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:31:42.515726+00:00
-- url     : https://prove2.me/submissions/b96297f6-2c92-44fb-98b1-a6ba2c00796f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProdLeRevEqProdGe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinReversal
namespace GlobalTheory.CompanionTheory.FinReversal
theorem _root_.solution {M : Type*} [CommMonoid M] (h : ℕ) (f : Fin h → M) (j : Fin h) :
    ∏ a ∈ Finset.univ.filter (fun a => a ≤ j), f (Fin.rev a)
      = ∏ i ∈ Finset.univ.filter (fun i => Fin.rev j ≤ i), f i := by
  refine Finset.prod_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact Fin.rev_le_rev.mpr ha
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [← Fin.rev_le_rev, Fin.rev_rev]
    exact ha
  · intro a _
    exact Fin.rev_rev a
  · intro a _
    exact Fin.rev_rev a
  · intro a _
    rfl
end GlobalTheory.CompanionTheory.FinReversal
