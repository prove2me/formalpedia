-- Prove2me | solution 1 for MurtySimon.card_edgeSet_completeBipartiteGraph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:21:37.924549+00:00
-- url     : https://prove2.me/submissions/9212677f-d1a1-4a3f-9526-06af483c71e8

module
public import Definitions.Def_MurtySimon_Equality
public import Definitions.Def_MurtySimon_Main
public import Theorems.Thm_MurtySimon_OnPath_mem_edgeSet


set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]
namespace MurtySimon
theorem _root_.solution (n : ℕ) :
    Nat.card (completeBipartiteGraph (Fin ((n + 1) / 2)) (Fin (n / 2))).edgeSet = n ^ 2 / 4 := by
  classical
  rw [Nat.card_eq_fintype_card, ← edgeFinset_card]
  have hbi : (completeBipartiteGraph (Fin ((n + 1) / 2)) (Fin (n / 2))).edgeFinset =
      (univ ×ˢ univ : Finset (Fin ((n + 1) / 2) × Fin (n / 2))).image
        (fun p => s(Sum.inl p.1, Sum.inr p.2)) := by
    ext e
    induction e using Sym2.ind with
    | h x y =>
      simp only [mem_edgeFinset, mem_edgeSet, completeBipartiteGraph_adj, mem_image,
        mem_product, mem_univ, true_and, Prod.exists, Sym2.eq_iff]
      rcases x with x | x <;> rcases y with y | y <;> simp [eq_comm]
  rw [hbi, card_image_of_injective]
  · rw [card_product, card_univ, card_univ, Fintype.card_fin, Fintype.card_fin]
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · rw [show (2 * k + 1) / 2 = k by omega, show (2 * k) / 2 = k by omega,
        show (2 * k) ^ 2 = 4 * k ^ 2 by ring, Nat.mul_div_cancel_left _ (by norm_num)]
      ring
    · rw [show (2 * k + 1 + 1) / 2 = k + 1 by omega, show (2 * k + 1) / 2 = k by omega,
        show (2 * k + 1) ^ 2 = 4 * (k ^ 2 + k) + 1 by ring,
        show (4 * (k ^ 2 + k) + 1) / 4 = k ^ 2 + k by omega]
      ring
  · rintro ⟨a1, b1⟩ ⟨a2, b2⟩ h
    simp only [Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, and_false,
      or_false] at h
    exact Prod.ext h.1 h.2
end MurtySimon
