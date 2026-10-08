-- Prove2me | solution 1 for GilmoreGomoryTSP.MinCost.lemma_8_count_22a_22b
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T00:59:05.337236+00:00
-- url     : https://prove2.me/submissions/bc34d802-c677-433d-93d4-44f3a5fe6ef5

import Mathlib
import Definitions.Def_GilmoreGomoryTSP_MinCost_Model
import Definitions.Def_GilmoreGomoryTSP_MinCost_Underestimate

open GilmoreGomoryTSP.MinCost in
theorem solution {n : ℕ} (φ ψ : Equiv.Perm (Fin (n + 1))) (q : Fin n) :
    (Finset.univ.filter fun i => i ≤ q.castSucc ∧ q.castSucc < φ.symm (ψ i)).card =
      (Finset.univ.filter fun j => φ.symm (ψ j) ≤ q.castSucc ∧ q.castSucc < j).card := by
  set S : Finset (Fin (n + 1)) := Finset.univ.filter fun i => i ≤ q.castSucc with hS
  set T : Finset (Fin (n + 1)) := Finset.univ.filter fun i => φ.symm (ψ i) ≤ q.castSucc with hT
  have hL : (Finset.univ.filter fun i => i ≤ q.castSucc ∧ q.castSucc < φ.symm (ψ i)) = S \ T := by
    ext i; simp [hS, hT, not_le]
  have hR : (Finset.univ.filter fun j => φ.symm (ψ j) ≤ q.castSucc ∧ q.castSucc < j) = T \ S := by
    ext i; simp [hS, hT, not_le]
  have hST : T.card = S.card := by
    apply Finset.card_equiv (ψ.trans φ.symm)
    intro i; simp [hS, hT]
  rw [hL, hR]
  have h1 := Finset.card_sdiff_add_card_inter S T
  have h2 := Finset.card_sdiff_add_card_inter T S
  rw [Finset.inter_comm] at h2
  omega
