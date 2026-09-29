-- Prove2me | solution 1 for NonmonotoneSubmod.QueryLB.balanced_queries_indistinguishable
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:49:09.750681+00:00
-- url     : https://prove2.me/submissions/24e6b4d0-3180-4044-ab16-8ce044cc3717

import Mathlib
import Definitions.Def_NonmonotoneSubmod_QueryLB_HardInstance
import Definitions.Def_NonmonotoneSubmod_QueryLB_QueryAlgorithm

namespace NonmonotoneSubmod.QueryLB

theorem aux_bqi_fC_eq_gCut (n m : ℕ) (C Q : Finset (Fin n)) (h : Balanced n m C Q) :
    fC n m C Q = gCut n Q := by
  unfold fC gCut fkl
  unfold Balanced at h
  rw [if_pos h]
  have hc : (Q ∩ C).card + (Q ∩ Cᶜ).card = Q.card := by
    rw [← Finset.sdiff_eq_inter_compl]
    exact Finset.card_inter_add_card_sdiff Q C
  have hc' : ((Q ∩ C).card : ℝ) + (Q ∩ Cᶜ).card = Q.card := by exact_mod_cast hc
  rw [← hc']
  ring

end NonmonotoneSubmod.QueryLB

open NonmonotoneSubmod.QueryLB

theorem solution (n m q : ℕ) (A : DetAlg (Fin n) q)
    (C : Finset (Fin n)) (hbal : ∀ i < q, Balanced n m C (A.queryAt (gCut n) i)) :
    (∀ i ≤ q, A.answers (fC n m C) i = A.answers (gCut n) i) ∧
      A.run (fC n m C) = A.run (gCut n) := by
  have key : ∀ i ≤ q, A.answers (fC n m C) i = A.answers (gCut n) i := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      have hb := hbal k (by omega)
      simp only [DetAlg.answers]
      rw [ih']
      congr 2
      exact aux_bqi_fC_eq_gCut n m C _ hb
  refine ⟨key, ?_⟩
  unfold DetAlg.run
  rw [key q le_rfl]
