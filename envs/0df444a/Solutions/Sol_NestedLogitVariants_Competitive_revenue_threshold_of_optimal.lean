-- Prove2me | solution 1 for NestedLogitVariants.Competitive.revenue_threshold_of_optimal
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T13:03:54.004981+00:00
-- url     : https://prove2.me/submissions/ac513840-90b7-4aff-b497-fcbd9ae09b57

import Definitions.Def_NestedLogitVariants_Competitive_Model
import Theorems.Thm_NestedLogitVariants_Competitive_proposition_2
import Theorems.Thm_NestedLogitVariants_Competitive_lemma_3

open NestedLogitVariants.Competitive

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (hγ : ∀ i, I.γ i ≤ 1) (hfc : ∀ i, I.vnp i = 0) (hv0 : 0 < I.v0)
    (Sstar : ι → Finset (Fin n)) (hopt : IsOptimal I Sstar)
    (i : ι) (j : Fin n) (hj : j ∈ Sstar i) :
    I.γ i * revenue I Sstar + (1 - I.γ i) * R I i (Sstar i) ≤ I.r i j := by
  by_contra h
  have hR := NestedLogitVariants.Competitive.proposition_2 I hI hγ hfc hv0 Sstar hopt i ⟨j, hj⟩
  have hlt := NestedLogitVariants.Competitive.lemma_3 I hI hγ hfc hv0 Sstar i j hj (lt_of_not_ge h) hR
  exact (not_lt_of_ge (hopt _)) hlt

#print axioms solution
