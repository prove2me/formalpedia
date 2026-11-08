-- Prove2me | solution 1 for LegalAssign.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:42:45.889767+00:00
-- url     : https://prove2.me/submissions/d800b57b-d7ce-48d5-806b-8f04569cfcf8

import Mathlib
import Definitions.Def_LegalAssign_Instance
import Definitions.Def_LegalAssign_legalSeq

open LegalAssign in
theorem solution {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (G : Instance A B) :
    ∃ k, G.legalSeq k = G.legalSeq (k + 1) := by
  have hB : ∀ S T : Set (Finset (A × B)), S ⊆ T → G.blockedBy S ⊆ G.blockedBy T := by
    rintro S T h M ⟨hM, M', hM', hb⟩
    exact ⟨hM, M', h hM', hb⟩
  have hf : ∀ S T : Set (Finset (A × B)), S ⊆ T → G.legalOp S ⊆ G.legalOp T := by
    intro S T h
    unfold Instance.legalOp
    exact Set.diff_subset_diff_right (hB _ _ (Set.diff_subset_diff_right (hB _ _ h)))
  have h0 : G.stable ⊆ G.legalOp G.stable := by
    intro M hM
    refine ⟨hM.1, ?_⟩
    rintro ⟨_, M', _, e, _, hbp⟩
    exact hM.2 e.1 e.2 hbp
  have hmono : ∀ k, G.legalSeq k ⊆ G.legalSeq (k + 1) := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih => exact hf _ _ ih
  have hmon : Monotone G.legalSeq := monotone_nat_of_le_succ hmono
  obtain ⟨n, hn⟩ := WellFoundedGT.monotone_chain_condition (⟨G.legalSeq, hmon⟩ : ℕ →o _)
  exact ⟨n, hn (n + 1) (by omega)⟩
