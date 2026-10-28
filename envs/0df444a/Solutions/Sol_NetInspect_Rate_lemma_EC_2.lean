-- Prove2me | solution 1 for NetInspect.Rate.lemma_EC_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:20:39.98358+00:00
-- url     : https://prove2.me/submissions/d245d595-885e-4a86-ab9e-cf1e2629fca0

import Mathlib
import Definitions.Def_BlottoLP_Flow_ZeroSum
import Definitions.Def_NetInspect_Rate_Model

open Finset NetInspect.Rate NetInspect.Rate.DetectionModel in
theorem solution {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : DetectionModel V E) :
    G.mStar ≤ G.nStar := by
  classical
  -- cover gives membership
  have hcov : ∀ S : Finset V, G.IsSetCover S → ∀ e : E, ∃ i ∈ S, e ∈ G.C i := by
    intro S hS e
    have h := hS e
    unfold DetectionModel.F at h
    by_contra hne
    have : e ∉ G.CS S := by
      unfold DetectionModel.CS
      rw [Finset.mem_biUnion]
      exact hne
    rw [Finset.inter_singleton_of_notMem this, Finset.card_empty] at h
    exact zero_ne_one h
  have key : ∀ (S : Finset V) (T : Finset E), G.IsSetCover S → G.IsSetPacking T →
      T.card ≤ S.card := by
    intro S T hS hT
    choose f hfS hfC using hcov S hS
    refine Finset.card_le_card_of_injOn f (fun e _ => hfS e) ?_
    intro e1 he1 e2 he2 hf
    have hp := hT (f e1)
    unfold DetectionModel.F DetectionModel.CS at hp
    rw [Finset.singleton_biUnion] at hp
    have m1 : e1 ∈ G.C (f e1) ∩ T := Finset.mem_inter.mpr ⟨hfC e1, he1⟩
    have m2 : e2 ∈ G.C (f e1) ∩ T := Finset.mem_inter.mpr ⟨hf ▸ hfC e2, he2⟩
    exact Finset.card_le_one.mp hp e1 m1 e2 m2
  have hne : {k | ∃ S : Finset V, S.card = k ∧ G.IsSetCover S}.Nonempty := by
    refine ⟨Finset.univ.card, Finset.univ, rfl, ?_⟩
    intro e
    obtain ⟨i, hi⟩ := G.coverable e
    unfold DetectionModel.F DetectionModel.CS
    have : e ∈ Finset.univ.biUnion G.C := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩
    rw [Finset.inter_singleton_of_mem this, Finset.card_singleton]
  obtain ⟨S, hSc, hS⟩ := Nat.sInf_mem hne
  unfold DetectionModel.mStar
  apply csSup_le
  · refine ⟨0, ∅, rfl, ?_⟩
    intro i
    unfold DetectionModel.F
    simp
  · rintro k ⟨T, rfl, hT⟩
    unfold DetectionModel.nStar
    rw [← hSc]
    exact key S T hS hT
