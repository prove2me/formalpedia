-- Prove2me | solution 1 for NetInspect.Rate.corollary_EC_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T13:53:53.506495+00:00
-- url     : https://prove2.me/submissions/24757bbe-66e8-4b52-8eef-066ad911b41c

import Mathlib
import Definitions.Def_BlottoLP_Flow_ZeroSum
import Definitions.Def_NetInspect_Rate_Model

open Finset NetInspect.Rate NetInspect.Rate.DetectionModel in
theorem solution {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : DetectionModel V E) :
    (∀ (S : Finset V) (T : Finset E), G.F S T ≤ ∑ i ∈ S, G.F {i} T) ∧
    (∀ (S : Finset V) (T : Finset E), G.F S T = ∑ e ∈ T, G.F S {e}) := by
  constructor
  · intro S T
    simp only [DetectionModel.F, DetectionModel.CS, Finset.singleton_biUnion]
    rw [Finset.biUnion_inter]
    exact Finset.card_biUnion_le
  · intro S T
    simp only [DetectionModel.F]
    have h : ∀ e, (G.CS S ∩ {e}).card = if e ∈ G.CS S then 1 else 0 := by
      intro e
      split_ifs with he
      · rw [Finset.inter_singleton_of_mem he, Finset.card_singleton]
      · rw [Finset.inter_singleton_of_notMem he, Finset.card_empty]
    simp only [h]
    rw [Finset.sum_boole, Nat.cast_id, Finset.filter_mem_eq_inter, Finset.inter_comm]
