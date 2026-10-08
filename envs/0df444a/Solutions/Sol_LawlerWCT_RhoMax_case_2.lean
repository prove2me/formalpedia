-- Prove2me | solution 1 for LawlerWCT.RhoMax.case_2
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:47:43.036349+00:00
-- url     : https://prove2.me/submissions/38293d43-c857-4aad-9a9f-d3946e2af52a

import Mathlib
import Definitions.Def_LawlerWCT_RhoMax_Model
open LawlerWCT.RhoMax

theorem solution {ι : Type*} (N : Finset ι) (G : ι → ι → Prop)
    (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N) (hacyc : ∀ j, ¬ Relation.TransGen G j j)
    (p w : ι → ℝ) (hp : ∀ j ∈ N, 0 < p j) (ρ : ℝ) (I : Finset ι)
    (hI : LawlerWCT.SeriesPar.IsInitialSet G N I) (hIne : I.Nonempty)
    (hmax : ∀ I', LawlerWCT.SeriesPar.IsInitialSet G N I' → I'.Nonempty → trialWeight p w ρ I' ≤ trialWeight p w ρ I)
    (hneg : trialWeight p w ρ I < 0) :
    ∀ I', LawlerWCT.SeriesPar.IsInitialSet G N I' → I'.Nonempty → LawlerWCT.SeriesPar.rho p w I' < ρ := by
  classical
  intro I' hi hn
  have hp' : 0 < ∑ j ∈ I', p j := Finset.sum_pos (fun j hj => hp j (hi.1 hj)) hn
  rw [LawlerWCT.SeriesPar.rho, div_lt_iff₀ hp']
  have hh := lt_of_le_of_lt (hmax I' hi hn) hneg
  simp only [trialWeight, Finset.sum_sub_distrib, ← Finset.mul_sum] at hh
  linarith


#print axioms solution

