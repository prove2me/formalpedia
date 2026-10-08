-- Prove2me | solution 1 for LawlerWCT.RhoMax.case_3
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:47:44.129883+00:00
-- url     : https://prove2.me/submissions/666a21b7-6822-4d53-b3b2-d7017268096a

import Mathlib
import Definitions.Def_LawlerWCT_RhoMax_Model
open LawlerWCT.RhoMax

theorem solution {ι : Type*} (N : Finset ι) (G : ι → ι → Prop)
    (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N) (hacyc : ∀ j, ¬ Relation.TransGen G j j)
    (p w : ι → ℝ) (hp : ∀ j ∈ N, 0 < p j) (ρ : ℝ) (I : Finset ι)
    (hI : LawlerWCT.SeriesPar.IsInitialSet G N I) (hIne : I.Nonempty)
    (hmax : ∀ I', LawlerWCT.SeriesPar.IsInitialSet G N I' → I'.Nonempty → trialWeight p w ρ I' ≤ trialWeight p w ρ I)
    (hzero : trialWeight p w ρ I = 0) :
    LawlerWCT.SeriesPar.IsRhoMaximal G p w N I ∧ LawlerWCT.SeriesPar.rho p w I = ρ := by
  classical
  have hpI : 0 < ∑ j ∈ I, p j := Finset.sum_pos (fun j hj => hp j (hI.1 hj)) hIne
  have he : LawlerWCT.SeriesPar.rho p w I = ρ := by
    rw [LawlerWCT.SeriesPar.rho, div_eq_iff hpI.ne']
    simp only [trialWeight, Finset.sum_sub_distrib, ← Finset.mul_sum] at hzero
    linarith
  refine ⟨⟨hI, hIne, ?_⟩, he⟩
  intro I' hi hn
  rw [he, LawlerWCT.SeriesPar.rho, div_le_iff₀ (Finset.sum_pos (fun j hj => hp j (hi.1 hj)) hn)]
  have hh := hmax I' hi hn
  rw [hzero] at hh
  simp only [trialWeight, Finset.sum_sub_distrib, ← Finset.mul_sum] at hh
  linarith


#print axioms solution

