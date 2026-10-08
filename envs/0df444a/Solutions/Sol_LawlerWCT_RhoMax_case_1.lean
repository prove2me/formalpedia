-- Prove2me | solution 1 for LawlerWCT.RhoMax.case_1
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T19:30:19.233616+00:00
-- url     : https://prove2.me/submissions/1d918f8f-4769-4a2f-91d2-6264b5ef6f01

import Definitions.Def_LawlerWCT_RhoMax_Model
open LawlerWCT.RhoMax LawlerWCT.SeriesPar

theorem solution {ι : Type*} (N : Finset ι) (p w : ι → ℝ) (hp : ∀ j ∈ N, 0 < p j)
    (ρ : ℝ) (I : Finset ι) (hIN : I ⊆ N) (hpos : 0 < trialWeight p w ρ I) :
    I.Nonempty ∧ ρ < rho p w I := by
  classical
  have hne : I.Nonempty := by
    by_contra h
    have he : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [he, trialWeight] at hpos
  refine ⟨hne, ?_⟩
  have hsum : 0 < ∑ j ∈ I, p j :=
    Finset.sum_pos (fun j hj => hp j (hIN hj)) hne
  rw [rho, lt_div_iff₀ hsum]
  simp only [trialWeight, Finset.sum_sub_distrib, ← Finset.mul_sum] at hpos
  linarith

#print axioms solution
