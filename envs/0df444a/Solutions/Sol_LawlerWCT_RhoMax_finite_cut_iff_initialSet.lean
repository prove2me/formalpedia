-- Prove2me | solution 1 for LawlerWCT.RhoMax.finite_cut_iff_initialSet
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:50:33.312984+00:00
-- url     : https://prove2.me/submissions/3e4419f4-97d6-4961-aba5-e4bf627de716

import Mathlib
import Definitions.Def_LawlerWCT_RhoMax_Model
open LawlerWCT.RhoMax

theorem solution {ι : Type*} [DecidableEq ι] (N : Finset ι)
    (G : ι → ι → Prop) (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N) (w : ι → ℝ)
    (T : Finset (Node ι)) (hT : T ⊆ nodes N) (ht : Node.t ∈ T) (hs : Node.s ∉ T) :
    cutCapacity N G w T < ⊤ ↔ LawlerWCT.SeriesPar.IsInitialSet G N (jobsOf N T) := by
  classical
  have hcut : cutCapacity N G w T < ⊤ ↔
      ∀ i ∈ N, Node.job i ∉ T → ∀ j ∈ N, Node.job j ∈ T → ¬ G i j := by
    rw [lt_top_iff_ne_top]
    simp only [cutCapacity, WithTop.sum_ne_top]
    constructor
    · intro h i hi hit j hj hjt hg
      have hh := h (.job i) (by simp [nodes, hi, hit]) (.job j) hjt
      simpa [cap, hg] using hh
    · intro h u hu v hv
      have huN := (Finset.mem_sdiff.mp hu).1
      have huT := (Finset.mem_sdiff.mp hu).2
      cases u with
      | s => cases v <;> simp [cap]
      | t => cases v <;> simp [cap]
      | job i =>
        have hi : i ∈ N := by simpa [nodes] using huN
        cases v with
        | s => simp [cap]
        | t => simp [cap]
        | job j =>
          have hj : j ∈ N := by simpa [nodes] using hT hv
          simp [cap, h i hi huT j hj hv]
  rw [hcut]
  constructor
  · intro h
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro j hj i hi hg
    have hjT : Node.job j ∈ T := (Finset.mem_filter.mp hj).2
    have hc : ∀ a b, G a b → Node.job b ∈ T → Node.job a ∈ T := by
      intro a b hab hb
      by_contra ha
      exact h a (hGN a b hab).1 ha b (hGN a b hab).2 hb hab
    have hiT : Node.job i ∈ T := by
      induction hg using Relation.TransGen.head_induction_on with
      | single hab => exact hc _ _ hab hjT
      | head hab hbc ih => exact hc _ _ hab (ih (hGN _ _ hab).2)
    exact Finset.mem_filter.mpr ⟨hi, hiT⟩
  · intro h i hi hit j hj hjt hg
    have hjI : j ∈ jobsOf N T := Finset.mem_filter.mpr ⟨hj, hjt⟩
    have hiI := h.2 j hjI i hi (Relation.TransGen.single hg)
    exact hit (Finset.mem_filter.mp hiI).2


#print axioms solution
