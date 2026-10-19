-- Prove2me | solution 1 for OAI.CriticalZ3.Box.separated_subset
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:52:32.109+00:00
-- url     : https://prove2.me/submissions/9ed9051c-a94a-4e50-89b8-8af522b1d94a

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry

open OAI OAI.CriticalZ3 OAI.CriticalZ3.Box
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open Classical
theorem cz_near_card (s : Finset Vertex) (a : Vertex) (m : ℕ) :
    (s.filter (fun b => ¬ ∃ i, (4*m+2 : ℤ) < |a i - b i|)).card ≤ (8*m+5)^3 := by
  have hsub : s.filter (fun b => ¬ ∃ i, (4*m+2 : ℤ) < |a i - b i|) ⊆
      Finset.Icc (fun i => a i - (4*m+2 : ℤ)) (fun i => a i + (4*m+2 : ℤ)) := by
    intro b hb
    simp only [Finset.mem_filter, not_exists, not_lt] at hb
    rw [Finset.mem_Icc]
    constructor <;> intro i <;> have := abs_le.mp (hb.2 i) <;> simp only <;> linarith [this.1, this.2]
  refine (Finset.card_le_card hsub).trans (le_of_eq ?_)
  rw [Pi.card_Icc, Fin.prod_univ_three]
  simp only [Int.card_Icc]
  have : ∀ i : Fin 3, (a i + (4*m+2 : ℤ) + 1 - (a i - (4*m+2 : ℤ))).toNat = 8*m+5 := by
    intro i; omega
  rw [this 0, this 1, this 2]; ring

theorem solution (s : Finset Vertex) (m K : ℕ)
    (hcard : K*(8*m+5)^3 ≤ s.card) :
    ∃ t ⊆ s, t.card = K ∧
      ∀ a ∈ t, ∀ b ∈ t, a ≠ b → ∃ i, (4*m+2 : ℤ) < |a i-b i| := by
  induction K generalizing s with
  | zero => exact ⟨∅, Finset.empty_subset _, rfl, by simp⟩
  | succ K ih =>
    have hpos : 0 < s.card := by
      have : 0 < (K+1)*(8*m+5)^3 := by positivity
      omega
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
    set s' := s.filter (fun b => ∃ i, (4*m+2 : ℤ) < |a i - b i|) with hs'
    have hcard' : K*(8*m+5)^3 ≤ s'.card := by
      have h1 := Finset.card_filter_add_card_filter_not
        (s := s) (fun b => ∃ i, (4*m+2 : ℤ) < |a i - b i|)
      have h2 := cz_near_card s a m
      rw [← hs'] at h1
      nlinarith
    obtain ⟨t', ht's, ht'card, ht'sep⟩ := ih s' hcard'
    have haT : a ∉ t' := by
      intro hat
      have := (Finset.mem_filter.mp (ht's hat)).2
      obtain ⟨i, hi⟩ := this
      simp at hi; linarith
    refine ⟨insert a t', ?_, ?_, ?_⟩
    · exact Finset.insert_subset ha (ht's.trans (Finset.filter_subset _ _))
    · rw [Finset.card_insert_of_notMem haT, ht'card]
    · intro x hx y hy hxy
      rw [Finset.mem_insert] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact absurd rfl hxy
      · exact (Finset.mem_filter.mp (ht's hy)).2
      · obtain ⟨i, hi⟩ := (Finset.mem_filter.mp (ht's hx)).2
        exact ⟨i, by rwa [abs_sub_comm]⟩
      · exact ht'sep x hx y hy hxy

