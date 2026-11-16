-- Prove2me | solution 1 for Kyprianou.Ch01.firstUpperPassage_le_iff_approachingCrossings
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T22:01:38.363005+00:00
-- url     : https://prove2.me/submissions/877b9558-0054-4e5c-8344-10e0860d02a3

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Kyprianou.Ch01
open scoped NNReal
set_option autoImplicit false

/-- First strict crossing is the infimum of crossings approached from above. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (s : ℝ) (ω : Ω) (t : ℝ≥0) :
    Kyprianou.Ch01.firstUpperPassage X s ω ≤ (t : WithTop ℝ≥0) ↔
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ v : ℝ≥0, 0 < v ∧ v < t + ε ∧ s < X v ω := by
  classical
  let S : Set ℝ≥0 := {v | 0 < v ∧ s < X v ω}
  by_cases hne : S.Nonempty
  · have hExists : ∃ v : ℝ≥0, 0 < v ∧ s < X v ω := hne
    have hT : firstUpperPassage X s ω = ((sInf S : ℝ≥0) : WithTop ℝ≥0) := by
      unfold firstUpperPassage
      simp only [if_pos hExists]
      rfl
    rw [hT]
    constructor
    · intro hT ε hε
      have hInf : sInf S ≤ t := WithTop.coe_le_coe.mp hT
      obtain ⟨v, hv, hvlt⟩ :=
        exists_lt_of_csInf_lt hne
          (lt_of_le_of_lt hInf (lt_add_of_pos_right t hε))
      exact ⟨v, hv.1, hvlt, hv.2⟩
    · intro h
      have hInf : sInf S ≤ t := by
        refine le_of_forall_pos_le_add fun ε hε => ?_
        obtain ⟨v, hpos, hv, hcross⟩ := h ε hε
        exact (csInf_le (OrderBot.bddBelow S) (show v ∈ S from ⟨hpos,hcross⟩)).trans hv.le
      exact WithTop.coe_le_coe.mpr hInf
  · have hNo : ¬∃ v : ℝ≥0, 0 < v ∧ s < X v ω := hne
    have hT : firstUpperPassage X s ω = (⊤ : WithTop ℝ≥0) := by
      unfold firstUpperPassage
      simp only [if_neg hNo]
    rw [hT]
    constructor
    · intro h
      exact False.elim (WithTop.not_top_le_coe t h)
    · intro h
      exfalso
      obtain ⟨v, hv, _, hx⟩ := h 1 zero_lt_one
      exact hNo ⟨v,hv,hx⟩
