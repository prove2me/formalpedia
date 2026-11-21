-- Prove2me | solution 1 for Kyprianou.Ch01.firstUpperPassage_crossingBefore_of_ltV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T23:34:04.207485+00:00
-- url     : https://prove2.me/submissions/e50cae40-ddf3-4183-9d42-c8a91df96fe7

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Mathlib.MeasureTheory.MeasurableSpace.Defs
open Kyprianou.Ch01 Set
open scoped NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (s : ℝ) (ω : Ω) (t : ℝ≥0)
    (h : firstUpperPassage X s ω < (t : WithTop ℝ≥0)) :
    ∃ v : ℝ≥0, 0 < v ∧ v < t ∧ s < X v ω := by
  classical
  let S : Set ℝ≥0 := {u | 0 < u ∧ s < X u ω}
  by_cases hne : S.Nonempty
  · have hex : ∃ u : ℝ≥0, 0 < u ∧ s < X u ω := hne
    have hT : firstUpperPassage X s ω =
        ((sInf S : ℝ≥0) : WithTop ℝ≥0) := by
      unfold firstUpperPassage
      simp only [if_pos hex]
      rfl
    rw [hT] at h
    have hInf : sInf S < t := WithTop.coe_lt_coe.mp h
    obtain ⟨v, hv, hvlt⟩ := exists_lt_of_csInf_lt hne hInf
    exact ⟨v, hv.1, hvlt, hv.2⟩
  · have hnot : ¬∃ u : ℝ≥0, 0 < u ∧ s < X u ω := hne
    have hT : firstUpperPassage X s ω = (⊤ : WithTop ℝ≥0) := by
      unfold firstUpperPassage
      simp only [if_neg hnot]
    rw [hT] at h
    exact False.elim ((not_lt_of_ge le_top) h)
