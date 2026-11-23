-- Prove2me | solution 1 for Kyprianou.Ch01.positiveContinuousPairCommonCompactBounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T09:37:23.253606+00:00
-- url     : https://prove2.me/submissions/337feb69-4c72-4b34-82ae-cc3b90d73c5c

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 Set Filter
open scoped Topology
set_option autoImplicit false

theorem solution
    (f g : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hfCont : ContinuousOn f (Set.Icc 0 T))
    (hgCont : ContinuousOn g (Set.Icc 0 T))
    (hfPos : ∀ t ∈ Set.Icc 0 T, 0 < f t)
    (hgPos : ∀ t ∈ Set.Icc 0 T, 0 < g t) :
    ∃ δ B : ℝ, 0 < δ ∧ δ ≤ B ∧
      (∀ t ∈ Set.Icc 0 T,
        f t ∈ Set.Icc δ B ∧ g t ∈ Set.Icc δ B) := by
  have hComp : IsCompact (Set.Icc (0 : ℝ) T) := isCompact_Icc
  have hNonempty : (Set.Icc (0 : ℝ) T).Nonempty :=
    ⟨0, ⟨le_rfl, hT⟩⟩
  obtain ⟨tf, htf, hfmin⟩ := hComp.exists_isMinOn hNonempty hfCont
  obtain ⟨tg, htg, hgmin⟩ := hComp.exists_isMinOn hNonempty hgCont
  obtain ⟨uf, huf, hfmax⟩ := hComp.exists_isMaxOn hNonempty hfCont
  obtain ⟨ug, hug, hgmax⟩ := hComp.exists_isMaxOn hNonempty hgCont
  let δ : ℝ := min (f tf) (g tg)
  let B : ℝ := max (f uf) (g ug)
  have hδ : 0 < δ := lt_min (hfPos tf htf) (hgPos tg htg)
  have hδB : δ ≤ B := by
    exact (min_le_left _ _).trans
      ((hfmax htf).trans (le_max_left _ _))
  refine ⟨δ, B, hδ, hδB, ?_⟩
  intro t ht
  constructor
  · exact ⟨(min_le_left _ _).trans (hfmin ht),
      (hfmax ht).trans (le_max_left _ _)⟩
  · exact ⟨(min_le_right _ _).trans (hgmin ht),
      (hgmax ht).trans (le_max_right _ _)⟩
