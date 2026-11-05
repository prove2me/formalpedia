-- Prove2me | solution 1 for MartOT.Curtain.shadow_mono
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T05:26:50.108979+00:00
-- url     : https://prove2.me/submissions/1126b3f7-7bd5-491e-bc89-d3c2789651c9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MartOT_Var_Setting
import Theorems.Thm_MartOT_Shadow_theorem_4_8
import Theorems.Thm_MartOT_Curtain_lemma_4_6

open MeasureTheory

theorem solution (μ μ' ν : Measure ℝ) (hle : μ ≤ μ') (h : MartOT.Var.ExtConvexLE μ' ν) :
    ∀ η η' : Measure ℝ, MartOT.Var.IsShadow ν μ η → MartOT.Var.IsShadow ν μ' η' → η ≤ η' := by
  intro η η' hη hη'
  obtain ⟨⟨hμ'f, hμ'i⟩, hν, _⟩ := id h
  have hμf : IsFiniteMeasure μ := isFiniteMeasure_of_le μ' hle
  have h1 : MartOT.Var.InM μ := ⟨hμf, hμ'i.mono_measure hle⟩
  have h2 : MartOT.Var.InM (μ' - μ) :=
    ⟨isFiniteMeasure_of_le μ' Measure.sub_le, hμ'i.mono_measure Measure.sub_le⟩
  have hsum : μ + (μ' - μ) = μ' := by rw [add_comm]; exact Measure.sub_add_cancel_of_le hle
  have h' : MartOT.Var.ExtConvexLE (μ + (μ' - μ)) ν := by rw [hsum]; exact h
  have h48 := MartOT.Shadow.theorem_4_8 μ (μ' - μ) ν h1 h2 hν h' η hη
  obtain ⟨⟨η2, hη2, -⟩, -⟩ := MartOT.Curtain.lemma_4_6 (μ' - μ) (ν - η) h48.1
  have hsh := h48.2 η2 hη2
  rw [hsum] at hsh
  have : η' = η + η2 := (MartOT.Curtain.lemma_4_6 μ' ν h).1.unique hη' hsh
  rw [this]
  exact Measure.le_add_right le_rfl
