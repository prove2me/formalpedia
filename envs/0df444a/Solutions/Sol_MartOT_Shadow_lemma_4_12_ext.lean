-- Prove2me | solution 1 for MartOT.Shadow.lemma_4_12_ext
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:17:50.653972+00:00
-- url     : https://prove2.me/submissions/b40992b4-9a6e-4790-b295-17850f76b4c7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MartOT_Var_Setting
import Theorems.Thm_MartOT_Shadow_theorem_4_8

open MeasureTheory NNReal

 theorem solution (α : ℝ≥0) (x : ℝ) (γ ν : Measure ℝ) (hγ : MartOT.Var.InM γ)
    (hν : MartOT.Var.InM ν)
    (h : MartOT.Var.ExtConvexLE ((α : ENNReal) • Measure.dirac x + γ) ν) :
    ∀ η1 : Measure ℝ, MartOT.Var.IsShadow ν ((α : ENNReal) • Measure.dirac x) η1 →
      MartOT.Var.ExtConvexLE γ (ν - η1) := by
  intro η1 hη1
  have hδ : MartOT.Var.InM ((α : ENNReal) • Measure.dirac x) := by
    constructor
    · rw [isFiniteMeasure_iff]
      simp
    · exact (integrable_dirac (a := x) (f := fun y : ℝ => y) (by simp)).smul_measure (by simp)
  exact (MartOT.Shadow.theorem_4_8 ((α : ENNReal) • Measure.dirac x) γ ν
    hδ hγ hν h η1 hη1).1
