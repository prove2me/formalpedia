-- Prove2me | solution 1 for MartOT.Curtain.theorem_5_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T05:12:59.722207+00:00
-- url     : https://prove2.me/submissions/427b39a7-71e3-4ba8-9323-e460440f6e06

import Mathlib
import Definitions.Def_MartOT_Var_Setting
import Theorems.Thm_MartOT_Opt_theorem_5_3

open MeasureTheory

theorem solution (μ ν : Measure ℝ) (hμ : MartOT.Var.InM μ) (hν : MartOT.Var.InM ν) (π : Measure (ℝ × ℝ))
    (hπ : MartOT.Var.IsMartingalePlan μ ν π) (hmono : MartOT.Var.IsLeftMonotone π) :
    MartOT.Var.IsLeftCurtain μ ν π := by
  obtain ⟨h1, h2⟩ := hπ.1
  have hfin : IsFiniteMeasure π := by
    haveI := hμ.1
    refine ⟨?_⟩
    have : π Set.univ = (π.map Prod.fst) Set.univ := by
      rw [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ]
    rw [this, h1]; exact measure_lt_top μ _
  subst h1 h2
  exact MartOT.Opt.theorem_5_3 π hμ hν hπ hmono
