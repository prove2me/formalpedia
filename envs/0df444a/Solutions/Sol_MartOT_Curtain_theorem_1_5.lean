-- Prove2me | solution 1 for MartOT.Curtain.theorem_1_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T05:06:48.857079+00:00
-- url     : https://prove2.me/submissions/544741ee-763d-474a-90a2-90bf88564318
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MartOT_Var_Setting
import Theorems.Thm_MartOT_Curtain_theorem_4_18
import Theorems.Thm_MartOT_Curtain_theorem_4_21
import Theorems.Thm_MartOT_Curtain_theorem_5_3

open MeasureTheory

theorem solution (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : MartOT.Var.ConvexLE μ ν) :
    ∃! π : Measure (ℝ × ℝ), MartOT.Var.IsMartingalePlan μ ν π ∧ MartOT.Var.IsLeftMonotone π := by
  obtain ⟨⟨πlc, hlc, huniq⟩, hmart⟩ := MartOT.Curtain.theorem_4_18 μ ν hμν
  refine ⟨πlc, ⟨(hmart πlc hlc).2, MartOT.Curtain.theorem_4_21 μ ν hμν πlc hlc⟩, ?_⟩
  rintro π ⟨hπ, hmono⟩
  exact huniq π (MartOT.Curtain.theorem_5_3 μ ν hμν.1 hμν.2.1 π hπ hmono)
