-- Prove2me | solution 1 for OAI.QuinticLienard.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T18:13:18.777293+00:00
-- url     : https://prove2.me/submissions/8566fb2a-5d0f-4cc4-8c55-f473ce13dd2e

import Mathlib
import Definitions.Def_QuinticLienard
import Definitions.Def_OAIQWQL000
import Theorems.Thm_OAI_QuinticLienard_Sharpness_sharpness
import Theorems.Thm_OAI_QuinticLienard_upper_bound

section
-- module Solutions.OAIQW_QuinticLienard.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff NNReal

namespace QuinticLienard
theorem main_oai :
    (∀ F : Polynomial ℝ, F.degree ≤ 5 → {C : Set Plane | IsLimitCycle F C}.encard ≤ 2) ∧
    (∃ F : Polynomial ℝ, F.degree ≤ 5 ∧ {C : Set Plane | IsLimitCycle F C}.encard = 2) :=
  ⟨upper_bound,Sharpness.sharpness⟩
end QuinticLienard

end OAI
end

theorem solution : type_of% @OAI.QuinticLienard.main_oai := @OAI.QuinticLienard.main_oai
