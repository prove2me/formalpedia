-- Prove2me | solution 1 for GlobalTheory.ddbar_const_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:53:15.00001+00:00
-- url     : https://prove2.me/submissions/154e9e80-aa99-481c-93f0-d552886ab2d5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Theorems.Thm_GlobalTheory_eventually_differentiableAt_of_contDiffAt_two
import Theorems.Thm_GlobalTheory_differentiableAt_dbar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology ComplexConjugate
noncomputable section
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedSpace ℝ G]
  [IsScalarTower ℝ ℂ G]
variable {u u' : E → F} {z : E}
namespace GlobalTheory
theorem _root_.solution (c : ℂ) (hu : ContDiffAt ℝ 2 u z) :
    ddbar (fun x => c • u x) z = c • ddbar u z := by
  rw [ddbar, ddbar, ← del_const_smul c (differentiableAt_dbar hu)]
  refine del_congr ?_
  filter_upwards [eventually_differentiableAt_of_contDiffAt_two hu] with x h1
    using dbar_const_smul c h1
end GlobalTheory
