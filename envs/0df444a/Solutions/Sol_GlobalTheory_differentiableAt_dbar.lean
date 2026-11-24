-- Prove2me | solution 1 for GlobalTheory.differentiableAt_dbar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:43:35.058696+00:00
-- url     : https://prove2.me/submissions/427230c9-6408-4a63-a97b-ada9afada45d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Theorems.Thm_GlobalTheory_contDiffAt_dbar

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
theorem _root_.solution (hu : ContDiffAt ℝ 2 u z) : DifferentiableAt ℝ (dbar u) z :=
  (contDiffAt_dbar (m := 1) hu (by norm_num)).differentiableAt one_ne_zero
end GlobalTheory
