-- Prove2me | solution 1 for GlobalTheory.del_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:33:59.8942+00:00
-- url     : https://prove2.me/submissions/a0a06643-13df-40fb-9722-540b600bfc39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo

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
variable {f g : E → F} {z : E}
namespace GlobalTheory
theorem _root_.solution (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    del (fun x => f x - g x) z = del f z - del g z := by
  rw [del, fderiv_fun_sub hf hg]; exact (linPartCLM E F).map_sub _ _
end GlobalTheory
