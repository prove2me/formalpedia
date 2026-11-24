-- Prove2me | solution 1 for GlobalTheory.ddbar_eq_zero_of_holomorphic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:33:59.13426+00:00
-- url     : https://prove2.me/submissions/14cf4680-4e24-43cf-88e6-355d1a0aa1b7

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
variable {u u' : E → F} {z : E}
namespace GlobalTheory
theorem _root_.solution (hu : ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ u x) :
    ddbar u z = 0 := by
  rw [ddbar, ← del_const (0 : E →L⋆[ℂ] F) z]
  exact del_congr (hu.mono fun _ hx => dbar_eq_zero hx)
end GlobalTheory
