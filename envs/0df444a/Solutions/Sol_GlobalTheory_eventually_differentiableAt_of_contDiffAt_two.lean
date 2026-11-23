-- Prove2me | solution 1 for GlobalTheory.eventually_differentiableAt_of_contDiffAt_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:21.835801+00:00
-- url     : https://prove2.me/submissions/65a849f9-cafb-4d3a-89a0-2af5b5e5ffa5

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
theorem _root_.solution {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] (hu : ContDiffAt 𝕜 2 u z) :
    ∀ᶠ x in 𝓝 z, DifferentiableAt 𝕜 u x :=
  (hu.eventually (by simp)).mono fun _ hx => hx.differentiableAt two_ne_zero
end GlobalTheory
