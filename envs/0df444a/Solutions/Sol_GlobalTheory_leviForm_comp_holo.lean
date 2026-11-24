-- Prove2me | solution 1 for GlobalTheory.leviForm_comp_holo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:14:51.930812+00:00
-- url     : https://prove2.me/submissions/5cf8c0da-b2e7-4ea6-ac18-ba5088f1bb18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Theorems.Thm_GlobalTheory_ddbar_comp_holo

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
variable {u u' : E → ℝ} {z : E}
namespace GlobalTheory
theorem _root_.solution {u : F → ℝ} {φ : E → F} (hu : ContDiffAt ℝ 2 u (φ z))
    (hφ : ContDiffAt ℂ 2 φ z) (v w : E) :
    leviForm (fun x => u (φ x)) z v w = leviForm u (φ z) (fderiv ℂ φ z v) (fderiv ℂ φ z w) :=
  ddbar_comp_holo (u := fun y => (u y : ℂ)) (contDiffAt_ofReal_comp hu) hφ v w
end GlobalTheory
