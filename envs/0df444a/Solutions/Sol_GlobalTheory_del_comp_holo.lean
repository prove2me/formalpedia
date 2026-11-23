-- Prove2me | solution 1 for GlobalTheory.del_comp_holo
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:00.824843+00:00
-- url     : https://prove2.me/submissions/6bf82447-8b54-48fd-ae8e-f71770bc9f41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Theorems.Thm_GlobalTheory_del_eq_of_hasFDerivAt

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
theorem _root_.solution {u : F → G} {φ : E → F} (hu : DifferentiableAt ℝ u (φ z))
    (hφ : DifferentiableAt ℂ φ z) (v : E) :
    del (fun x => u (φ x)) z v = del u (φ z) (fderiv ℂ φ z v) := by
  rw [del_eq_of_hasFDerivAt (f := fun x => u (φ x))
    (hu.hasFDerivAt.comp z (hφ.hasFDerivAt.restrictScalars ℝ))]
  simp [linPart_apply, del_apply]
end GlobalTheory
