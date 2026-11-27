-- Prove2me | solution 1 for GlobalTheory.del_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:37:31.042043+00:00
-- url     : https://prove2.me/submissions/83901b60-35e8-4caa-99b0-fd5c90607526

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Theorems.Thm_GlobalTheory_del_add_dbar

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
    (hφ : DifferentiableAt ℝ φ z) (v : E) :
    del (fun x => u (φ x)) z v = del u (φ z) (del φ z v) + dbar u (φ z) (dbar φ z v) := by
  have h : HasFDerivAt (fun x => u (φ x)) _ z := hu.hasFDerivAt.comp z hφ.hasFDerivAt
  rw [del_apply, h.fderiv, del_apply φ, dbar_apply φ]
  simp only [ContinuousLinearMap.comp_apply, ← del_add_dbar u, map_smul, map_sub, map_add,
    map_smulₛₗ, conj_I, map_div₀, map_one, map_ofNat]
  module
end GlobalTheory
