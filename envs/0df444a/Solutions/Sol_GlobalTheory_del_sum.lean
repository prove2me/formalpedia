-- Prove2me | solution 1 for GlobalTheory.del_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:00.833915+00:00
-- url     : https://prove2.me/submissions/b0cdd1f7-524a-42fa-9479-6e0a835fa883

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
theorem _root_.solution {ι : Type*} {t : Finset ι} {A : ι → E → F}
    (h : ∀ i ∈ t, DifferentiableAt ℝ (A i) z) :
    del (fun x => ∑ i ∈ t, A i x) z = ∑ i ∈ t, del (A i) z := by
  rw [del, fderiv_fun_sum h]; exact map_sum (linPartCLM E F) _ _
end GlobalTheory
