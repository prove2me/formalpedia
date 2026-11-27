-- Prove2me | solution 1 for GlobalTheory.del_clm_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:37:27.100687+00:00
-- url     : https://prove2.me/submissions/bc41d0e7-56c7-4f56-ae5a-6134bbf46d5f

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
theorem _root_.solution (T : F →L[ℂ] G) (hf : DifferentiableAt ℝ f z) (v : E) :
    del (fun x => T (f x)) z v = T (del f z v) := by
  rw [del_eq_of_hasFDerivAt (f := fun x => T (f x))
    ((T.restrictScalars ℝ).hasFDerivAt.comp z hf.hasFDerivAt)]
  simp [linPart_apply, del_apply]
end GlobalTheory
