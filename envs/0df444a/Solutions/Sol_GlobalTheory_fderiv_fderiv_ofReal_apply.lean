-- Prove2me | solution 1 for GlobalTheory.fderiv_fderiv_ofReal_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:10.915398+00:00
-- url     : https://prove2.me/submissions/69e6da63-ddde-450b-a0b7-2d48a3342dee

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
variable {u u' : E → ℝ} {z : E}
namespace GlobalTheory
theorem _root_.solution (hu : ContDiffAt ℝ 2 u z) (v w : E) :
    fderiv ℝ (fderiv ℝ fun x => (u x : ℂ)) z v w = (fderiv ℝ (fderiv ℝ u) z v w : ℂ) := by
  have h := differentiableAt_fderiv_of_contDiffAt_two (F := ℂ) (contDiffAt_ofReal_comp hu)
  have h' : DifferentiableAt ℝ (fderiv ℝ u) z :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have h1 : DifferentiableAt ℝ (fun x => fderiv ℝ u x w) z := h'.clm_apply (differentiableAt_const _)
  have he : (fun x => fderiv ℝ (fun x => (u x : ℂ)) x w) =ᶠ[𝓝 z]
      fun x => ((fderiv ℝ u x w : ℝ) : ℂ) :=
    (hu.eventually (by simp)).mono fun _ hx => fderiv_ofReal_apply (hx.differentiableAt two_ne_zero) w
  rw [← fderiv_fderiv_apply (contDiffAt_ofReal_comp hu), he.fderiv_eq, fderiv_ofReal_apply h1,
    fderiv_clm_apply h' (differentiableAt_const _)]
  simp
end GlobalTheory
