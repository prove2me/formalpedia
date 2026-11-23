-- Prove2me | solution 1 for GlobalTheory.ddbar_comp_holo
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:20:11.448806+00:00
-- url     : https://prove2.me/submissions/ba37a89f-db9f-4a5b-9212-9b10f71d2d8e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Theorems.Thm_GlobalTheory_del_eq_of_hasFDerivAt
import Theorems.Thm_GlobalTheory_dbar_comp_holo
import Theorems.Thm_GlobalTheory_eventually_differentiableAt_of_contDiffAt_two

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
theorem _root_.solution {u : F → G} {φ : E → F} (hu : ContDiffAt ℝ 2 u (φ z))
    (hφ : ContDiffAt ℂ 2 φ z) (v w : E) :
    ddbar (fun x => u (φ x)) z v w = ddbar u (φ z) (fderiv ℂ φ z v) (fderiv ℂ φ z w) := by
  have hφR : ContDiffAt ℝ 2 φ z := hφ.restrict_scalars ℝ
  have hφ1 : DifferentiableAt ℂ φ z := hφ.differentiableAt two_ne_zero
  have hc : ContDiffAt ℝ 2 (fun x => u (φ x)) z := hu.comp z hφR
  rw [ddbar_eq_del_dbar hc]
  have he : (fun x => dbar (fun x => u (φ x)) x w) =ᶠ[𝓝 z]
      fun x => antilinPart (fderiv ℝ u (φ x)) (fderiv ℂ φ x w) := by
    filter_upwards [eventually_differentiableAt_of_contDiffAt_two hφ,
      hφ.continuousAt.eventually (eventually_differentiableAt_of_contDiffAt_two hu)] with x h1 h2
    exact dbar_comp_holo h2 h1 w
  have hψ : DifferentiableAt ℂ (fun x => fderiv ℂ φ x w) z :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
      (differentiableAt_const _)
  have hA : HasFDerivAt (fun x => fderiv ℝ u (φ x)) _ z :=
    (differentiableAt_fderiv_of_contDiffAt_two hu).hasFDerivAt.comp z
      (hφ1.hasFDerivAt.restrictScalars ℝ)
  have hψ' := hψ.hasFDerivAt.restrictScalars ℝ
  have h1 := hA.clm_apply hψ'
  have h2 := hA.clm_apply (hψ'.const_smul I)
  have h3 := (h1.add (h2.const_smul I)).const_smul (1 / 2 : ℂ)
  rw [del_congr he, ddbar_apply hu]
  simp only [antilinPart_apply]
  erw [del_eq_of_hasFDerivAt h3]
  simp only [linPart_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.coe_restrictScalars', map_smul, I_smul_I_smul, map_neg, Pi.smul_apply]
  match_scalars
  all_goals first | ring1 | (ring_nf; simp only [I_sq]; ring1)
end GlobalTheory
