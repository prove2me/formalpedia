-- Prove2me | solution 1 for GlobalTheory.HermFrame.curv_comp_holo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:48:39.273878+00:00
-- url     : https://prove2.me/submissions/5a6b80ca-c390-4cb5-ac77-8e8417c1612b

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Theorems.Thm_GlobalTheory_HermFrame_curv_eq
import Theorems.Thm_GlobalTheory_dbar_comp_holo
import Theorems.Thm_GlobalTheory_ddbar_comp_holo
import Theorems.Thm_GlobalTheory_del_comp_holo


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m n l : Type*}
variable [Fintype n] [DecidableEq n]
variable {U : Set E} {H H' : E → Matrix n n ℂ} {z : E} {j k : WithTop ℕ∞}
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [NormedSpace ℝ E']
  [IsScalarTower ℝ ℂ E'] {φ : E' → E} {w : E'}
namespace GlobalTheory.HermFrame
theorem _root_.solution (h : MContDiffAt 2 H (φ w)) (hu : IsUnit (H (φ w)).det)
    (hφ : ContDiffAt ℂ 2 φ w) (ξ η : E') :
    curv (fun x => H (φ x)) w ξ η = curv H (φ w) (fderiv ℂ φ w ξ) (fderiv ℂ φ w η) := by
  have hφ1 := hφ.differentiableAt two_ne_zero
  have h1 : MContDiffAt 1 H (φ w) := h.of_le one_le_two
  have hc : MContDiffAt 2 (fun x => H (φ x)) w :=
    fun a b => (h a b).comp w (hφ.restrict_scalars ℝ)
  have e1 : mdel (fun x => H (φ x)) w ξ = mdel H (φ w) (fderiv ℂ φ w ξ) := by
    ext a b; exact del_comp_holo (u := fun y => H y a b) (h1.diff a b) hφ1 ξ
  have e2 : mdbar (fun x => H (φ x)) w η = mdbar H (φ w) (fderiv ℂ φ w η) := by
    ext a b; exact dbar_comp_holo (u := fun y => H y a b) (h1.diff a b) hφ1 η
  have e3 : mddbar (fun x => H (φ x)) w ξ η =
      mddbar H (φ w) (fderiv ℂ φ w ξ) (fderiv ℂ φ w η) := by
    ext a b; exact ddbar_comp_holo (u := fun y => H y a b) (h a b) hφ ξ η
  rw [curv_eq hc hu, curv_eq h hu, e1, e2, e3]
end GlobalTheory.HermFrame
