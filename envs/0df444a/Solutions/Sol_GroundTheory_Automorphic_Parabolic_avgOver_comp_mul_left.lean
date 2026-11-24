-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.avgOver_comp_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:44:05.492785+00:00
-- url     : https://prove2.me/submissions/05b70fe7-ab57-430a-8b2a-1d48adf19272

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_rightStab

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Set
variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]
variable {K : Subgroup G} {f : G → W}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (h x : G) :
    avgOver K (fun y => f (h * y)) x = avgOver K f (h * x) := by
  have hst : rightStab (fun y => f (h * y)) = rightStab f := by
    ext g
    simp only [mem_rightStab]
    constructor
    · intro H y
      have := H (h⁻¹ * y)
      simp only [← mul_assoc, mul_inv_cancel, one_mul] at this
      exact this
    · intro H y
      rw [← mul_assoc, H]
  rw [avgOver, avgOver, avgSub, avgSub, hst]
  simp only [mul_assoc]
end GroundTheory.Automorphic.Parabolic
