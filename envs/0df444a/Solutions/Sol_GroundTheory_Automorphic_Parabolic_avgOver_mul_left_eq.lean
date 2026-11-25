-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.avgOver_mul_left_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:15:27.91515+00:00
-- url     : https://prove2.me/submissions/610b6b85-35f4-4030-a860-bc95d7213ced

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCount
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_comp_linearMap
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_comp_mul_left


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
variable {A : Subgroup G}
variable (θ : A → W →ₗ[ℂ] W)
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {K : Subgroup G} {h : G → W}
    (hh : ∀ a : A, ∀ y, h ((a : G) * y) = θ a (h y)) (hf : AvgFinite K h) (a : A) (y : G) :
    avgOver K h ((a : G) * y) = θ a (avgOver K h y) := by
  rw [← avgOver_comp_mul_left, ← avgOver_comp_linearMap hf (θ a)]
  congr 1
  funext z
  exact hh a z
end GroundTheory.Automorphic.Parabolic
