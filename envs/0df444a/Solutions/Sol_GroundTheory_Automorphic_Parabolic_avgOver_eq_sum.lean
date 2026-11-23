-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.avgOver_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:20:09.246583+00:00
-- url     : https://prove2.me/submissions/4dd7fb64-7f2f-49f7-bd2c-d06076e53bc7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgSub_eq_sum

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
theorem _root_.solution [Fintype (K ⧸ (rightStab f).subgroupOf K)] (x : G) :
    avgOver K f x = (((rightStab f).relIndex K : ℂ)⁻¹) •
      ∑ q : K ⧸ (rightStab f).subgroupOf K, f (x * ((Quotient.out q : K) : G)) := by
  rw [avgOver, avgSub_eq_sum]
  rfl
end GroundTheory.Automorphic.Parabolic
