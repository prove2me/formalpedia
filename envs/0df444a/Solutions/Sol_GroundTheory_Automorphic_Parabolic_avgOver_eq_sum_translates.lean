-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.avgOver_eq_sum_translates
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:18.010677+00:00
-- url     : https://prove2.me/submissions/5d5e4121-a670-45be-8deb-cbd03265736f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_eq_sum

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
  {K : Subgroup G} {f : G → W}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution
    [Fintype (K ⧸ (rightStab f).subgroupOf K)] :
    avgOver K f = (((rightStab f).relIndex K : ℂ)⁻¹) •
      ∑ q : K ⧸ (rightStab f).subgroupOf K, fun y => f (y * ((Quotient.out q : K) : G)) := by
  funext x
  rw [avgOver_eq_sum, Pi.smul_apply, Finset.sum_apply]
end GroundTheory.Automorphic.Parabolic
