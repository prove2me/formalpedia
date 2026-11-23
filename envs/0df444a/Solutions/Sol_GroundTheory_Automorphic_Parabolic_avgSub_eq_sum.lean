-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.avgSub_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:21.569567+00:00
-- url     : https://prove2.me/submissions/bac3ff71-8b93-4132-b83b-df59b6a5de65

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage

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
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (K : Subgroup G) (S : Subgroup K) [Fintype (K ⧸ S)] (f : G → W) (x : G) :
    avgSub K S f x = ((S.index : ℂ)⁻¹) • ∑ q : K ⧸ S, f (x * ((Quotient.out q : K) : G)) := by
  rw [avgSub, finsum_eq_sum_of_fintype]
end GroundTheory.Automorphic.Parabolic
