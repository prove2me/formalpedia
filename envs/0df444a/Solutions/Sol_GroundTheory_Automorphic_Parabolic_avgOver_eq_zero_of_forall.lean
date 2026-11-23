-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.avgOver_eq_zero_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:17.956927+00:00
-- url     : https://prove2.me/submissions/ae773458-92c8-411d-9302-2863a47aa78e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCount

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
theorem _root_.solution {K : Subgroup G} {f : G → W} {x : G}
    (h0 : ∀ k ∈ K, f (x * k) = 0) : avgOver K f x = 0 := by
  unfold avgOver avgSub
  rw [finsum_eq_zero_of_forall_eq_zero (fun q => h0 _ (Quotient.out q).2), smul_zero]
end GroundTheory.Automorphic.Parabolic
