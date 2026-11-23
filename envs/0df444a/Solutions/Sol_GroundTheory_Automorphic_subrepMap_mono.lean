-- Prove2me | solution 1 for GroundTheory.Automorphic.subrepMap_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:16.323108+00:00
-- url     : https://prove2.me/submissions/699f20d6-3b0b-4764-9c71-64a29ea4cc76

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthLattice

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
open Function
variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {ρ : Representation ℂ G V}
variable {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W}
namespace GroundTheory.Automorphic
theorem _root_.solution (f : Representation.IntertwiningMap ρ σ) : Monotone (subrepMap f) :=
  fun _ _ h _ ⟨x, hx, hxy⟩ => ⟨x, h hx, hxy⟩
end GroundTheory.Automorphic
