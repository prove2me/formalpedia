-- Prove2me | solution 1 for GroundTheory.Automorphic.subrepComap_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:04:20.11018+00:00
-- url     : https://prove2.me/submissions/bbd8b9b4-4773-489b-9036-0985775fc741

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
theorem _root_.solution (f : Representation.IntertwiningMap ρ σ) : Monotone (subrepComap f) :=
  fun _ _ h _ hx => h hx
end GroundTheory.Automorphic
