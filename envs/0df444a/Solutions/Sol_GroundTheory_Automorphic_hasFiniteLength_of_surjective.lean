-- Prove2me | solution 1 for GroundTheory.Automorphic.hasFiniteLength_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:08:11.506802+00:00
-- url     : https://prove2.me/submissions/a92d64d1-8f84-41f1-ab5c-3d0c0bb841d3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthLattice
import Theorems.Thm_GroundTheory_Automorphic_HasFiniteLength_wellFoundedLT
import Theorems.Thm_GroundTheory_Automorphic_HasFiniteLength_wellFoundedGT
import Theorems.Thm_GroundTheory_Automorphic_hasFiniteLength_of_strictMono
import Theorems.Thm_GroundTheory_Automorphic_subrepComap_mono

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
theorem _root_.solution (f : Representation.IntertwiningMap ρ σ)
    (hf : Surjective f) (hρ : HasFiniteLength ρ) : HasFiniteLength σ := by
  have := hρ.wellFoundedLT
  have := hρ.wellFoundedGT
  refine hasFiniteLength_of_strictMono (ι := Unit) (α := fun _ => Subrepresentation ρ)
    (fun B _ => subrepComap f B) fun A B hAB => ?_
  refine lt_of_le_of_ne (fun _ => subrepComap_mono f hAB.le) fun h => hAB.ne ?_
  have h1 := congrFun h ()
  refine le_antisymm hAB.le fun y hy => ?_
  obtain ⟨x, rfl⟩ := hf y
  have hx : x ∈ subrepComap f B := hy
  rw [← show subrepComap f A = subrepComap f B from h1] at hx
  exact hx
end GroundTheory.Automorphic
