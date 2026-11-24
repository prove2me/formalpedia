-- Prove2me | solution 1 for GroundTheory.Automorphic.hasFiniteLength_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:53:06.728712+00:00
-- url     : https://prove2.me/submissions/2702732d-2a65-45e4-ad44-097b14b74a71

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthLattice
import Theorems.Thm_GroundTheory_Automorphic_HasFiniteLength_wellFoundedLT
import Theorems.Thm_GroundTheory_Automorphic_HasFiniteLength_wellFoundedGT
import Theorems.Thm_GroundTheory_Automorphic_hasFiniteLength_of_strictMono
import Theorems.Thm_GroundTheory_Automorphic_subrepMap_mono

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
    (hf : Injective f) (hσ : HasFiniteLength σ) : HasFiniteLength ρ := by
  have := hσ.wellFoundedLT
  have := hσ.wellFoundedGT
  refine hasFiniteLength_of_strictMono (ι := Unit) (α := fun _ => Subrepresentation σ)
    (fun A _ => subrepMap f A) fun A B hAB => ?_
  refine lt_of_le_of_ne (fun _ => subrepMap_mono f hAB.le) fun h => hAB.ne ?_
  have h1 := congrFun h ()
  refine le_antisymm hAB.le fun x hx => ?_
  obtain ⟨y, hy, hyx⟩ : f x ∈ subrepMap f A := by
    show f x ∈ subrepMap f A
    rw [show subrepMap f A = subrepMap f B from h1]
    exact ⟨x, hx, rfl⟩
  rw [← hf hyx]
  exact hy
end GroundTheory.Automorphic
