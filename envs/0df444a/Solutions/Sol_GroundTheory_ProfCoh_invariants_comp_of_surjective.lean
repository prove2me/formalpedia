-- Prove2me | solution 1 for GroundTheory.ProfCoh.invariants_comp_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:48:53.967366+00:00
-- url     : https://prove2.me/submissions/c812a5bc-1486-417a-9483-a30e950d4570

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_CoprimeRegular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open Representation TensorProduct
variable {k Γ₁ Γ₂ X : Type*} [CommRing k] [Group Γ₁] [Group Γ₂] [AddCommGroup X] [Module k X]
namespace GroundTheory.ProfCoh
theorem _root_.solution (ρ : Representation k Γ₁ X) (e : Γ₂ →* Γ₁)
    (he : Function.Surjective e) :
    Representation.invariants (ρ.comp e) = ρ.invariants := by
  ext x
  simp only [mem_invariants]
  exact ⟨fun h γ => by obtain ⟨δ, rfl⟩ := he γ; exact h δ, fun h δ => h (e δ)⟩
end GroundTheory.ProfCoh
