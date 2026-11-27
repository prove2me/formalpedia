-- Prove2me | solution 1 for GroundTheory.ProfCoh.piFamilyRep_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:50:36.122604+00:00
-- url     : https://prove2.me/submissions/5869a751-53fb-4328-a85c-4b0016288ca2

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveInvariants
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_ArtinDefs

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
open Representation
open scoped TensorProduct
universe u v
variable {k Γ : Type*} [CommSemiring k] [Monoid Γ]
namespace GroundTheory.ProfCoh
theorem _root_.solution {ι : Type*} (V : ι → Type*) [∀ i, AddCommMonoid (V i)]
    [∀ i, Module k (V i)] (ρ : ∀ i, Representation k Γ (V i)) (γ : Γ) (x : ∀ i, V i) (i : ι) :
    piFamilyRep V ρ γ x i = ρ i γ (x i) :=
  rfl
end GroundTheory.ProfCoh
