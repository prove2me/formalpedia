-- Prove2me | solution 1 for GroundTheory.ProfCoh.nonempty_equiv_funPermRep_of_card_fixedBy_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:47:44.381623+00:00
-- url     : https://prove2.me/submissions/e5d0488d-9851-4ca7-9d8c-c42804340181

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_Additive
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Lattice
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsPerm
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_PermLatticeDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_PermLatticeCharacter
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_PermLattice
import Theorems.Thm_GroundTheory_ProfCoh_character_funPermRep
import Theorems.Thm_GroundTheory_ProfCoh_nonempty_equiv_of_character_eq


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
open Module Representation GroundTheory.Global
open scoped TensorProduct
universe u v
variable {k : Type*} {Γ : Type*} [Field k] [Group Γ]
namespace GroundTheory.ProfCoh
theorem _root_.solution [CharZero k] [Finite Γ] {X X' : Type*}
    [MulAction Γ X] [MulAction Γ X'] [Finite X] [Finite X']
    (h : ∀ γ : Γ, Nat.card (MulAction.fixedBy X γ) = Nat.card (MulAction.fixedBy X' γ)) :
    Nonempty ((funPermRep k Γ X).Equiv (funPermRep k Γ X')) := by
  classical
  have := Fintype.ofFinite X
  have := Fintype.ofFinite X'
  exact nonempty_equiv_of_character_eq _ _ (funext fun γ => by
    rw [character_funPermRep, character_funPermRep, h])
end GroundTheory.ProfCoh
