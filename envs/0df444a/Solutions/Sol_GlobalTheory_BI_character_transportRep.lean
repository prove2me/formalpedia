-- Prove2me | solution 1 for GlobalTheory.BI.character_transportRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:59:07.349822+00:00
-- url     : https://prove2.me/submissions/e02fa849-4dd3-4c28-98cc-6bb3d8f99d2e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfRepresentation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
noncomputable section
open GlobalTheory GlobalTheory.BI
variable {K G V W : Type} [Field K] [Group G] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
namespace GlobalTheory.BI
theorem _root_.solution [FiniteDimensional K V] [FiniteDimensional K W]
    (ρ : Representation K G V) (e : V ≃ₗ[K] W) (g : G) :
    (transportRep ρ e).character g = ρ.character g :=
  LinearMap.trace_conj' (ρ g) e
end GlobalTheory.BI
