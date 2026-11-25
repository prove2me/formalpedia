-- Prove2me | solution 1 for GroundTheory.ProfCoh.isIntertwiningMap_modNMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:24:41.346576+00:00
-- url     : https://prove2.me/submissions/7b8bfd45-bd4f-432a-9ddf-d4212ff60ea9

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveSnake

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
universe u v
open Representation
variable {Γ : Type*} [Group Γ] {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [DistribMulAction Γ A] [DistribMulAction Γ B] [DistribMulAction Γ C] (n : ℕ)
namespace GroundTheory.ProfCoh
theorem _root_.solution {f : A →+ B} (hfγ : ∀ (γ : Γ) (a : A), f (γ • a) = γ • f a) :
    (modNRep Γ A n).IsIntertwiningMap (modNRep Γ B n) (modNMap n f) :=
  ⟨fun γ x => by
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact congrArg Submodule.Quotient.mk (hfγ γ a)⟩
end GroundTheory.ProfCoh
