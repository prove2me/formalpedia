-- Prove2me | solution 1 for GroundTheory.ProfCoh.AdditiveFunction.toFun_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:19:44.803549+00:00
-- url     : https://prove2.me/submissions/2515719f-874f-4d10-bbe0-63160c5492b0

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveSnake
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_Additive
import Theorems.Thm_GroundTheory_ProfCoh_coe_torsNRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_modNRep_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.coe_torsNRep_apply
attribute [local simp] GroundTheory.ProfCoh.modNRep_mk



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
universe u v
open Representation
open GroundTheory.ProfCoh.AdditiveFunction
variable {l : ℕ} {Γ : Type v} [Group Γ] (d : AdditiveFunction.{u} l Γ)
namespace GroundTheory.ProfCoh.AdditiveFunction
theorem _root_.solution {X Y : Type u} [AddCommGroup X] [Module (ZMod l) X] [Finite X]
    [AddCommGroup Y] [Module (ZMod l) Y] [Finite Y] (ρ : Representation (ZMod l) Γ X)
    (σ : Representation (ZMod l) Γ Y) :
    d.toFun (X × Y) (ρ.prod σ) = d.toFun X ρ + d.toFun Y σ :=
  d.additive ρ _ σ (LinearMap.inl _ X Y) (LinearMap.snd _ X Y)
    ⟨fun _ _ => by ext <;> simp⟩ ⟨fun _ _ => rfl⟩ LinearMap.inl_injective
    Function.Exact.inl_snd LinearMap.snd_surjective
end GroundTheory.ProfCoh.AdditiveFunction
