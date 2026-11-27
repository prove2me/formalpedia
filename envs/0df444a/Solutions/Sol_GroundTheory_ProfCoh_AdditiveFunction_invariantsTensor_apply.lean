-- Prove2me | solution 1 for GroundTheory.ProfCoh.AdditiveFunction.invariantsTensor_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:49:52.711771+00:00
-- url     : https://prove2.me/submissions/8f863ac8-40e7-4f2a-9d55-f1ababbfc785

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveInvariants

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
universe u v w
open Representation TensorProduct
open GroundTheory.ProfCoh.AdditiveFunction
namespace GroundTheory.ProfCoh.AdditiveFunction
theorem _root_.solution (l : ℕ) [Fact l.Prime] (Γ : Type v) [Group Γ] [Finite Γ]
    (hΓ : Nat.Coprime (Nat.card Γ) l) {N : Type w} [AddCommGroup N] [Module (ZMod l) N]
    [Module.Finite (ZMod l) N] (σ : Representation (ZMod l) Γ N) (X : Type u) [AddCommGroup X]
    [Module (ZMod l) X] [Finite X] (ρ : Representation (ZMod l) Γ X) :
    (invariantsTensor.{u} l Γ hΓ σ).toFun X ρ = Module.finrank (ZMod l) (ρ.tprod σ).invariants :=
  rfl
end GroundTheory.ProfCoh.AdditiveFunction
