-- Prove2me | solution 1 for GroundTheory.ProfCoh.AdditiveFunction.tensorRep_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:49:57.686488+00:00
-- url     : https://prove2.me/submissions/fcea2337-fc3f-4b4d-b24a-2633e3d37bd4

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
open GroundTheory.ProfCoh.AdditiveFunction
variable {l : ℕ} {Γ : Type v} [Group Γ]
namespace GroundTheory.ProfCoh.AdditiveFunction
theorem _root_.solution [Fact l.Prime] (d : AdditiveFunction.{u} l Γ) {N : Type u}
    [AddCommGroup N] [Module (ZMod l) N] [Finite N] (σ : Representation (ZMod l) Γ N)
    (W : Type u) [AddCommGroup W] [Module (ZMod l) W] [Finite W]
    (ρ : Representation (ZMod l) Γ W) [Finite (W ⊗[ZMod l] N)] :
    (d.tensorRep σ).toFun W ρ = d.toFun (W ⊗[ZMod l] N) (ρ.tprod σ) := by
  rfl
end GroundTheory.ProfCoh.AdditiveFunction
