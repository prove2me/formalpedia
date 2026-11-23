-- Prove2me | solution 1 for GroundTheory.ProfCoh.AdditiveFunction.toFun_eq_zero_of_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:10:09.363946+00:00
-- url     : https://prove2.me/submissions/8ff4fe13-2374-41dd-82c7-66c735221c7e

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
open GroundTheory.ProfCoh.AdditiveFunction
variable {l : ℕ} {Γ : Type v} [Group Γ] (d : AdditiveFunction.{u} l Γ)
variable {X Y : Type u} [AddCommGroup X] [Module (ZMod l) X] [Finite X]
  [AddCommGroup Y] [Module (ZMod l) Y] [Finite Y]
namespace GroundTheory.ProfCoh.AdditiveFunction
theorem _root_.solution [Subsingleton X] (ρ : Representation (ZMod l) Γ X) :
    d.toFun X ρ = 0 := by
  have h := d.additive ρ ρ ρ 0 0 ⟨fun _ _ => Subsingleton.elim _ _⟩
    ⟨fun _ _ => Subsingleton.elim _ _⟩ (fun _ _ _ => Subsingleton.elim _ _)
    (fun _ => ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩)
    (fun _ => ⟨0, Subsingleton.elim _ _⟩)
  omega
end GroundTheory.ProfCoh.AdditiveFunction
