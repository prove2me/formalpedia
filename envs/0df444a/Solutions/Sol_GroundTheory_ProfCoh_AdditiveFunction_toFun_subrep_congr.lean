-- Prove2me | solution 1 for GroundTheory.ProfCoh.AdditiveFunction.toFun_subrep_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:19:47.026369+00:00
-- url     : https://prove2.me/submissions/41a0c78a-9c48-4970-b5cd-1abdea40d088

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
theorem _root_.solution (ρ : Representation (ZMod l) Γ X) {p q : Submodule (ZMod l) X}
    (h : p = q) (hp : ∀ γ, p ≤ p.comap (ρ γ)) (hq : ∀ γ, q ≤ q.comap (ρ γ)) :
    d.toFun p (ρ.subrepresentation p hp) = d.toFun q (ρ.subrepresentation q hq) := by
  subst h
  rfl
end GroundTheory.ProfCoh.AdditiveFunction
