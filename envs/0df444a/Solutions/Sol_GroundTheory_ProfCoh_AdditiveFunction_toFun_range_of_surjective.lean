-- Prove2me | solution 1 for GroundTheory.ProfCoh.AdditiveFunction.toFun_range_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:19:46.249391+00:00
-- url     : https://prove2.me/submissions/8ab25187-8b85-4a96-ac77-1eaf4218cf16

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveSnake
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_toFun_congr

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
omit [Finite X]
namespace GroundTheory.ProfCoh.AdditiveFunction
theorem _root_.solution (ρ : Representation (ZMod l) Γ X)
    (σ : Representation (ZMod l) Γ Y) (φ : X →ₗ[ZMod l] Y) (hφ : ρ.IsIntertwiningMap σ φ)
    (hs : Function.Surjective φ) :
    d.toFun (LinearMap.range φ)
        (σ.subrepresentation _ (range_le_comap_of_isIntertwiningMap hφ)) = d.toFun Y σ :=
  d.toFun_congr _ _ (LinearEquiv.ofTop _ (LinearMap.range_eq_top.2 hs)) (fun _ _ => rfl)
end GroundTheory.ProfCoh.AdditiveFunction
