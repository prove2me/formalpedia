-- Prove2me | solution 1 for GroundTheory.ProfCoh.AdditiveFunction.toFun_range_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:19:45.574859+00:00
-- url     : https://prove2.me/submissions/f1f12eab-4e61-46a3-90e4-6f0c42b7fdbe

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveSnake
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_toFun_eq_zero_of_subsingleton
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_toFun_eq_ker_add_range

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
theorem _root_.solution (ρ : Representation (ZMod l) Γ X)
    (σ : Representation (ZMod l) Γ Y) (φ : X →ₗ[ZMod l] Y) (hφ : ρ.IsIntertwiningMap σ φ)
    (hinj : Function.Injective φ) :
    d.toFun (LinearMap.range φ)
        (σ.subrepresentation _ (range_le_comap_of_isIntertwiningMap hφ)) = d.toFun X ρ := by
  have : Subsingleton (LinearMap.ker φ) :=
    ⟨fun a b => Subtype.ext (hinj (by rw [LinearMap.mem_ker.1 a.2, LinearMap.mem_ker.1 b.2]))⟩
  rw [d.toFun_eq_ker_add_range ρ σ φ hφ,
    d.toFun_eq_zero_of_subsingleton (X := LinearMap.ker φ), zero_add]
end GroundTheory.ProfCoh.AdditiveFunction
