-- Prove2me | solution 1 for GroundTheory.ProfCoh.AdditiveFunction.toFun_eq_ker_add_range
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:58.98881+00:00
-- url     : https://prove2.me/submissions/b8265894-3fe3-4ea7-aa62-6d2fa0836a11

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
theorem _root_.solution (ρ : Representation (ZMod l) Γ X)
    (σ : Representation (ZMod l) Γ Y) (φ : X →ₗ[ZMod l] Y) (hφ : ρ.IsIntertwiningMap σ φ) :
    d.toFun X ρ = d.toFun (LinearMap.ker φ)
        (ρ.subrepresentation _ (ker_le_comap_of_isIntertwiningMap hφ)) +
      d.toFun (LinearMap.range φ)
        (σ.subrepresentation _ (range_le_comap_of_isIntertwiningMap hφ)) :=
  d.additive _ ρ _ (LinearMap.ker φ).subtype φ.rangeRestrict ⟨fun _ _ => rfl⟩
    ⟨fun γ x => Subtype.ext (hφ.isIntertwining γ x)⟩ (Submodule.injective_subtype _)
    (fun y => by
      rw [← LinearMap.exact_subtype_ker_map φ y, Subtype.ext_iff]
      rfl)
    (LinearMap.surjective_rangeRestrict φ)
end GroundTheory.ProfCoh.AdditiveFunction
