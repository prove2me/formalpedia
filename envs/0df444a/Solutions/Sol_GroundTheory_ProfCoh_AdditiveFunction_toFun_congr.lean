-- Prove2me | solution 1 for GroundTheory.ProfCoh.AdditiveFunction.toFun_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:15:03.459515+00:00
-- url     : https://prove2.me/submissions/79ed1c41-fce8-478c-99a2-506f47a3c4f3

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveSnake
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_toFun_eq_zero_of_subsingleton
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
variable {X Y : Type u} [AddCommGroup X] [Module (ZMod l) X] [Finite X]
  [AddCommGroup Y] [Module (ZMod l) Y] [Finite Y]
namespace GroundTheory.ProfCoh.AdditiveFunction
theorem _root_.solution (ρ : Representation (ZMod l) Γ X) (σ : Representation (ZMod l) Γ Y)
    (e : X ≃ₗ[ZMod l] Y) (he : ∀ γ x, e (ρ γ x) = σ γ (e x)) :
    d.toFun X ρ = d.toFun Y σ := by
  have h := d.additive ρ σ (Representation.trivial (ZMod l) Γ PUnit.{u + 1}) e.toLinearMap 0
    ⟨he⟩ ⟨fun _ _ => Subsingleton.elim _ _⟩ e.injective
    (fun y => ⟨fun _ => ⟨e.symm y, by simp⟩, fun _ => Subsingleton.elim _ _⟩)
    (fun _ => ⟨0, Subsingleton.elim _ _⟩)
  rw [h, d.toFun_eq_zero_of_subsingleton (X := PUnit.{u + 1}), add_zero]
end GroundTheory.ProfCoh.AdditiveFunction
