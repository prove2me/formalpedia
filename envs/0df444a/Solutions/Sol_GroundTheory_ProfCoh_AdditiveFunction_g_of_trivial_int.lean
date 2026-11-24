-- Prove2me | solution 1 for GroundTheory.ProfCoh.AdditiveFunction.g_of_trivial_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:49:37.036884+00:00
-- url     : https://prove2.me/submissions/afa0204d-8ada-43ec-8a24-97344b0af728

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveSnake
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_Additive
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_g_eq_of_torsion_trivial
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_toFun_congr
import Theorems.Thm_GroundTheory_ProfCoh_modNRep_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.modNRep_mk



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
universe u v
open Representation
open GroundTheory.ProfCoh.AdditiveFunction
variable {l : ℕ} {Γ : Type v} [Group Γ] (d : AdditiveFunction.{u} l Γ)
namespace GroundTheory.ProfCoh.AdditiveFunction
theorem _root_.solution [NeZero l] (A : Type u) [AddCommGroup A] [DistribMulAction Γ A]
    (htriv : ∀ (γ : Γ) (a : A), γ • a = a) (e : A ≃+ ℤ) : d.g A = d.one := by
  have hA : ∀ a : A, l • a = 0 → a = 0 := fun a ha => by
    have h := congrArg e ha
    rw [map_nsmul, map_zero, nsmul_eq_mul] at h
    have h' := (mul_eq_zero.1 h).resolve_left (by exact_mod_cast NeZero.ne l)
    exact e.injective (by rw [h', map_zero])
  let b : Module.Basis Unit ℤ A := (Module.Basis.singleton Unit ℤ).map e.symm.toIntLinearEquiv
  let E : ModN A l ≃ₗ[ZMod l] ULift.{u} (ZMod l) := (ModN.basis b).equivFun.trans
    ((LinearEquiv.funUnique Unit (ZMod l) (ZMod l)).trans ULift.moduleEquiv.symm)
  have : Finite (ModN A l) := Finite.of_equiv _ E.symm.toEquiv
  rw [d.g_eq_of_torsion_trivial A hA]
  refine d.toFun_congr _ _ E (fun γ x => ?_)
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [modNRep_mk, htriv]
  rfl
end GroundTheory.ProfCoh.AdditiveFunction
