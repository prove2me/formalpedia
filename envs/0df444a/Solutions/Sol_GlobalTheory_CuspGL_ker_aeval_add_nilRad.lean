-- Prove2me | solution 1 for GlobalTheory.CuspGL.ker_aeval_add_nilRad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:44:31.93562+00:00
-- url     : https://prove2.me/submissions/91078a76-a02e-4642-ac92-258e9d7975ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_KerAevalAddStabilizerNilradicalSocle
import Theorems.Thm_GlobalTheory_CuspGL_aeval_add_nilRad

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL
variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
namespace GlobalTheory.CuspGL
theorem _root_.solution :
    ∀ (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g h : Module.End F V) (f : F[X]), h ∈ nilRad (LinearMap.ker (aeval g f)) → LinearMap.ker (aeval g f) ≤ LinearMap.ker (aeval (g + h) f) ∧ (LinearMap.ker (aeval (g + h) f) = LinearMap.ker (aeval g f) → ∀ j : ℕ, Module.finrank F (LinearMap.ker (aeval g (f ^ j))) = Module.finrank F (LinearMap.ker (aeval (g + h) (f ^ j)))) := by
  intro F _ V _ _ _ g h f hh
  have hg : ∀ x ∈ LinearMap.ker (aeval g f), g x ∈ LinearMap.ker (aeval g f) := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    have : aeval g f * g = g * aeval g f := by
      have h1 : aeval g (f * X) = aeval g (X * f) := by rw [mul_comm]
      simpa using h1
    rw [← Module.End.mul_apply, this, Module.End.mul_apply, hx, map_zero]
  refine ⟨fun x hx => ?_, fun he j => ?_⟩
  · rw [LinearMap.mem_ker, (aeval_add_nilRad hg hh f).1 x hx]
    exact hx
  · have : LinearMap.ker (aeval g (f ^ j)) = LinearMap.ker (aeval (g + h) (f ^ j)) := by
      cases j with
      | zero =>
        ext x
        simp
      | succ j =>
        ext x
        have H := (aeval_add_nilRad hg hh (f ^ j)).2 x
        have e1 : x ∈ LinearMap.ker (aeval g (f ^ (j + 1))) ↔
            aeval g (f ^ j) x ∈ LinearMap.ker (aeval g f) := by
          rw [pow_succ', map_mul, LinearMap.mem_ker, LinearMap.mem_ker, Module.End.mul_apply]
        have e2 : x ∈ LinearMap.ker (aeval (g + h) (f ^ (j + 1))) ↔
            aeval (g + h) (f ^ j) x ∈ LinearMap.ker (aeval (g + h) f) := by
          rw [pow_succ', map_mul, LinearMap.mem_ker, LinearMap.mem_ker, Module.End.mul_apply]
        rw [e1, e2, he]
        constructor
        · intro a
          have := Submodule.add_mem _ H a
          rwa [sub_add_cancel] at this
        · intro a
          have := Submodule.sub_mem _ a H
          rwa [sub_sub_cancel] at this
    rw [this]
end GlobalTheory.CuspGL
