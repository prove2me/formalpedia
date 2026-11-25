-- Prove2me | solution 1 for GroundTheory.ProfCoh.AdditiveFunction.toFun_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:30:46.135848+00:00
-- url     : https://prove2.me/submissions/94e3fa70-1716-4a68-a8e4-400c78e4bfd3

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveSnake
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_Additive
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_toFun_prod
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_toFun_congr
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
namespace GroundTheory.ProfCoh.AdditiveFunction
theorem _root_.solution {X : Type u} [AddCommGroup X] [Module (ZMod l) X] [Finite X]
    (ρ : Representation (ZMod l) Γ X) (n : ℕ) :
    d.toFun (Fin n → X) (piRep (Fin n) ρ) = n * d.toFun X ρ := by
  induction n with
  | zero => simp [d.toFun_eq_zero_of_subsingleton (X := Fin 0 → X)]
  | succ n ih =>
    rw [← d.toFun_congr (ρ.prod (piRep (Fin n) ρ)) (piRep (Fin (n + 1)) ρ)
      (Fin.consLinearEquiv (ZMod l) (fun _ => X)) ?_, d.toFun_prod, ih]
    · push_cast
      ring
    · intro γ x
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
end GroundTheory.ProfCoh.AdditiveFunction
