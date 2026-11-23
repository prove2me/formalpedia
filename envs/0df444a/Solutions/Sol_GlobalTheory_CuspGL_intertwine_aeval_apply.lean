-- Prove2me | solution 1 for GlobalTheory.CuspGL.intertwine_aeval_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:15.320851+00:00
-- url     : https://prove2.me/submissions/0e18ebc8-2dc6-445b-9551-ee44fbb86818

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsConjEqAddOfIsCoprime

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
namespace GlobalTheory.CuspGL
theorem _root_.solution {F : Type} [Field F] {V W : Type} [AddCommGroup V] [Module F V] [AddCommGroup W]
    [Module F W] (f : V →ₗ[F] W) (a : Module.End F V) (b : Module.End F W) (h : ∀ x, f (a x) = b (f x))
    (p : F[X]) (x : V) : f (aeval a p x) = aeval b p (f x) := by
  have hpow : ∀ (n : ℕ) (x : V), f ((a ^ n) x) = (b ^ n) (f x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih => intro x; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n c => simp [aeval_monomial, hpow]
end GlobalTheory.CuspGL
