-- Prove2me | solution 1 for GlobalTheory.CuspGL.coe_aeval_restrict_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:04:07.08247+00:00
-- url     : https://prove2.me/submissions/6b3606d4-3b21-48f9-b298-7034ca4fa648

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyOfIrreduci

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
theorem _root_.solution {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    (g : Module.End F V) (W : Submodule F V) (hW : ∀ x ∈ W, g x ∈ W) (p : F[X]) (x : W) :
    ((aeval (g.restrict hW : Module.End F W) p x : W) : V) = aeval g p x := by
  induction p using Polynomial.induction_on generalizing x with
  | C a => simp [Module.algebraMap_end_apply]
  | add p q hp hq => simp [hp, hq]
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc, map_mul, map_mul (aeval g), aeval_X, aeval_X,
      Module.End.mul_apply, Module.End.mul_apply, ih]
    rfl
end GlobalTheory.CuspGL
