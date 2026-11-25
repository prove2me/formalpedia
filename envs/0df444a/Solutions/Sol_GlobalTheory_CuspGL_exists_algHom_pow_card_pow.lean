-- Prove2me | solution 1 for GlobalTheory.CuspGL.exists_algHom_pow_card_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:12:26.53341+00:00
-- url     : https://prove2.me/submissions/61e91c33-ecda-42fd-9831-12681c93f020

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FrobeniusTorusMinpolyDegreeRootPowerSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL
variable {F : Type} [Field F] [Finite F]
namespace GlobalTheory.CuspGL
theorem _root_.solution (i : ℕ) :
    ∃ f : AlgebraicClosure F →ₐ[F] AlgebraicClosure F, ∀ x, f x = x ^ Nat.card F ^ i := by
  letI := Fintype.ofFinite F
  refine ⟨FiniteField.frobeniusAlgHom F (AlgebraicClosure F) ^ i, fun x => ?_⟩
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', AlgHom.mul_apply, ih, FiniteField.coe_frobeniusAlgHom, pow_succ, pow_mul,
      Nat.card_eq_fintype_card]
end GlobalTheory.CuspGL
