-- Prove2me | solution 1 for GlobalTheory.CuspGL.Primary.aeval_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:57:46.533033+00:00
-- url     : https://prove2.me/submissions/6610ed53-8e4b-4f11-ad23-df9a76858271

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyBlockAndInvariantUnderStabilizerNilradic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumMobiusInverseCharpolyInvariantLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyLinearEqui
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MobiusInversionAffineFinrankSubspacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSurjectivePiAdjoinRootKerEqRangeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AevalApplyMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvariantSubspaceMobiusInverseCharpolyPrimaryEq
import Theorems.Thm_GlobalTheory_PolynomialEvaluationMembership_aeval_apply_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL GlobalTheory.CuspGL.Primary
namespace GlobalTheory.CuspGL.Primary
theorem _root_.solution {F V : Type} [Field F] [AddCommGroup V] [Module F V] (g : Module.End F V)
    (W : Submodule F V) (hW : ∀ x ∈ W, g x ∈ W) (p : F[X]) : ∀ x ∈ W, aeval g p x ∈ W := by
  first
  | exact @_root_.GlobalTheory.PolynomialEvaluationMembership.aeval_apply_mem
  | exact _root_.GlobalTheory.PolynomialEvaluationMembership.aeval_apply_mem
  | (apply _root_.GlobalTheory.PolynomialEvaluationMembership.aeval_apply_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.PolynomialEvaluationMembership.aeval_apply_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PolynomialEvaluationMembership.aeval_apply_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PolynomialEvaluationMembership.aeval_apply_mem ..)
end GlobalTheory.CuspGL.Primary
