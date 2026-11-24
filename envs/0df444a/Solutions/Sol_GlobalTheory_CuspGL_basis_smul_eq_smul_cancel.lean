-- Prove2me | solution 1 for GlobalTheory.CuspGL.basis_smul_eq_smul_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:04:02.241046+00:00
-- url     : https://prove2.me/submissions/4d03f8ee-c7bd-4f4a-99dd-956a28c6127b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsMonomialBasisAbelianByPrimePowerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_TraceLiftMonomialMatrixEqSumEigenvaluesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterBrauerLiftAbelianByPrimePower

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
namespace GlobalTheory.CuspGL
theorem _root_.solution {k V ι : Type} [Field k] [AddCommGroup V] [Module k V]
    (b : Module.Basis ι k V) {x y : k} {i j : ι} (hx : x ≠ 0) (h : x • b i = y • b j) :
    i = j ∧ x = y := by
  classical
  have h1 := congrArg (fun v => b.repr v i) h
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
    smul_eq_mul, mul_one, Finsupp.single_apply] at h1
  by_cases hij : j = i
  · subst hij
    simpa using h1
  · simp [hij, hx] at h1
end GlobalTheory.CuspGL
