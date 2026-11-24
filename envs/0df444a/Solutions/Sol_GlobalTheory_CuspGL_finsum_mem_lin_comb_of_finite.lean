-- Prove2me | solution 1 for GlobalTheory.CuspGL.finsum_mem_lin_comb_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:04:04.732072+00:00
-- url     : https://prove2.me/submissions/1670d562-c0ab-4b25-8080-a1f07e537d43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_AdditiveEqPolynomialVonMangoldtConvolutionOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ConjOfPrimaryFinrankKerPowEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyLinearEqui
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_AdditiveEqPolynomialVonMangoldtConvolutionOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ConjOfPrimaryFinrankKerPowEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyLinearEquiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassMobiusInverseMonicEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_PrimitiveEndClassFunctionEqZeroOfPrimaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsPrimitiveEndClassFunctionInvariantSubspaceMobiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_PrimitiveEndClassFunctionZeroOfCharpolyMassZero

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
theorem _root_.solution {α : Type} [Finite α] (S : Set α) (a b : ℂ) (u v : α → ℂ) :
    ∑ᶠ x ∈ S, (a * u x - b * v x) = a * (∑ᶠ x ∈ S, u x) - b * ∑ᶠ x ∈ S, v x := by
  have hS : S.Finite := Set.toFinite S
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, finsum_mem_eq_finite_toFinset_sum _ hS,
    finsum_mem_eq_finite_toFinset_sum _ hS, Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
end GlobalTheory.CuspGL
