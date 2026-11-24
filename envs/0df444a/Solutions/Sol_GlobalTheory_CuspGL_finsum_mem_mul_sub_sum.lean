-- Prove2me | solution 1 for GlobalTheory.CuspGL.finsum_mem_mul_sub_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:04:05.833685+00:00
-- url     : https://prove2.me/submissions/7c52c7f3-a99d-4dc0-a1aa-0507fa95588a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InnerProductRootPowerSumEqOfFrobeniusModEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvertibleEndInnerProductRootPowerSumMobiusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvertibleEndInnerProductRootPowerSumEqTorusSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_PrimitiveEndClassFunctionZeroOfCharpolyMassZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyLinearEqui
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsPrimitiveEndClassFunctionInvariantSubspaceMobiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootPowerSumCharacterAdditiveAndXSubOnePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfFinsumMulStarPowEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_PrimitiveClassFunctionExpansionRootSums

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
theorem _root_.solution {G : Type} [Finite G] (S : Set G) (c : ℂ) (φ : G → ℂ) (T : Finset ℕ)
    (a : ℕ → ℂ) (ψ : ℕ → G → ℂ) :
    ∑ᶠ g ∈ S, (c * φ g - ∑ k ∈ T, a k * ψ k g) = c * (∑ᶠ g ∈ S, φ g) - ∑ k ∈ T, a k * ∑ᶠ g ∈ S, ψ k g := by
  have hS : S.Finite := Set.toFinite S
  simp only [finsum_mem_eq_finite_toFinset_sum _ hS]
  rw [Finset.sum_sub_distrib, Finset.sum_comm]
  simp only [Finset.mul_sum]
end GlobalTheory.CuspGL
