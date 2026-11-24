-- Prove2me | solution 1 for GlobalTheory.CuspGL.sum_mul_card_filter_modEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:22:06.045465+00:00
-- url     : https://prove2.me/submissions/bc358bcc-54e8-4945-9c62-c4c222353c5e

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
import Theorems.Thm_GlobalTheory_CuspGL_card_filter_mul_pow_modEq

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
theorem _root_.solution (q n l : ℕ) (hq : 1 < q) (hn : 0 < n) (A : ℕ → ℂ)
    (hA : ∀ k i : ℕ, k * q ^ i ≡ l [MOD (q ^ n - 1)] → A k = A l) :
    ∑ k ∈ Finset.range (q ^ n - 1),
      A k * (((Finset.range n).filter (fun i => k * q ^ i ≡ l [MOD (q ^ n - 1)])).card : ℂ) = n * A l := by
  have key : ∀ i ∈ Finset.range n, ∑ k ∈ Finset.range (q ^ n - 1),
      (if k * q ^ i ≡ l [MOD (q ^ n - 1)] then A k else 0) = A l := by
    intro i hi
    rw [← Finset.sum_filter]
    obtain ⟨k, hk⟩ := Finset.card_eq_one.mp
      (card_filter_mul_pow_modEq q n i l hq hn (Finset.mem_range.mp hi).le)
    have hmem : k ∈ (Finset.range (q ^ n - 1)).filter (fun k => k * q ^ i ≡ l [MOD (q ^ n - 1)]) := by
      rw [hk]; exact Finset.mem_singleton_self k
    rw [hk, Finset.sum_singleton]
    exact hA k i (Finset.mem_filter.mp hmem).2
  calc ∑ k ∈ Finset.range (q ^ n - 1),
        A k * (((Finset.range n).filter (fun i => k * q ^ i ≡ l [MOD (q ^ n - 1)])).card : ℂ)
      = ∑ k ∈ Finset.range (q ^ n - 1), ∑ i ∈ Finset.range n,
          (if k * q ^ i ≡ l [MOD (q ^ n - 1)] then A k else 0) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> simp
    _ = ∑ i ∈ Finset.range n, ∑ k ∈ Finset.range (q ^ n - 1),
          (if k * q ^ i ≡ l [MOD (q ^ n - 1)] then A k else 0) := Finset.sum_comm
    _ = ∑ i ∈ Finset.range n, A l := Finset.sum_congr rfl key
    _ = n * A l := by simp
end GlobalTheory.CuspGL
