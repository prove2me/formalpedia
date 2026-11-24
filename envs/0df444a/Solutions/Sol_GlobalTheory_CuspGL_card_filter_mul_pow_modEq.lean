-- Prove2me | solution 1 for GlobalTheory.CuspGL.card_filter_mul_pow_modEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:04:04.328424+00:00
-- url     : https://prove2.me/submissions/4d4459f7-deb7-4d14-9d15-943c4cc926f5

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
theorem _root_.solution (q n i l : ℕ) (hq : 1 < q) (hn : 0 < n) (hi : i ≤ n) :
    ((Finset.range (q ^ n - 1)).filter (fun k => k * q ^ i ≡ l [MOD (q ^ n - 1)])).card = 1 := by
  set N := q ^ n - 1 with hN
  have hq1 : 1 ≤ q ^ n := Nat.one_le_pow _ _ (by omega)
  have hqn : q ≤ q ^ n := Nat.le_self_pow (by omega) q
  have hNpos : 0 < N := by omega
  have hcop : Nat.Coprime (q ^ i) N := by
    have h1 : Nat.Coprime (q ^ n) N := by
      rw [hN, Nat.coprime_self_sub_right hq1]
      exact Nat.coprime_one_right _
    exact (h1.coprime_dvd_left (dvd_pow_self q (by omega))).pow_left i
  have uniq : ∀ a b, a ∈ Finset.range N → b ∈ Finset.range N →
      a * q ^ i % N = b * q ^ i % N → a = b := by
    intro a b ha hb hab
    have hmod : a ≡ b [MOD N] := Nat.ModEq.cancel_right_of_coprime (Nat.Coprime.gcd_eq_one hcop.symm) hab
    have ha' := Nat.mod_eq_of_lt (Finset.mem_range.mp ha)
    have hb' := Nat.mod_eq_of_lt (Finset.mem_range.mp hb)
    unfold Nat.ModEq at hmod
    omega
  obtain ⟨k, hk, hkeq⟩ := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range N) (t := Finset.range N)
    (fun k _ => k * q ^ i % N) (fun k _ => Finset.mem_range.mpr (Nat.mod_lt _ hNpos))
    (fun a b ha hb hab => uniq a b ha hb hab) le_rfl (l % N) (Finset.mem_range.mpr (Nat.mod_lt _ hNpos))
  rw [Finset.card_eq_one]
  refine ⟨k, ?_⟩
  ext k'
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hk', h'⟩
    have h'' : k' * q ^ i % N = l % N := h'
    exact uniq k' k hk' hk (h''.trans hkeq)
  · rintro rfl
    exact ⟨hk, hkeq.symm⟩
end GlobalTheory.CuspGL
