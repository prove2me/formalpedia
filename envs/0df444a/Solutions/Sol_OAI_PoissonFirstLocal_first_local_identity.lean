-- Prove2me | solution 1 for OAI.PoissonFirstLocal.first_local_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:35:42.18047+00:00
-- url     : https://prove2.me/submissions/8dbe3997-aa76-46a8-8f1f-264334e83ab8

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Theorems.Thm_OAI_PoissonFirstLocal_exponent_table

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open OAI.PoissonFirstLocal
open scoped Classical
namespace OAI.PoissonFirstLocal
theorem _root_.solution (side parityBit ε₁ ε₂ : Bool)
    (n p : ℕ) (χ : MulChar (ZMod n) ℂ) (hχ : χ ^ 6 = 1) :
    oldFactor side parityBit ε₁ ε₂ n p χ = newFactor parityBit ε₁ ε₂ n p χ := by
  let q := χ (p : ZMod n)
  by_cases hcop : n.Coprime p
  · have hunit : IsUnit (p : ZMod n) :=
      (ZMod.isUnit_iff_coprime p n).mpr hcop.symm
    have h6 : q ^ 6 = 1 := by
      dsimp [q]
      rw [← MulChar.pow_apply' χ (by decide : 6 ≠ 0), hχ]
      simp [MulChar.one_apply, hunit]
    have hmask : mask n p = 1 := by simp [mask, hcop]
    change mask n p * q ^ (4 * bit (if side then ε₂ else ε₁)) *
      q ^ (if side then cExp₂ parityBit ε₁ ε₂ else cExp₁ parityBit ε₁ ε₂) *
      q ^ EExp parityBit ε₁ ε₂ =
      (if retained parityBit ε₁ ε₂ then q ^ 4 else mask n p)
    rw [hmask, one_mul, ← pow_add, ← pow_add]
    cases side
    · change q ^ (totalExp₁ parityBit ε₁ ε₂) =
          (if retained parityBit ε₁ ε₂ then q ^ 4 else 1)
      rw [pow_eq_pow_mod _ h6, (exponent_table parityBit ε₁ ε₂).1]
      split_ifs <;> simp
    · change q ^ (totalExp₂ parityBit ε₁ ε₂) =
          (if retained parityBit ε₁ ε₂ then q ^ 4 else 1)
      rw [pow_eq_pow_mod _ h6, (exponent_table parityBit ε₁ ε₂).2]
      split_ifs <;> simp
  · have hnu : ¬ IsUnit (p : ZMod n) := by
      intro hu
      exact hcop ((ZMod.isUnit_iff_coprime p n).mp hu).symm
    have hzero : q = 0 := MulChar.map_nonunit χ hnu
    simp [oldFactor, newFactor, mask, hcop, q, hzero]
end OAI.PoissonFirstLocal
