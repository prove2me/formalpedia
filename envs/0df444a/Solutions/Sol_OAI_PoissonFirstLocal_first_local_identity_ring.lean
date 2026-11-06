-- Prove2me | solution 1 for OAI.PoissonFirstLocal.first_local_identity_ring
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:17:06.072201+00:00
-- url     : https://prove2.me/submissions/f74c6e3c-ed24-4273-a10a-da8a5133b537

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_PoissonFirstLocal_exponent_table
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



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
open Finset Complex
open scoped Classical
open scoped Classical
open OAI.PoissonFirstLocal
open scoped Classical
namespace OAI.PoissonFirstLocal
theorem _root_.solution {R : Type*} [CommRing R]
    (side parityBit ε₁ ε₂ : Bool)
    (z : R) (χ : MulChar R ℂ) (hχ : χ ^ 6 = 1) :
    oldFactorRing side parityBit ε₁ ε₂ z χ =
      newFactorRing parityBit ε₁ ε₂ z χ := by
  let q := χ z
  by_cases hu : IsUnit z
  · have h6 : q ^ 6 = 1 := by
      dsimp [q]
      rw [← MulChar.pow_apply' χ (by decide : 6 ≠ 0), hχ]
      simp [MulChar.one_apply, hu]
    have hmask : quotientUnitMask z = 1 := by
      simp [quotientUnitMask, hu]
    change quotientUnitMask z * q ^ (4 * bit (if side then ε₂ else ε₁)) *
      q ^ (if side then cExp₂ parityBit ε₁ ε₂ else cExp₁ parityBit ε₁ ε₂) *
      q ^ EExp parityBit ε₁ ε₂ =
        (if retained parityBit ε₁ ε₂ then q ^ 4 else quotientUnitMask z)
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
  · have hz : q = 0 := MulChar.map_nonunit χ hu
    simp [oldFactorRing, newFactorRing, quotientUnitMask, hu]
end OAI.PoissonFirstLocal
