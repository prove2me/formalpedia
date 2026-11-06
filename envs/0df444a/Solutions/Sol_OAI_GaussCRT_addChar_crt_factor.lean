-- Prove2me | solution 1 for OAI.GaussCRT.addChar_crt_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:51:31.084969+00:00
-- url     : https://prove2.me/submissions/c63cfa5f-1957-4e25-b43d-c7415bbe3517

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ChineseRemainder

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section
open Finset Complex
open scoped Classical
open OAI.GaussCRT
namespace OAI.GaussCRT
theorem _root_.solution (m n : ℕ) (h : m.Coprime n)
    (ψ : AddChar (ZMod (m * n)) ℂ) (x : ZMod (m * n)) :
    ψ x =
      leftAddChar m n h ψ ((ZMod.chineseRemainder h x).1) *
      rightAddChar m n h ψ ((ZMod.chineseRemainder h x).2) := by
  let z := ZMod.chineseRemainder h x
  have hz : (z.1, (0 : ZMod n)) + ((0 : ZMod m), z.2) = z := by
    ext <;> simp
  calc
    ψ x = ψ ((ZMod.chineseRemainder h).symm z) := by simp [z]
    _ = ψ ((ZMod.chineseRemainder h).symm (z.1, 0) +
          (ZMod.chineseRemainder h).symm (0, z.2)) := by
          rw [← map_add, hz]
    _ = _ := by rw [AddChar.map_add_eq_mul]; rfl
end OAI.GaussCRT
