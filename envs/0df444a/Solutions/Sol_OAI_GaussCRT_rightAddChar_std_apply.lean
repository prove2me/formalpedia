-- Prove2me | solution 1 for OAI.GaussCRT.rightAddChar_std_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:36:19.888571+00:00
-- url     : https://prove2.me/submissions/04b1701d-2da0-4f86-b7f0-5f3ceaef2ac0

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ChineseRemainder
import Theorems.Thm_OAI_GaussCRT_crt_right_axis

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
theorem _root_.solution (m n r : ℕ) (h : m.Coprime n)
    [NeZero m] [NeZero n] [NeZero (m * n)]
    (hr : ((m * r : ℕ) : ZMod n) = 1) (z : ZMod n) :
    rightAddChar m n h (ZMod.stdAddChar (N := m * n)) z =
      (ZMod.stdAddChar (N := n)) ((r : ZMod n) * z) := by
  have hright :
      rightAddChar m n h (ZMod.stdAddChar (N := m * n)) z =
      ZMod.stdAddChar ((m * r * z.val : ℕ) : ZMod (m * n)) := by
    change ZMod.stdAddChar ((ZMod.chineseRemainder h).symm (0, z)) = _
    rw [crt_right_axis m n r h hr z]
  have hz : ((r : ZMod n) * z) = ((r * z.val : ℕ) : ZMod n) := by
    rw [← ZMod.natCast_zmod_val z]
    simp [Nat.cast_mul]
  rw [hright, hz]
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have h1 := ZMod.stdAddChar_coe (N := m * n) (j := (m * r * z.val : ℤ))
  have h2 := ZMod.stdAddChar_coe (N := n) (j := (r * z.val : ℤ))
  norm_cast at h1 h2 ⊢
  rw [h1, h2]
  congr 1
  field_simp
  simp only [Nat.cast_mul]
  ring
end OAI.GaussCRT
