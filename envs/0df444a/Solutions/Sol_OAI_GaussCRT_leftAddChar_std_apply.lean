-- Prove2me | solution 1 for OAI.GaussCRT.leftAddChar_std_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:36:21.663188+00:00
-- url     : https://prove2.me/submissions/f144fa2d-df8c-44e7-86b3-caa4cc1d17ae

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ChineseRemainder
import Theorems.Thm_OAI_GaussCRT_crt_left_axis

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
    (hr : ((n * r : ℕ) : ZMod m) = 1) (z : ZMod m) :
    leftAddChar m n h (ZMod.stdAddChar (N := m * n)) z =
      (ZMod.stdAddChar (N := m)) ((r : ZMod m) * z) := by
  have hleft :
      leftAddChar m n h (ZMod.stdAddChar (N := m * n)) z =
      ZMod.stdAddChar ((n * r * z.val : ℕ) : ZMod (m * n)) := by
    change ZMod.stdAddChar ((ZMod.chineseRemainder h).symm (z, 0)) = _
    rw [crt_left_axis m n r h hr z]
  have hz : ((r : ZMod m) * z) = ((r * z.val : ℕ) : ZMod m) := by
    rw [← ZMod.natCast_zmod_val z]
    simp [Nat.cast_mul]
  rw [hleft, hz]
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have h1 := ZMod.stdAddChar_coe (N := m * n) (j := (n * r * z.val : ℤ))
  have h2 := ZMod.stdAddChar_coe (N := m) (j := (r * z.val : ℤ))
  norm_cast at h1 h2 ⊢
  rw [h1, h2]
  congr 1
  field_simp
  simp only [Nat.cast_mul]
  ring
end OAI.GaussCRT
