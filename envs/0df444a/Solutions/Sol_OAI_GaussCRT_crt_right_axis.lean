-- Prove2me | solution 1 for OAI.GaussCRT.crt_right_axis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:35:36.552283+00:00
-- url     : https://prove2.me/submissions/1abbdf79-38aa-4ddb-99dc-3e8b9aa70eb9

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
theorem _root_.solution (m n r : ℕ) (h : m.Coprime n)
    [NeZero m] [NeZero n]
    (hr : ((m * r : ℕ) : ZMod n) = 1) (z : ZMod n) :
    (ZMod.chineseRemainder h).symm (0, z) =
      ((m * r * z.val : ℕ) : ZMod (m * n)) := by
  apply (ZMod.chineseRemainder h).injective
  rw [(ZMod.chineseRemainder h).apply_symm_apply]
  have hfst (x : ZMod (m * n)) : ((ZMod.chineseRemainder h) x).1 =
      (x.cast : ZMod m) := by
        simp [ZMod.chineseRemainder, ZMod.castHom_apply, Prod.fst_zmod_cast]
  have hsnd (x : ZMod (m * n)) : ((ZMod.chineseRemainder h) x).2 =
      (x.cast : ZMod n) := by
        simp [ZMod.chineseRemainder, ZMod.castHom_apply, Prod.snd_zmod_cast]
  apply Prod.ext
  · rw [hfst, ZMod.cast_natCast (by simp : m ∣ m * n) (m * r * z.val)]
    simp [Nat.cast_mul]
  · rw [hsnd, ZMod.cast_natCast (by simp : n ∣ m * n) (m * r * z.val)]
    simp only [Nat.cast_mul]
    rw [← Nat.cast_mul (α := ZMod n) m r, hr, one_mul,
      ZMod.natCast_zmod_val]
end OAI.GaussCRT
