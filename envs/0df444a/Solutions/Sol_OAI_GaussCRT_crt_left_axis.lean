-- Prove2me | solution 1 for OAI.GaussCRT.crt_left_axis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:35:21.896917+00:00
-- url     : https://prove2.me/submissions/f7700a54-37a1-48c6-87f2-b9285736aa16

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
    (hr : ((n * r : ℕ) : ZMod m) = 1) (z : ZMod m) :
    (ZMod.chineseRemainder h).symm (z, 0) =
      ((n * r * z.val : ℕ) : ZMod (m * n)) := by
  apply (ZMod.chineseRemainder h).injective
  rw [(ZMod.chineseRemainder h).apply_symm_apply]
  have hfst (x : ZMod (m * n)) : ((ZMod.chineseRemainder h) x).1 =
      (x.cast : ZMod m) := by
        simp [ZMod.chineseRemainder, ZMod.castHom_apply, Prod.fst_zmod_cast]
  have hsnd (x : ZMod (m * n)) : ((ZMod.chineseRemainder h) x).2 =
      (x.cast : ZMod n) := by
        simp [ZMod.chineseRemainder, ZMod.castHom_apply, Prod.snd_zmod_cast]
  apply Prod.ext
  · rw [hfst, ZMod.cast_natCast (by simp : m ∣ m * n) (n * r * z.val)]
    simp only [ Nat.cast_mul]
    rw [← Nat.cast_mul (α := ZMod m) n r, hr, one_mul,
      ZMod.natCast_zmod_val]
  · rw [hsnd, ZMod.cast_natCast (by simp : n ∣ m * n) (n * r * z.val)]
    simp [Nat.cast_mul]
end OAI.GaussCRT
