-- Prove2me | solution 1 for OAI.GaussCRT.gauss_sum_crt_standard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:08:07.139418+00:00
-- url     : https://prove2.me/submissions/fcb9968f-808c-4368-bfc8-9a53e22de981

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ChineseRemainder
import Theorems.Thm_OAI_GaussCRT_gauss_sum_crt
import Theorems.Thm_OAI_GaussCRT_leftAddChar_std_apply
import Theorems.Thm_OAI_GaussCRT_rightAddChar_std_apply
import Theorems.Thm_OAI_GaussCRT_gauss_shift_cross

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
theorem _root_.solution (m n r s : ℕ)
    [NeZero m] [NeZero n] [NeZero (m * n)]
    (h : m.Coprime n)
    (hr : ((n * r : ℕ) : ZMod m) = 1)
    (hs : ((m * s : ℕ) : ZMod n) = 1)
    (χm : MulChar (ZMod m) ℂ) (χn : MulChar (ZMod n) ℂ) :
    (∑ x : ZMod (m * n),
      χm ((ZMod.chineseRemainder h x).1) *
      χn ((ZMod.chineseRemainder h x).2) *
      (ZMod.stdAddChar (N := m * n)) x) =
      χm (n : ZMod m) * χn (m : ZMod n) *
        gaussSum χm (ZMod.stdAddChar (N := m)) *
        gaussSum χn (ZMod.stdAddChar (N := n)) := by
  have hleft : leftAddChar m n h (ZMod.stdAddChar (N := m * n)) =
      (ZMod.stdAddChar (N := m)).mulShift (r : ZMod m) := by
    ext z
    exact leftAddChar_std_apply m n r h hr z
  have hright : rightAddChar m n h (ZMod.stdAddChar (N := m * n)) =
      (ZMod.stdAddChar (N := n)).mulShift (s : ZMod n) := by
    ext z
    exact rightAddChar_std_apply m n s h hs z
  rw [gauss_sum_crt m n h χm χn (ZMod.stdAddChar (N := m * n)),
      hleft, hright,
      gauss_shift_cross m n r χm hr,
      gauss_shift_cross n m s χn hs]
  ring
end OAI.GaussCRT
