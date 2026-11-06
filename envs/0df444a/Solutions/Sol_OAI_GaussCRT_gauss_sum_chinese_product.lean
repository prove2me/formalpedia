-- Prove2me | solution 1 for OAI.GaussCRT.gauss_sum_chinese_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:35:14.602001+00:00
-- url     : https://prove2.me/submissions/376e9700-e5f8-4926-84e7-3bd8f580a773

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
theorem _root_.solution (m n : ℕ)
    [NeZero m] [NeZero n] [NeZero (m * n)] (h : m.Coprime n)
    (χm : MulChar (ZMod m) ℂ) (χn : MulChar (ZMod n) ℂ)
    (ψm : AddChar (ZMod m) ℂ) (ψn : AddChar (ZMod n) ℂ) :
    (∑ x : ZMod (m * n),
      χm ((ZMod.chineseRemainder h x).1) *
      χn ((ZMod.chineseRemainder h x).2) *
      ψm ((ZMod.chineseRemainder h x).1) *
      ψn ((ZMod.chineseRemainder h x).2)) =
      gaussSum χm ψm * gaussSum χn ψn := by
  let e := (ZMod.chineseRemainder h).toEquiv
  let F : ZMod m × ZMod n → ℂ :=
    fun z => χm z.1 * χn z.2 * ψm z.1 * ψn z.2
  calc
    (∑ x : ZMod (m * n),
      χm ((ZMod.chineseRemainder h x).1) *
      χn ((ZMod.chineseRemainder h x).2) *
      ψm ((ZMod.chineseRemainder h x).1) *
      ψn ((ZMod.chineseRemainder h x).2)) =
        ∑ x : ZMod (m * n), F (e x) := rfl
    _ = ∑ z : ZMod m × ZMod n, F z := Equiv.sum_comp e F
    _ = ∑ z : ZMod m, ∑ w : ZMod n, F (z, w) := Fintype.sum_prod_type F
    _ = gaussSum χm ψm * gaussSum χn ψn := by
      simp only [F, gaussSum]
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro w hw
      ring
end OAI.GaussCRT
