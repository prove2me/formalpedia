-- Prove2me | solution 1 for OAI.GaussCRT.gauss_sum_crt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:36:03.920111+00:00
-- url     : https://prove2.me/submissions/b691598b-59fd-4122-8413-403214aa555b

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ChineseRemainder
import Theorems.Thm_OAI_GaussCRT_gauss_sum_chinese_product
import Theorems.Thm_OAI_GaussCRT_addChar_crt_factor

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
    (ψ : AddChar (ZMod (m * n)) ℂ) :
    (∑ x : ZMod (m * n),
      χm ((ZMod.chineseRemainder h x).1) *
      χn ((ZMod.chineseRemainder h x).2) * ψ x) =
      gaussSum χm (leftAddChar m n h ψ) *
      gaussSum χn (rightAddChar m n h ψ) := by
  simp_rw [addChar_crt_factor m n h ψ]
  convert gauss_sum_chinese_product m n h χm χn
    (leftAddChar m n h ψ) (rightAddChar m n h ψ) using 1 ;
      congr 1 ; ext x ; ring
end OAI.GaussCRT
