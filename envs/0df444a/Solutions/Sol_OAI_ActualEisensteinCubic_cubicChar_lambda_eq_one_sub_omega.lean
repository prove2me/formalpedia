-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.cubicChar_lambda_eq_one_sub_omega
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:22:37.741197+00:00
-- url     : https://prove2.me/submissions/d26e66f7-68aa-494b-a8b4-92baaf0671f5

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Theorems.Thm_OAI_ActualEisensteinCubic_A3_cubicChar_neg_one
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
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
open OAI.ActualEisensteinCubic
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    cubicChar P hgood (Ideal.Quotient.mk P lambda) =
      cubicChar P hgood (Ideal.Quotient.mk P (1 - omega)) := by
  have hl : lambda = (-1 : O) * (1 - omega) := by
    dsimp [lambda]
    ring
  calc
    cubicChar P hgood (Ideal.Quotient.mk P lambda) =
        cubicChar P hgood (Ideal.Quotient.mk P ((-1 : O) * (1 - omega))) := by rw [hl]
    _ = cubicChar P hgood (-1) *
        cubicChar P hgood (Ideal.Quotient.mk P (1 - omega)) := by rw [map_mul, map_mul, map_neg, map_one]
    _ = _ := by rw [A3_cubicChar_neg_one P hgood, one_mul]
end OAI.ActualEisensteinCubic
