-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.cubicChar_traceLambda_relation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:24:24.677204+00:00
-- url     : https://prove2.me/submissions/2d35f606-857b-4f88-8915-5408cb4d547a

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicChar_omega
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
    cubicChar P hgood (Ideal.Quotient.mk P traceLambda) =
      omega ^ ((Nat.card (O ⧸ P) - 1) / 3) *
        cubicChar P hgood (Ideal.Quotient.mk P (1 - omega)) := by
  have ht : traceLambda = omega * (1 - omega) := by
    rw [traceLambda_eq_unit_mul_lambda]
    dsimp [lambda]
    ring
  calc
    cubicChar P hgood (Ideal.Quotient.mk P traceLambda) =
        cubicChar P hgood (Ideal.Quotient.mk P (omega * (1 - omega))) := by rw [ht]
    _ = cubicChar P hgood (Ideal.Quotient.mk P omega) *
        cubicChar P hgood (Ideal.Quotient.mk P (1 - omega)) := by rw [map_mul, map_mul]
    _ = _ := by rw [cubicChar_omega P hgood]
end OAI.ActualEisensteinCubic
