-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.canonical_two_prime_gauss_transform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:22:38.789182+00:00
-- url     : https://prove2.me/submissions/68b6a09b-388a-4548-95d4-b2d3bc4c87c5

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Theorems.Thm_OAI_IdealGaussCRT_gauss_transform_ideal_crt
import Theorems.Thm_OAI_ActualEisensteinCubic_canonicalSextic_pow_ne_one


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
open AddChar MulChar
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hc : IsCoprime P Q)
    [Fintype (O ⧸ P * Q)] [Fintype (O ⧸ P)] [Fintype (O ⧸ Q)]
    (hgoodP : lambda ∉ P) (hgoodQ : lambda ∉ Q)
    (hcharP : ringChar (O ⧸ P) ≠ 2)
    (hcharQ : ringChar (O ⧸ Q) ≠ 2)
    (j k : ℕ) (hj0 : j ≠ 0) (hj6 : j < 6)
    (hk0 : k ≠ 0) (hk6 : k < 6)
    (ψ : AddChar (O ⧸ P * Q) ℂ) (h : O ⧸ P * Q) :
    (∑ x : O ⧸ P * Q,
      (canonicalSextic P hgoodP ^ j)
          (Ideal.Quotient.factor (Ideal.mul_le_left : P * Q ≤ P) x) *
      (canonicalSextic Q hgoodQ ^ k)
          (Ideal.Quotient.factor (Ideal.mul_le_right : P * Q ≤ Q) x) *
      ψ (h * x)) =
      (if Ideal.Quotient.factor (Ideal.mul_le_left : P * Q ≤ P) h = 0
        then 0 else
        ((canonicalSextic P hgoodP ^ j)
          (Ideal.Quotient.factor (Ideal.mul_le_left : P * Q ≤ P) h))⁻¹ *
          gaussSum (canonicalSextic P hgoodP ^ j)
            (IdealGaussCRT.leftAddChar
              (Ideal.quotientMulEquivQuotientProd P Q hc) ψ)) *
      (if Ideal.Quotient.factor (Ideal.mul_le_right : P * Q ≤ Q) h = 0
        then 0 else
        ((canonicalSextic Q hgoodQ ^ k)
          (Ideal.Quotient.factor (Ideal.mul_le_right : P * Q ≤ Q) h))⁻¹ *
          gaussSum (canonicalSextic Q hgoodQ ^ k)
            (IdealGaussCRT.rightAddChar
              (Ideal.quotientMulEquivQuotientProd P Q hc) ψ)) := by
  exact IdealGaussCRT.gauss_transform_ideal_crt P Q hc
    (canonicalSextic P hgoodP ^ j)
    (canonicalSextic Q hgoodQ ^ k) ψ
    (canonicalSextic_pow_ne_one P hgoodP hcharP hj0 hj6)
    (canonicalSextic_pow_ne_one Q hgoodQ hcharQ hk0 hk6) h
end OAI.ActualEisensteinCubic
