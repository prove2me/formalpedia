-- Prove2me | solution 1 for OAI.IdealGaussCRT.gauss_transform_ideal_crt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:20:56.670106+00:00
-- url     : https://prove2.me/submissions/bcdd5b7a-a7dd-45c4-815a-5c00fd7b0785

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Theorems.Thm_OAI_IdealGaussCRT_gauss_transform_crt
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
open OAI.IdealGaussCRT
open AddChar MulChar
namespace OAI.IdealGaussCRT
theorem _root_.solution {A : Type*} [CommRing A]
    (I J : Ideal A) (hc : IsCoprime I J)
    [I.IsMaximal] [J.IsMaximal]
    [Fintype (A ⧸ I * J)] [Fintype (A ⧸ I)] [Fintype (A ⧸ J)]
    (χI : MulChar (A ⧸ I) ℂ) (χJ : MulChar (A ⧸ J) ℂ)
    (ψ : AddChar (A ⧸ I * J) ℂ)
    (hχI : χI ≠ 1) (hχJ : χJ ≠ 1)
    (h : A ⧸ I * J) :
    (∑ x : A ⧸ I * J,
      χI (Ideal.Quotient.factor (Ideal.mul_le_left : I * J ≤ I) x) *
      χJ (Ideal.Quotient.factor (Ideal.mul_le_right : I * J ≤ J) x) *
      ψ (h * x)) =
      (if Ideal.Quotient.factor (Ideal.mul_le_left : I * J ≤ I) h = 0
        then 0 else
        (χI (Ideal.Quotient.factor (Ideal.mul_le_left : I * J ≤ I) h))⁻¹ *
          gaussSum χI
            (leftAddChar (Ideal.quotientMulEquivQuotientProd I J hc) ψ)) *
      (if Ideal.Quotient.factor (Ideal.mul_le_right : I * J ≤ J) h = 0
        then 0 else
        (χJ (Ideal.Quotient.factor (Ideal.mul_le_right : I * J ≤ J) h))⁻¹ *
          gaussSum χJ
            (rightAddChar (Ideal.quotientMulEquivQuotientProd I J hc) ψ)) := by
  let : Field (A ⧸ I) := Ideal.Quotient.field I
  let : Field (A ⧸ J) := Ideal.Quotient.field J
  let e := Ideal.quotientMulEquivQuotientProd I J hc
  convert gauss_transform_crt e χI χJ ψ hχI hχJ h using 1 <;>
    simp only [e, Ideal.quotientMulEquivQuotientProd_fst,
      Ideal.quotientMulEquivQuotientProd_snd]
end OAI.IdealGaussCRT
