-- Prove2me | solution 1 for OAI.IdealGaussCRT.gauss_sum_ideal_crt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:37:14.932228+00:00
-- url     : https://prove2.me/submissions/6055c715-4a2d-4d3b-88dc-1c871a7a1575

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ChineseRemainder
import Theorems.Thm_OAI_GaussCRT_gauss_sum_crt
import Theorems.Thm_OAI_IdealGaussCRT_gauss_sum_crt

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
open scoped Classical
open OAI.IdealGaussCRT
variable {T R S : Type*} [CommRing T] [CommRing R] [CommRing S]
namespace OAI.IdealGaussCRT
theorem _root_.solution {A : Type*} [CommRing A]
    (I J : Ideal A) (h : IsCoprime I J)
    [Fintype (A ⧸ I * J)] [Fintype (A ⧸ I)] [Fintype (A ⧸ J)]
    (χI : MulChar (A ⧸ I) ℂ) (χJ : MulChar (A ⧸ J) ℂ)
    (ψ : AddChar (A ⧸ I * J) ℂ) :
    (∑ x : A ⧸ I * J,
      χI (Ideal.Quotient.factor (Ideal.mul_le_left : I * J ≤ I) x) *
      χJ (Ideal.Quotient.factor (Ideal.mul_le_right : I * J ≤ J) x) * ψ x) =
      gaussSum χI (leftAddChar (Ideal.quotientMulEquivQuotientProd I J h) ψ) *
      gaussSum χJ (rightAddChar (Ideal.quotientMulEquivQuotientProd I J h) ψ) := by
  let e := Ideal.quotientMulEquivQuotientProd I J h
  convert gauss_sum_crt e χI χJ ψ using 1
  congr 1
  ext x
  simp only [e, Ideal.quotientMulEquivQuotientProd_fst,
    Ideal.quotientMulEquivQuotientProd_snd]
end OAI.IdealGaussCRT
