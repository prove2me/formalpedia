-- Prove2me | solution 1 for OAI.IdealGaussCRT.crt_right_inverse_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:35:47.545324+00:00
-- url     : https://prove2.me/submissions/10f9c7f8-f1b6-4a03-b3cf-1351b759fffe

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
open scoped Classical
open OAI.IdealGaussCRT
variable {T R S : Type*} [CommRing T] [CommRing R] [CommRing S]
namespace OAI.IdealGaussCRT
theorem _root_.solution {A : Type*} [CommRing A]
    {a b u v : A} (hbez : u * a + v * b = 1) (y : A) :
    (Ideal.quotientMulEquivQuotientProd
      (Ideal.span {a}) (Ideal.span {b})
      (principal_coprime_of_bezout hbez)).symm
        (0, Ideal.Quotient.mk (Ideal.span {b}) y) =
      Ideal.Quotient.mk ((Ideal.span {a}) * (Ideal.span {b})) (y * u * a) := by
  let I : Ideal A := Ideal.span {a}
  let J : Ideal A := Ideal.span {b}
  let e := Ideal.quotientMulEquivQuotientProd I J
    (principal_coprime_of_bezout hbez)
  apply e.injective
  apply Prod.ext
  · change (e (e.symm (0, Ideal.Quotient.mk J y))).1 =
      (e (Ideal.Quotient.mk (I * J) (y * u * a))).1
    rw [e.apply_symm_apply]
    simp only [e, Ideal.quotientMulEquivQuotientProd_fst,
      Ideal.Quotient.factor_mk]
    symm
    apply (Ideal.Quotient.eq_zero_iff_mem).mpr
    exact Ideal.mem_span_singleton.mpr ⟨y * u, by ring⟩
  · change (e (e.symm (0, Ideal.Quotient.mk J y))).2 =
      (e (Ideal.Quotient.mk (I * J) (y * u * a))).2
    rw [e.apply_symm_apply]
    simp only [e, Ideal.quotientMulEquivQuotientProd_snd,
      Ideal.Quotient.factor_mk]
    apply Ideal.Quotient.eq.mpr
    change y - y * u * a ∈ J
    rw [Ideal.mem_span_singleton]
    refine ⟨y * v, ?_⟩
    calc
      y - y * u * a = y * (u * a + v * b) - y * u * a := by rw [hbez]; ring
      _ = b * (y * v) := by ring
end OAI.IdealGaussCRT
