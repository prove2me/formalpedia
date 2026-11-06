-- Prove2me | solution 1 for OAI.IdealGaussCRT.leftAddChar_traceProd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:36:40.920868+00:00
-- url     : https://prove2.me/submissions/58af932c-63bb-4e25-9f13-754631c900de

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ChineseRemainder
import Theorems.Thm_OAI_IdealGaussCRT_crt_left_inverse_coordinate
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk

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
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ)
    {a b u v : A} (hbez : u * a + v * b = 1)
    (ha : ι a ≠ 0) (hb : ι b ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1) :
    leftAddChar
      (Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
        (principal_coprime_of_bezout hbez))
      (traceProdChar ι ψ lam a b ha hb hlam hbase) =
      (traceModChar ι ψ lam a ha hlam hbase).mulShift
        (Ideal.Quotient.mk (Ideal.span {a}) v) := by
  ext z
  refine Quotient.inductionOn' z ?_
  intro x
  change traceProdChar ι ψ lam a b ha hb hlam hbase
      ((Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
        (principal_coprime_of_bezout hbez)).symm
        (Ideal.Quotient.mk (Ideal.span {a}) x, 0)) =
    (traceModChar ι ψ lam a ha hlam hbase).mulShift
      (Ideal.Quotient.mk (Ideal.span {a}) v)
      (Ideal.Quotient.mk (Ideal.span {a}) x)
  rw [crt_left_inverse_coordinate hbez x]
  simp only [traceProdChar_mk, AddChar.mulShift_apply, ← map_mul,
    traceModChar_mk]
  congr 1
  simp only [map_mul]
  field_simp
end OAI.IdealGaussCRT
