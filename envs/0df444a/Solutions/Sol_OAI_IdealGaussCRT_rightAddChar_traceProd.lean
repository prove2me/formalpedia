-- Prove2me | solution 1 for OAI.IdealGaussCRT.rightAddChar_traceProd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:36:43.2302+00:00
-- url     : https://prove2.me/submissions/2e024144-1e68-4d49-a3f7-df6b4acb0a0b

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ChineseRemainder
import Theorems.Thm_OAI_IdealGaussCRT_crt_right_inverse_coordinate
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
    rightAddChar
      (Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
        (principal_coprime_of_bezout hbez))
      (traceProdChar ι ψ lam a b ha hb hlam hbase) =
      (traceModChar ι ψ lam b hb hlam hbase).mulShift
        (Ideal.Quotient.mk (Ideal.span {b}) u) := by
  ext z
  refine Quotient.inductionOn' z ?_
  intro y
  change traceProdChar ι ψ lam a b ha hb hlam hbase
      ((Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
        (principal_coprime_of_bezout hbez)).symm
        (0, Ideal.Quotient.mk (Ideal.span {b}) y)) =
    (traceModChar ι ψ lam b hb hlam hbase).mulShift
      (Ideal.Quotient.mk (Ideal.span {b}) u)
      (Ideal.Quotient.mk (Ideal.span {b}) y)
  rw [crt_right_inverse_coordinate hbez y]
  simp only [traceProdChar_mk, AddChar.mulShift_apply, ← map_mul,
    traceModChar_mk]
  congr 1
  simp only [map_mul]
  field_simp
end OAI.IdealGaussCRT
