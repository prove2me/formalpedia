-- Prove2me | solution 1 for OAI.IdealGaussCRT.gauss_shift_bezout_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:36:43.950075+00:00
-- url     : https://prove2.me/submissions/abd22d6b-9bd9-4490-854f-268553be4559

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ChineseRemainder
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_IdealGaussCRT_bezout_inverse_left
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
    {a b u v : A} [Fintype (A ⧸ Ideal.span {a})]
    (hbez : u * a + v * b = 1)
    (χ : MulChar (A ⧸ Ideal.span {a}) ℂ)
    (ψ : AddChar (A ⧸ Ideal.span {a}) ℂ) :
    gaussSum χ (ψ.mulShift (Ideal.Quotient.mk (Ideal.span {a}) v)) =
      χ (Ideal.Quotient.mk (Ideal.span {a}) b) * gaussSum χ ψ := by
  let mb := Ideal.Quotient.mk (Ideal.span {a}) b
  let mv := Ideal.Quotient.mk (Ideal.span {a}) v
  have hprod : mb * mv = 1 := bezout_inverse_left hbez
  have hu : IsUnit mv := IsUnit.of_mul_eq_one_right mb hprod
  have hχ : χ mb * χ mv = 1 := by rw [← map_mul, hprod, map_one]
  have hshift := gaussSum_mulShift χ ψ hu.unit
  have hshift' : χ mv * gaussSum χ (ψ.mulShift mv) = gaussSum χ ψ := by
    simpa only [hu.unit_spec] using hshift
  calc
    gaussSum χ (ψ.mulShift mv) =
        (χ mb * χ mv) * gaussSum χ (ψ.mulShift mv) := by rw [hχ, one_mul]
    _ = χ mb * (χ mv * gaussSum χ (ψ.mulShift mv)) := by ring
    _ = χ mb * gaussSum χ ψ := by rw [hshift']
end OAI.IdealGaussCRT
