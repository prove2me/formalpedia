-- Prove2me | solution 1 for OAI.IdealGaussCRT.bezout_inverse_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:36:25.502307+00:00
-- url     : https://prove2.me/submissions/3483bfad-cc07-401b-b6f3-403e1f718f5d

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
    {a b u v : A} (hbez : u * a + v * b = 1) :
    (Ideal.Quotient.mk (Ideal.span {b}) a) *
      (Ideal.Quotient.mk (Ideal.span {b}) u) = 1 := by
  rw [← map_mul]
  apply Ideal.Quotient.eq.mpr
  change a * u - 1 ∈ Ideal.span {b}
  rw [Ideal.mem_span_singleton]
  refine ⟨-v, ?_⟩
  calc
    a * u - 1 = a * u - (u * a + v * b) := by rw [hbez]
    _ = b * -v := by ring
end OAI.IdealGaussCRT
