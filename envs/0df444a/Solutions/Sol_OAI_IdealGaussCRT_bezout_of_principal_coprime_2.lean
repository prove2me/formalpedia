-- Prove2me | solution 2 for OAI.IdealGaussCRT.bezout_of_principal_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:48:52.085267+00:00
-- url     : https://prove2.me/submissions/0dafdafe-5a24-45e0-a418-cdfe5817d203

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

theorem solution {A : Type*} [CommRing A]
    {a b : A} (h : IsCoprime (Ideal.span {a}) (Ideal.span {b})) :
    ∃ u v : A, u * a + v * b = 1 :=
  (Ideal.isCoprime_span_singleton_iff a b).mp h
