-- Prove2me | solution 1 for OAI.IdealGaussCRT.bezout_of_principal_coprime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:35:42.778439+00:00
-- url     : https://prove2.me/submissions/1f1aff71-a001-4ff9-a070-5c9c5de0ba86

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
    {a b : A} (h : IsCoprime (Ideal.span {a}) (Ideal.span {b})) :
    ∃ u v : A, u * a + v * b = 1 := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Ideal.isCoprime_iff_exists.mp h
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.mp hx
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp hy
  refine ⟨u, v, ?_⟩
  rw [hu, hv] at hxy
  convert hxy using 1; ring
end OAI.IdealGaussCRT
