-- Prove2me | solution 2 for OAI.IdealGaussCRT.addChar_crt_factor
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:48:29.607032+00:00
-- url     : https://prove2.me/submissions/a0dfd56d-aa0c-4c2b-8691-5b7f8cbfc3f3

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

theorem solution (e : T ≃+* R × S) (ψ : AddChar T ℂ) (x : T) :
    ψ x = leftAddChar e ψ (e x).1 * rightAddChar e ψ (e x).2 := by
  show ψ x = ψ (e.symm ((e x).1, 0)) * ψ (e.symm (0, (e x).2))
  rw [← AddChar.map_add_eq_mul, ← map_add]
  have h : ((e x).1, (0 : S)) + (0, (e x).2) = e x := by ext <;> simp
  rw [h]
  simp
