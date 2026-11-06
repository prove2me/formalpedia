-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.A3_ramified_local_character
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:19:43.696203+00:00
-- url     : https://prove2.me/submissions/b891d59f-e1a1-485c-a624-284974fb6a25

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftCusp_A3_ramified_det_relation
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
open OAI.ActualEisensteinCubic
open ShortDraftCusp
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (a b c d u : O) (hdet : a * d - b * c = 1)
    (hA : a - u * b ∈ P) :
    cubicChar P hgood (Ideal.Quotient.mk P a) *
      cubicChar P hgood (Ideal.Quotient.mk P (c - u * d)) =
      cubicChar P hgood (Ideal.Quotient.mk P (-u)) := by
  have hA0 : Ideal.Quotient.mk P (a - u * b) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr hA
  have hrel := congrArg (Ideal.Quotient.mk P)
    (A3_ramified_det_relation a b c d u hdet)
  simp only [map_sub, map_mul, map_neg, hA0, mul_zero, sub_zero] at hrel
  have hh := congrArg (cubicChar P hgood) hrel
  simpa only [map_mul, map_sub, map_neg] using hh
end OAI.ActualEisensteinCubic
