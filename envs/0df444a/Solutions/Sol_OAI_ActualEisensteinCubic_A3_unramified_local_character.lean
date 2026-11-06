-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.A3_unramified_local_character
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:19:54.823198+00:00
-- url     : https://prove2.me/submissions/fa267ab9-e4cc-4496-bfdd-48d1c827d2dc

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftCusp_A3_unramified_inverse_congr
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
    (a b c d : O) (hdet : a * d - b * c = 1)
    (hb : -b ∈ P) :
    cubicChar P hgood (Ideal.Quotient.mk P a) *
      cubicChar P hgood (Ideal.Quotient.mk P d) = 1 := by
  have hb0 : Ideal.Quotient.mk P (-b) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr hb
  have hrel := congrArg (Ideal.Quotient.mk P)
    (A3_unramified_inverse_congr a b c d hdet)
  simp only [map_mul, map_add, map_one] at hrel
  have hbb : Ideal.Quotient.mk P b = 0 := by
    have h := congrArg Neg.neg hb0
    simpa only [map_neg, neg_zero, neg_neg] using h
  simp only [hbb, zero_mul, add_zero] at hrel
  have hh := congrArg (cubicChar P hgood) hrel
  simpa only [map_mul, map_one] using hh
end OAI.ActualEisensteinCubic
