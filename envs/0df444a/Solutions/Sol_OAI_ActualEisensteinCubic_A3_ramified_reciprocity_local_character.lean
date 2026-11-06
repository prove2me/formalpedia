-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.A3_ramified_reciprocity_local_character
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:19:44.519203+00:00
-- url     : https://prove2.me/submissions/f57a820c-9a4a-4484-8b8e-d911ddd256e5

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftCusp_A3_ramified_reciprocity_congr
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
    (a b cprime d u : O)
    (hdet : a * d - b * (u * cprime) = 1)
    (ha : a ∈ P) :
    cubicChar P hgood (Ideal.Quotient.mk P (a - u * b)) *
      cubicChar P hgood (Ideal.Quotient.mk P cprime) = 1 := by
  have ha0 : Ideal.Quotient.mk P a = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr ha
  have hrel := congrArg (Ideal.Quotient.mk P)
    (A3_ramified_reciprocity_congr a b cprime d u hdet)
  simp only [map_sub, map_mul, map_add, map_one, ha0, zero_mul,
    add_zero] at hrel
  have hh := congrArg (cubicChar P hgood) hrel
  simpa only [map_mul, map_sub, map_one, ha0, zero_sub, add_zero] using hh
end OAI.ActualEisensteinCubic
