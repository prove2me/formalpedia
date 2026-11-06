-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.canonicalSextic_sixth_power_mask
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:15:05.101046+00:00
-- url     : https://prove2.me/submissions/359710d4-3fc7-41d4-8792-28322d663570

import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly
import Theorems.Thm_OAI_ActualEisensteinCubic_canonicalSextic_pow_six
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftSextic_sextic_power_is_unit_mask
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
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (a : O) :
    canonicalSextic P hgood (Ideal.Quotient.mk P (a ^ 6)) =
      if a ∈ P then 0 else 1 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  rw [map_pow, ShortDraftSextic.sextic_power_is_unit_mask
    (canonicalSextic P hgood) (canonicalSextic_pow_six P hgood)]
  by_cases ha : a ∈ P
  · simp [ha, isUnit_iff_ne_zero, Ideal.Quotient.eq_zero_iff_mem]
  · simp [ha, isUnit_iff_ne_zero, Ideal.Quotient.eq_zero_iff_mem]
end OAI.ActualEisensteinCubic
