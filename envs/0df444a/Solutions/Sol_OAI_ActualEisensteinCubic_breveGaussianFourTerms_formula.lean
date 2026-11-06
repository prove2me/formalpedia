-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.breveGaussianFourTerms_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:19:39.935243+00:00
-- url     : https://prove2.me/submissions/03c1b72b-808c-4509-8850-e1bd91aaf955

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
import Theorems.Thm_OAI_ActualEisensteinCubic_breveE_quarter_trace
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
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
open EisensteinEmbedding ConcreteTraceCRT Complex
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (a b : ℤ) :
    breveGaussianFourTerms a b =
      (1 + Complex.I ^ (-b) + Complex.I ^ a + Complex.I ^ (b-a)) / 2 := by
  let c : ℂ := (a : ℂ) + (b : ℂ) * omega3
  have hfirst : ShortDraftTrace.breveE (((-c) / eisLam) / 4) =
      Complex.I ^ (-b) := by
    have hc : -c = ((-a : ℤ) : ℂ) + ((-b : ℤ) : ℂ) * omega3 := by
      dsimp [c]
      push_cast
      ring
    rw [hc]
    exact breveE_quarter_trace (-a) (-b)
  have hsecond : ShortDraftTrace.breveE
      (((-c * omega3 ^ 2) / eisLam) / 4) = Complex.I ^ a := by
    have hc : -c * omega3 ^ 2 = ((a-b : ℤ) : ℂ) + (a : ℂ) * omega3 := by
      dsimp [c]
      push_cast
      linear_combination -(a : ℂ) * omega3_sq -
        (b : ℂ) * (omega3 - 1) * omega3_sq
    rw [hc]
    exact breveE_quarter_trace (a-b) a
  have hthird : ShortDraftTrace.breveE
      (((-c * (1 + omega3) ^ 2) / eisLam) / 4) =
      Complex.I ^ (b-a) := by
    have hω : (1 + omega3) ^ 2 = omega3 := by
      linear_combination omega3_sq
    have hc : -c * (1 + omega3) ^ 2 =
        (b : ℂ) + ((b-a : ℤ) : ℂ) * omega3 := by
      rw [hω]
      dsimp [c]
      push_cast
      linear_combination -(b : ℂ) * omega3_sq
    rw [hc]
    exact breveE_quarter_trace b (b-a)
  dsimp [breveGaussianFourTerms]
  rw [hfirst, hsecond, hthird]
  simp only [map_zero_eq_one]
end OAI.ActualEisensteinCubic
