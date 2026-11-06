-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.breveE_bilinear_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:45:58.925981+00:00
-- url     : https://prove2.me/submissions/468b2baf-9ffa-43e6-aa6b-f8392687a154

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_BinaryGaussian
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianDualLimit
import Theorems.Thm_OAI_ActualEisensteinCoordinates_eval_mul
import Theorems.Thm_OAI_ActualEisensteinCubic_breveE_int_trace_div
import Theorems.Thm_OAI_ActualEisensteinCubic_eisEmbedding_eval
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
theorem _root_.solution (u v m n : ℤ) :
    ShortDraftTrace.breveE
      (eisEmbedding (ActualEisensteinCoordinates.eval u v) *
        eisEmbedding (ActualEisensteinCoordinates.eval m n) / eisLam) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((u*n+v*m-v*n : ℤ) : ℂ)) := by
  rw [← map_mul, ActualEisensteinCoordinates.eval_mul]
  rw [eisEmbedding_eval]
  simpa using
    breveE_int_trace_div 1 (u*m-v*n) (u*n+v*m-v*n) (by norm_num)
end OAI.ActualEisensteinCubic
