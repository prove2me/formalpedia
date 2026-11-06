-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.eisEmbedding_traceLambda
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:12:31.512357+00:00
-- url     : https://prove2.me/submissions/958eb367-7fd8-4ed7-927f-b77a922463b2

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
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
open EisensteinEmbedding ConcreteTraceCRT IdealGaussCRT
namespace OAI.ActualEisensteinCubic
theorem _root_.solution :
    eisEmbedding traceLambda = eisLam := by
  have hgen : pb.gen = omega := by
    simpa only [pb, omega] using
      (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis_gen
  change embedding omega3 omega3_sq (1 + 2 * omega : O) = 1 + 2 * omega3
  rw [← hgen]
  simp only [map_add, map_one, map_mul, map_ofNat, embedding_gen]
end OAI.ActualEisensteinCubic
