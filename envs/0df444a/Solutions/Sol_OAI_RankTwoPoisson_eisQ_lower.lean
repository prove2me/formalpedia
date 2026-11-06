-- Prove2me | solution 1 for OAI.RankTwoPoisson.eisQ_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:25:54.388452+00:00
-- url     : https://prove2.me/submissions/44d18cae-e1df-4146-b9f5-ad15802558fe

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
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
open OAI.RankTwoPoisson
open Real
namespace OAI.RankTwoPoisson
theorem _root_.solution (z : ℤ × ℤ) :
    ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) / 2 ≤ eisQ z := by
  dsimp [eisQ]
  nlinarith [sq_nonneg ((z.1 : ℝ) - (z.2 : ℝ))]
end OAI.RankTwoPoisson
