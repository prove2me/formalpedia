-- Prove2me | solution 1 for OAI.AnalyticBridge.restrict_positive_side_to_weight_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:10:48.617201+00:00
-- url     : https://prove2.me/submissions/6e59e5ec-3c2f-4cf1-9fcc-2b4966a90121

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
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
open OAI.AnalyticBridge
namespace OAI.AnalyticBridge
theorem _root_.solution
    {Ω : Type*} (S : Finset Ω) (w : Ω → ℂ) (U : Ω → ℂ) :
    (∑ ω ∈ S with w ω ≠ 0, ‖w ω‖ * ‖U ω‖ ^ 2) =
      (∑ ω ∈ S, ‖w ω‖ * ‖U ω‖ ^ 2) := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases hw : w ω = 0 <;> simp [hw]
end OAI.AnalyticBridge
