-- Prove2me | solution 1 for OAI.FourierBridge.logPhase_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:14:50.849611+00:00
-- url     : https://prove2.me/submissions/77c31677-d88a-49b3-b614-2e33d95a6a18

import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly
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
open OAI.FourierBridge
open scoped FourierTransform SchwartzMap
namespace OAI.FourierBridge
theorem _root_.solution (t y : ℝ) : ‖logPhase t y‖ = 1 := by
  simpa [logPhase] using
    Complex.norm_exp_ofReal_mul_I (2 * Real.pi * t * y)
end OAI.FourierBridge
