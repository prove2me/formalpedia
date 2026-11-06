-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.breveE_real_trace_of_O
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:49:44.103804+00:00
-- url     : https://prove2.me/submissions/cfb1ea63-026c-4917-b434-69b8864ea945

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianDualLimit
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianFiberMass
import Theorems.Thm_OAI_ActualEisensteinCubic_breveE_real_trace_div
import Theorems.Thm_OAI_ActualEisensteinCoordinates_eval_coords
import Theorems.Thm_OAI_ActualEisensteinCubic_eisEmbedding_eval
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftLatticeCount_coords_eval
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
open Filter Real Asymptotics
open OAI.ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (r : ℝ) (z : O) :
    ShortDraftTrace.breveE (eisEmbedding z / eisLam / (r : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((ActualEisensteinCoordinates.coords z).2 : ℂ) / (r : ℂ)) := by
  rw [← ActualEisensteinCoordinates.eval_coords z]
  rw [eisEmbedding_eval]
  simp only [ShortDraftLatticeCount.coords_eval]
  exact breveE_real_trace_div r _ _
end OAI.ActualEisensteinCubic
