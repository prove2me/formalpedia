-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.osc_q_eq_eis_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:29:49.073268+00:00
-- url     : https://prove2.me/submissions/ae39c45a-b3bd-4cf6-83b0-0895fd12dcff

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_RationalApproximation
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_AbelPhaseLimit
import Theorems.Thm_OAI_ActualEisensteinCubic_eisEmbedding_eval_norm_sq
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
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open OAI.ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (a b : ℤ) :
    OscSpecial.q (a : ℝ) (b : ℝ) =
      ‖eisEmbedding (ActualEisensteinCoordinates.eval a b)‖ ^ 2 := by
  rw [eisEmbedding_eval_norm_sq]
  dsimp [OscSpecial.q]
  push_cast
  ring
end OAI.ActualEisensteinCubic
