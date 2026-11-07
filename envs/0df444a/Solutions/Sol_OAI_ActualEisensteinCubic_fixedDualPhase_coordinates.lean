-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.fixedDualPhase_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:29:37.441201+00:00
-- url     : https://prove2.me/submissions/fad3b68a-7aae-4b65-94fd-a586ef491506

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_RationalApproximation
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_AbelPhaseLimit
import Theorems.Thm_OAI_ActualEisensteinCubic_eisEmbedding_eval


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
open EisensteinEmbedding ConcreteTraceCRT Complex
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (a b x y : ℤ) :
    fixedDualPhase (ActualEisensteinCoordinates.eval a b)
      (ActualEisensteinCoordinates.eval x y) =
      ShortDraftTrace.breveE
        ((-(((a : ℂ)+(b : ℂ)*omega3) *
          (((x : ℂ)+(y : ℂ)*omega3)^2))) / eisLam / 4) := by
  unfold fixedDualPhase
  rw [map_neg, map_mul, map_pow, eisEmbedding_eval, eisEmbedding_eval]
end OAI.ActualEisensteinCubic
