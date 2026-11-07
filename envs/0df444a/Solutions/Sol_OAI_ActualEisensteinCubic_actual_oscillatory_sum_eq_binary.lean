-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.actual_oscillatory_sum_eq_binary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:26:41.248049+00:00
-- url     : https://prove2.me/submissions/119118e5-68ee-4398-8e9c-849521b8f9ea

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_OscillatoryGaussian
import Theorems.Thm_OAI_ActualEisensteinCubic_actual_oscillatory_binary_coordinate
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
open OAI.ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    (a b : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) :
    let c : O := ActualEisensteinCoordinates.eval a b
    (∑' z : O,
      (eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates c hc)
        (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
        (‖eisEmbedding z‖ ^ 2 : ℂ))) =
      ∑' p : ℤ × ℤ,
        RankTwoComplex.binaryGaussian
          (OscSpecial.A η (a : ℝ) (b : ℝ))
          (OscSpecial.B η (a : ℝ) (b : ℝ))
          (OscSpecial.D η (a : ℝ) (b : ℝ)) p := by
  let W : O → ℂ := fun z =>
    (eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates
        (ActualEisensteinCoordinates.eval a b) hc)
      (Ideal.Quotient.mk (Ideal.span {ActualEisensteinCoordinates.eval a b}) z ^ 2) *
    Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
      (‖eisEmbedding z‖ ^ 2 : ℂ))
  have h := (latticeCoordEquiv.symm.tsum_eq W).symm
  simpa only [W, latticeCoordEquiv] using
    (show (∑' z : O, W z) =
      ∑' p : ℤ × ℤ,
        RankTwoComplex.binaryGaussian
          (OscSpecial.A η (a : ℝ) (b : ℝ))
          (OscSpecial.B η (a : ℝ) (b : ℝ))
          (OscSpecial.D η (a : ℝ) (b : ℝ)) p from by
      calc
        (∑' z : O, W z) = ∑' p : ℤ × ℤ, W (latticeCoordEquiv.symm p) := h
        _ = _ := by
          apply tsum_congr
          intro p
          have hp : latticeCoordEquiv.symm p =
              ActualEisensteinCoordinates.eval p.1 p.2 := rfl
          rw [hp]
          exact actual_oscillatory_binary_coordinate a b p.1 p.2 hc η)
end OAI.ActualEisensteinCubic
