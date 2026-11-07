-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.actual_oscillatory_binary_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:25:33.827191+00:00
-- url     : https://prove2.me/submissions/7732a21e-f95e-4f7f-94ac-4a108cc58c1d

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_OscillatoryGaussian
import Theorems.Thm_OAI_ActualEisensteinCubic_actual_oscillatory_gaussian_coordinate
import Theorems.Thm_OAI_ActualEisensteinCubic_coordinate_norm_pos_of_nonzero
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
    (a b m n : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let z : O := ActualEisensteinCoordinates.eval m n
    (eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates c hc)
        (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
        (‖eisEmbedding z‖ ^ 2 : ℂ)) =
      RankTwoComplex.binaryGaussian
        (OscSpecial.A η (a : ℝ) (b : ℝ))
        (OscSpecial.B η (a : ℝ) (b : ℝ))
        (OscSpecial.D η (a : ℝ) (b : ℝ)) (m,n) := by
  have hqZ : a*a-a*b+b*b ≠ 0 :=
    (coordinate_norm_pos_of_nonzero a b hc).ne'
  have hqC : (((a*a-a*b+b*b : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast hqZ
  dsimp only
  rw [actual_oscillatory_gaussian_coordinate a b m n hc η]
  unfold RankTwoComplex.binaryGaussian OscSpecial.A OscSpecial.B
    OscSpecial.D OscSpecial.q
  congr 1
  push_cast
  field_simp [hqC]
  ring
end OAI.ActualEisensteinCubic
