-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.actual_oscillatory_gaussian_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:49:40.162636+00:00
-- url     : https://prove2.me/submissions/a89bea4a-e82c-4e32-adf8-63195cc9f3ef

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_BinaryGaussian
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianDualLimit
import Theorems.Thm_OAI_ActualEisensteinCubic_eisEmbedding_eval_norm_sq
import Theorems.Thm_OAI_ActualEisensteinCubic_quadraticTraceModChar_coordinate
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
      Complex.exp (-(Real.pi : ℂ) *
        ((η : ℂ) * ((m*m-m*n+n*n : ℤ) : ℂ) -
          2 * Complex.I *
            (((-b*m*m+2*a*m*n+(b-a)*n*n : ℤ) : ℂ) /
              ((a*a-a*b+b*b : ℤ) : ℂ)))) := by
  dsimp only
  rw [quadraticTraceModChar_coordinate a b m n hc]
  have hnormC : ((‖eisEmbedding
      (ActualEisensteinCoordinates.eval m n)‖ : ℂ)^2) =
      ((m*m-m*n+n*n : ℤ) : ℂ) := by
    exact_mod_cast eisEmbedding_eval_norm_sq m n
  rw [hnormC]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring
end OAI.ActualEisensteinCubic
