-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.eisEmbedding_eval_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:44:35.419287+00:00
-- url     : https://prove2.me/submissions/ac163d8c-444a-4b62-9171-26eb8478595f

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_BinaryGaussian
import Theorems.Thm_OAI_ActualEisensteinCubic_eisEmbedding_eval
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
theorem _root_.solution (x y : ℤ) :
    ‖eisEmbedding (ActualEisensteinCoordinates.eval x y)‖ ^ 2 =
      (x*x-x*y+y*y : ℤ) := by
  rw [eisEmbedding_eval, ← Complex.normSq_eq_norm_sq]
  have hre : ((x : ℂ) + (y : ℂ) * omega3).re =
      (x : ℝ) - (y : ℝ) / 2 := by
    simp [omega3, Complex.add_re, Complex.mul_re]
    ring
  have him : ((x : ℂ) + (y : ℂ) * omega3).im =
      (y : ℝ) * Real.sqrt 3 / 2 := by
    simp [omega3, Complex.add_im, Complex.mul_im]
    ring
  rw [Complex.normSq_apply, hre, him]
  have hs : (Real.sqrt 3)^2 = (3:ℝ) := Real.sq_sqrt (by norm_num)
  push_cast
  nlinarith
end OAI.ActualEisensteinCubic
