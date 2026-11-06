-- Prove2me | solution 1 for OAI.RankTwoEisShift.dualPhase_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:44:47.84477+00:00
-- url     : https://prove2.me/submissions/9022ae6f-5281-4007-8724-5e847ebd6b8a

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_BinaryGaussian
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
open OAI.RankTwoEisShift
namespace OAI.RankTwoEisShift
theorem _root_.solution (k l : ℤ) (x y : ℝ) :
    ‖dualPhase k l x y‖ = 1 := by
  simp [dualPhase, Complex.norm_exp, Complex.mul_re]
end OAI.RankTwoEisShift
