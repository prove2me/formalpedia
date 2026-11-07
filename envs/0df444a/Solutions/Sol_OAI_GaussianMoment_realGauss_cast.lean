-- Prove2me | solution 1 for OAI.GaussianMoment.realGauss_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:25:37.085169+00:00
-- url     : https://prove2.me/submissions/a51b6cda-81ed-4b71-8e88-da6e88181c0a

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_OscillatoryGaussian
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
open OAI.GaussianMoment
open scoped Topology
open Filter
namespace OAI.GaussianMoment
theorem _root_.solution (t : ℝ) (z : ℤ × ℤ) :
    (realGauss t z : ℂ) = RankTwoEisShift.shifted t 0 0 z := by
  dsimp [realGauss, RankTwoPoisson.eisQ,
    RankTwoEisShift.shifted, RankTwoEisShift.Q]
  rw [← Complex.ofReal_exp]
  congr 1
  ring_nf
end OAI.GaussianMoment
