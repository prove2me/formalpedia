-- Prove2me | solution 1 for OAI.GaussianMoment.realGauss_summable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:25:25.649211+00:00
-- url     : https://prove2.me/submissions/3430a655-031d-4944-80a9-8188df53f654

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_OscillatoryGaussian
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_RankTwoPoisson_eis_gauss_summable
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
theorem _root_.solution {t : ℝ} (ht : 0 < t) :
    Summable (realGauss t) := by
  have h := (RankTwoPoisson.eis_gauss_summable ht).norm
  convert h using 1
  funext z
  dsimp [realGauss, RankTwoPoisson.eisGauss]
  rw [Complex.norm_exp]
  simp
end OAI.GaussianMoment
