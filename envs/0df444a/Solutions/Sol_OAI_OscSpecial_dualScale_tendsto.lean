-- Prove2me | solution 1 for OAI.OscSpecial.dualScale_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:27:44.0472+00:00
-- url     : https://prove2.me/submissions/9c2dee8a-400b-4d58-9f9a-0a8aa4ba4a98

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_OscillatoryGaussian
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_RationalApproximation
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
open OAI.OscSpecial
open scoped Topology
open Filter
namespace OAI.OscSpecial
theorem _root_.solution (a b : ℝ) (hq : 0 < q a b) :
    Tendsto (fun η : ℝ => dualScale η a b)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  have hnum : ContinuousAt (fun η : ℝ => η * q a b) 0 := by fun_prop
  have hden : ContinuousAt (fun η : ℝ => 4 * r η a b) 0 := by
    change ContinuousAt
      (fun η : ℝ => 4 * (1 + 3 * q a b * η ^ 2 / 16)) 0
    fun_prop
  have hden0 : 4 * r 0 a b ≠ 0 := by simp [r]
  have hcont : ContinuousAt (fun η : ℝ => dualScale η a b) 0 := by
    exact hnum.div hden hden0
  have hlim : Tendsto (fun η : ℝ => dualScale η a b)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa [dualScale] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · exact hlim
  · filter_upwards [self_mem_nhdsWithin] with η hη
    change 0 < η at hη
    have hr : 0 < r η a b := by
      unfold r
      positivity
    exact div_pos (mul_pos hη hq) (mul_pos (by norm_num) hr)
end OAI.OscSpecial
