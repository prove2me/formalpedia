-- Prove2me | solution 1 for OAI.RationalPrimeExtraction.eventual_count_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:29:04.683718+00:00
-- url     : https://prove2.me/submissions/9b861942-5a4d-4a66-9459-26d05b3b84cd

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_OscillatoryGaussian
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_RationalApproximation
import Theorems.Thm_OAI_RationalQuant_eventual_log_absorption
import Theorems.Thm_OAI_RationalQuant_scale_large_eventually
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_rational_prime_three_interval_count
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
open OAI.RationalPrimeExtraction
namespace OAI.RationalPrimeExtraction
theorem _root_.solution (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℝ, ∀ D : ℕ, D₀ ≤ (D : ℝ) →
      2 ≤ D ∧
      (D : ℝ) ^ ((4 / 45 : ℝ) - ε) ≤
        ((selected ((D : ℝ) ^ (4 / 45 : ℝ))).card : ℝ) := by
  obtain ⟨Y₀, hcount⟩ := rational_prime_three_interval_count
  obtain ⟨Dlog, hlog⟩ := RationalQuant.eventual_log_absorption ε hε
  obtain ⟨Dscale, hscale⟩ := RationalQuant.scale_large_eventually Y₀
  refine ⟨max Dlog Dscale, ?_⟩
  intro D hD
  have hDl : Dlog ≤ (D : ℝ) := (le_max_left _ _).trans hD
  have hDs : Dscale ≤ (D : ℝ) := (le_max_right _ _).trans hD
  obtain ⟨hDtwo, hY⟩ := hscale (D : ℝ) hDs
  have hDtwoNat : 2 ≤ D := by exact_mod_cast hDtwo
  have habs := hlog (D : ℝ) hDl hDtwo
  have hprime := hcount ((D : ℝ) ^ (4 / 45 : ℝ)) hY
  exact ⟨hDtwoNat, habs.trans (by simpa only [selected] using hprime)⟩
end OAI.RationalPrimeExtraction
