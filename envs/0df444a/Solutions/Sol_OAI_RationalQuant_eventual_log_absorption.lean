-- Prove2me | solution 1 for OAI.RationalQuant.eventual_log_absorption
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:27:28.385269+00:00
-- url     : https://prove2.me/submissions/b4e66be6-86b5-4f2d-8b6b-617abcf9604d

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_OscillatoryGaussian
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_RationalApproximation
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


section
namespace OAI
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
namespace RationalQuant
private theorem cpos : 0 < Real.log 2 / 20 := by
  have h : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  positivity
end RationalQuant
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
namespace RationalPrimeExtraction
end RationalPrimeExtraction
open ActualEisensteinCubic ShortDraftLatticeCount
namespace RationalPrimeExtraction
open ActualEisensteinCubic ShortDraftLatticeCount
end RationalPrimeExtraction
namespace OscSpecial
end OscSpecial
namespace GaussianMoment
open scoped Topology
open Filter
end GaussianMoment
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
namespace OscSpecial
open scoped Topology
open Filter
end OscSpecial
end
end OAI
end

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
open OAI.RationalQuant
namespace OAI.RationalQuant
theorem _root_.solution (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → 2 ≤ D →
      D ^ ((4 / 45 : ℝ) - ε) ≤
        (Real.log 2 / 20) *
          (D ^ (4 / 45 : ℝ) / Real.log (D ^ (4 / 45 : ℝ))) := by
  have hsmall := (isLittleO_log_rpow_atTop hε).bound cpos
  obtain ⟨D₀, hD₀⟩ := eventually_atTop.mp hsmall
  refine ⟨D₀, ?_⟩
  intro D hD hDtwo
  have hDpos : 0 < D := by linarith
  have hDone : 1 ≤ D := by linarith
  have hlogDpos : 0 < Real.log D := Real.log_pos (by linarith)
  have hpowpos : 0 < D ^ (4 / 45 : ℝ) := Real.rpow_pos_of_pos hDpos _
  have hlogYpos : 0 < Real.log (D ^ (4 / 45 : ℝ)) := by
    rw [Real.log_rpow hDpos]
    positivity
  have hlogD : Real.log D ≤
      (Real.log 2 / 20) * D ^ ε := by
    have h := hD₀ D hD
    simpa only [Real.norm_eq_abs, abs_of_pos hlogDpos,
      abs_of_pos (Real.rpow_pos_of_pos hDpos ε)] using h
  have hYleD : D ^ (4 / 45 : ℝ) ≤ D := by
    calc
      D ^ (4 / 45 : ℝ) ≤ D ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hDone (by norm_num)
      _ = D := by simp
  have hlogY : Real.log (D ^ (4 / 45 : ℝ)) ≤
      (Real.log 2 / 20) * D ^ ε :=
    (Real.log_le_log hpowpos hYleD).trans hlogD
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hlogYpos).mpr
  calc
    D ^ ((4 / 45 : ℝ) - ε) * Real.log (D ^ (4 / 45 : ℝ)) ≤
        D ^ ((4 / 45 : ℝ) - ε) *
          ((Real.log 2 / 20) * D ^ ε) :=
          mul_le_mul_of_nonneg_left hlogY (Real.rpow_nonneg hDpos.le _)
    _ = (Real.log 2 / 20) * D ^ (4 / 45 : ℝ) := by
      calc
        D ^ ((4 / 45 : ℝ) - ε) *
            ((Real.log 2 / 20) * D ^ ε) =
            (Real.log 2 / 20) *
              (D ^ ((4 / 45 : ℝ) - ε) * D ^ ε) := by ring
        _ = (Real.log 2 / 20) *
            D ^ (((4 / 45 : ℝ) - ε) + ε) := by
              rw [← Real.rpow_add hDpos]
        _ = (Real.log 2 / 20) * D ^ (4 / 45 : ℝ) := by
              congr 1
              ring_nf
end OAI.RationalQuant
