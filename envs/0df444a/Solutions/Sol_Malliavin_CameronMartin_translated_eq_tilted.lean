-- Prove2me | solution 1 for Malliavin.CameronMartin.translated_eq_tilted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:00:47.316274+00:00
-- url     : https://prove2.me/submissions/b8b5050c-228d-46f0-a627-d8f118d4edbd

import Definitions.Def_Malliavin_CameronMartin
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Definitions.Def_Malliavin_CameronMartinTheorem
import Theorems.Thm_Malliavin_CameronMartin_integrable_exp_coe
import Theorems.Thm_Malliavin_CameronMartin_map_translated_dual
import Theorems.Thm_Malliavin_CameronMartin_map_tilted_dual
import Theorems.Thm_Malliavin_CameronMartin_apply_inclusion

section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Real Topology
noncomputable section
universe u v u_1 u_2 u_3 u_4 u_5 u_6 u_8
namespace Malliavin.CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]
private theorem measure_eq_of_forall_map_dual_eq
    {μ ν : Measure W} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hproj : ∀ L : StrongDual ℝ W, μ.map L = ν.map L) : μ = ν := by
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one, hproj L]
end Malliavin.CameronMartin
end
end

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Real Topology
noncomputable section
universe u v u_1 u_2 u_3 u_4 u_5 u_6 u_8
open Malliavin Malliavin.CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]
namespace Malliavin.CameronMartin
theorem _root_.solution (h : Space μ) :
    translated μ h = μ.tilted (fun x ↦ (h : Lp ℝ 2 μ) x) := by
  have : IsProbabilityMeasure (μ.tilted (fun x ↦ (h : Lp ℝ 2 μ) x)) :=
    isProbabilityMeasure_tilted (integrable_exp_coe μ h)
  have : IsProbabilityMeasure (translated μ h) :=
    Measure.isProbabilityMeasure_map (measurable_translate _).aemeasurable
  apply measure_eq_of_forall_map_dual_eq
  intro L
  rw [map_translated_dual, map_tilted_dual, apply_inclusion]
end Malliavin.CameronMartin
