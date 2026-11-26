-- Prove2me | solution 1 for Malliavin.CameronMartin.map_tilted_dual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:59:59.444936+00:00
-- url     : https://prove2.me/submissions/94d9d00c-f5d5-45ab-9f90-dedcc7391f96

import Definitions.Def_Malliavin_CameronMartin
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Definitions.Def_Malliavin_CameronMartinTheorem
import Theorems.Thm_Malliavin_CameronMartin_integrable_exp_coe
import Theorems.Thm_Malliavin_CameronMartin_mgf_tilted_dual
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply


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
private theorem map_eq_gaussianReal_of_mgf_eq
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsFiniteMeasure ν]
    {X : Ω → ℝ} (hX : AEMeasurable X ν) (m : ℝ) (v : ℝ≥0)
    (hmgf : mgf X ν = mgf id (gaussianReal m v)) :
    ν.map X = gaussianReal m v := by
  have heqOn := eqOn_complexMGF_of_mgf hmgf.symm
  have hcomplex : complexMGF id (gaussianReal m v) = complexMGF X ν := by
    funext z
    apply heqOn
    simp only [integrableExpSet_id_gaussianReal, interior_univ, Set.mem_univ, Set.ofPred_true]
  have hmap := Measure.ext_of_complexMGF_eq aemeasurable_id hX hcomplex
  simpa only [Measure.map_id] using hmap.symm
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
theorem _root_.solution (h : Space μ) (L : StrongDual ℝ W) :
    (μ.tilted (fun x ↦ (h : Lp ℝ 2 μ) x)).map L =
      gaussianReal (L (mean μ) + @inner ℝ _ _ (ofDual μ L) h) (‖ofDual μ L‖₊ ^ 2) := by
  have : IsProbabilityMeasure (μ.tilted (fun x ↦ (h : Lp ℝ 2 μ) x)) :=
    isProbabilityMeasure_tilted (integrable_exp_coe μ h)
  apply map_eq_gaussianReal_of_mgf_eq L.continuous.measurable.aemeasurable
  funext t
  rw [mgf_tilted_dual, mgf_gaussianReal Measure.map_id t]
end Malliavin.CameronMartin
