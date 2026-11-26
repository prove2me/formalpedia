-- Prove2me | solution 1 for Malliavin.CameronMartin.denseRange_ofDual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:46:54.992863+00:00
-- url     : https://prove2.me/submissions/e625dd8b-28ef-417d-96b3-8d2722a98456

import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Moments.CovarianceBilinDual
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_CameronMartin

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real Topology
universe u v u_1 u_2 u_3 u_4 u_5 u_6 u_7
open Malliavin
open Malliavin.CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]
omit [CompleteSpace W] [SecondCountableTopology W]
namespace Malliavin.CameronMartin
theorem _root_.solution : DenseRange (ofDual μ) := by
  rw [DenseRange, Subtype.dense_iff]
  intro f hf
  have h_image :
      ((↑) '' Set.range (ofDual μ) : Set (Lp ℝ 2 μ)) =
        Set.range (centeredDualToLp μ) := by
    ext g
    constructor
    · rintro ⟨_, ⟨L, rfl⟩, rfl⟩
      exact ⟨L, rfl⟩
    · rintro ⟨L, rfl⟩
      exact ⟨ofDual μ L, ⟨L, rfl⟩, rfl⟩
  have hf' : f ∈ closure (Set.range (centeredDualToLp μ)) := hf
  exact h_image.symm ▸ hf'
end Malliavin.CameronMartin
