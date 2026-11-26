-- Prove2me | solution 1 for Malliavin.ClarkOconeFamily.IsBrownianOnElementary.itoIntegral_sum_elementaryPredictable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:02:18.666719+00:00
-- url     : https://prove2.me/submissions/eb4229be-f6d2-4542-8395-cb11b2773f10

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Probability.Process.Predictable
import Definitions.Def_Malliavin_ClarkOcone

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
namespace Malliavin
namespace ClarkOconeFamily.IsBrownianOnElementary
theorem _root_.solution
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} {C : ClarkOconeFamily B P 𝓕}
    (hC : C.IsBrownianOnElementary) {ι : Type*} (s : Finset ι)
    (a b : ι → ℝ≥0) (hab : ∀ i, a i ≤ b i)
    (Z : ∀ i, lpMeas ℝ ℝ (𝓕 (a i)) 2 P) :
    C.itoIntegral (s.sum fun i ↦ elementaryPredictable 𝓕 (a i) (b i) (Z i)) =
      s.sum fun i ↦ C.elementaryIntegralValue (hab i) (Z i) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact hC (hab i) (Z i)
end ClarkOconeFamily.IsBrownianOnElementary
end Malliavin
