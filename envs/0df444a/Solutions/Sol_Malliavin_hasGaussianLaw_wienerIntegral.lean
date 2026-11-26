-- Prove2me | solution 1 for Malliavin.hasGaussianLaw_wienerIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:04:08.879896+00:00
-- url     : https://prove2.me/submissions/30c5aeec-4aea-463f-b981-cc194752a3d0

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
import Theorems.Thm_Malliavin_integral_wienerIntegral
import Theorems.Thm_Malliavin_hasGaussianLaw_stepToRandom
import Theorems.Thm_Malliavin_CameronMartin_hasGaussianLaw_L2_limit_of_centered


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
open CameronMartin
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    HasGaussianLaw (wienerIntegral hB f : Ω → ℝ) P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨x, hx, hlim⟩ := mem_closure_iff_seq_limit.mp (denseRange_stepToLp f)
  choose v hv using hx
  have hlim' : Tendsto (fun n ↦ wienerIntegral hB (x n)) atTop (𝓝 (wienerIntegral hB f)) :=
    ((wienerIntegral hB).continuous.tendsto f).comp hlim
  refine hasGaussianLaw_L2_limit_of_centered P hlim' (fun n ↦ ?_) (fun n ↦ ?_)
  · rw [← hv n, wienerIntegral_stepToLp]
    exact hasGaussianLaw_stepToRandom hB (v n)
  · exact integral_wienerIntegral hB _
end Malliavin
