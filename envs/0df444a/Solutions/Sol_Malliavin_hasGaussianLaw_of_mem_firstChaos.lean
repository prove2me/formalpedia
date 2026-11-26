-- Prove2me | solution 1 for Malliavin.hasGaussianLaw_of_mem_firstChaos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:59:57.365362+00:00
-- url     : https://prove2.me/submissions/8ef06bf4-8713-4a6b-bbc9-249e1d033a1a

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
import Theorems.Thm_Malliavin_hasGaussianLaw_wienerIntegral
import Theorems.Thm_Malliavin_range_wienerIntegral

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P) {Z : RandomL2 P}
    (hZ : Z ∈ firstChaos hB) : HasGaussianLaw (Z : Ω → ℝ) P := by
  rw [← range_wienerIntegral] at hZ
  obtain ⟨f, rfl⟩ := hZ
  rw [ContinuousLinearMap.coe_coe]
  exact hasGaussianLaw_wienerIntegral hB f
end Malliavin
