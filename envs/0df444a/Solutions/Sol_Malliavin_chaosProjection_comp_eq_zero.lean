-- Prove2me | solution 1 for Malliavin.chaosProjection_comp_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:08:14.859802+00:00
-- url     : https://prove2.me/submissions/1a212c62-92f6-4611-8d1d-2c3f9456bd6e

import Definitions.Def_Malliavin_MultipleIntegral
import Definitions.Def_Malliavin_WienerChaos

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Topology symmDiff
noncomputable section
open Malliavin
universe u v u_1 u_2 u_4 u_6
universe u₁ u₂ u₃
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P) {m n : ℕ}
    (hmn : m ≠ n) :
    chaosProjection hB m ∘L chaosProjection hB n = 0 := by
  change
    (homogeneousChaos hB m : Submodule ℝ (RandomL2 P)).starProjection ∘L
      (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)).starProjection = 0
  rw [Submodule.starProjection_comp_starProjection_eq_zero_iff]
  exact homogeneousChaos_isOrtho hB hmn
end Malliavin
