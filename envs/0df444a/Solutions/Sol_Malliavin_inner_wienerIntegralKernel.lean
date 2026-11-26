-- Prove2me | solution 1 for Malliavin.inner_wienerIntegralKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:59:44.259336+00:00
-- url     : https://prove2.me/submissions/ee136c8e-0320-428e-961c-8035573b0ead

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
import Theorems.Thm_Malliavin_wienerIntegralKernel_apply
import Theorems.Thm_Malliavin_simplex_one

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P) (f g : IteratedKernel 1) :
    ⟪wienerIntegralKernel hB f, wienerIntegralKernel hB g⟫_ℝ =
      ∫ t in simplex ℝ≥0 1, ⟪f t, g t⟫_ℝ ∂iteratedKernelMeasure 1 := by
  rw [simplex_one, Measure.restrict_univ, ← L2.inner_def, wienerIntegralKernel_apply,
    wienerIntegralKernel_apply, inner_wienerIntegral, LinearIsometry.inner_map_map]
end Malliavin
