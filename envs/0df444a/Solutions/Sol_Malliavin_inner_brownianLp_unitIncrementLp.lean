-- Prove2me | solution 1 for Malliavin.inner_brownianLp_unitIncrementLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:03:20.35254+00:00
-- url     : https://prove2.me/submissions/13457edb-5b12-4b0b-997e-3b88da7e6e67

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P) (t : ℝ≥0) (k : ℕ) :
    ⟪brownianLp hB t, unitIncrementLp hB k⟫_ℝ = min (t : ℝ) (k + 1) - min (t : ℝ) k := by
  unfold unitIncrementLp
  rw [inner_sub_right, inner_brownianLp, inner_brownianLp]
  push_cast
  ring
end Malliavin
