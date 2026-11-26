-- Prove2me | solution 1 for Malliavin.brownianLp_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:54:41.440715+00:00
-- url     : https://prove2.me/submissions/19d8abd4-3be1-4c54-a07c-023bdab84a7d

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
theorem _root_.solution (hB : IsPreBrownianReal B P) : brownianLp hB 0 = 0 := by
  apply Lp.ext
  filter_upwards [coeFn_brownianLp hB 0, hB.eval_zero_ae_eq_zero, Lp.coeFn_zero ℝ 2 P]
    with ω h1 h2 h3
  rw [h1, h2, h3, Pi.zero_apply]
end Malliavin
