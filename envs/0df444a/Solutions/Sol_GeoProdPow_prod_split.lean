-- Prove2me | solution 1 for GeoProdPow.prod_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:06:57.117492+00:00
-- url     : https://prove2.me/submissions/8aeea5a4-f96b-4aae-ac3c-53424b198ee6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GeometricProductPowers_GaussianProductPowerBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeometricProductBound_OneSubSumLeProd
import Theorems.Thm_GeoProdPow_factor
import Theorems.Thm_GeoProdPow_gauss

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GeoProdPow
open Finset
namespace GeoProdPow
theorem _root_.solution (g0 g1 : ℝ) (h0 : 0 < g0) (h1 : 0 < g1) (r : ℕ) :
    ∏ i ∈ Ico 1 r, ((g0 ^ i - 1) * (g1 ^ i - 1)) =
      (g0 * g1) ^ (r * (r - 1) / 2) *
        ∏ i ∈ Ico 1 r, ((1 - (g0⁻¹) ^ i) * (1 - (g1⁻¹) ^ i)) := by
  have e : ∀ i, (g0 ^ i - 1) * (g1 ^ i - 1) =
      (g0 * g1) ^ i * ((1 - (g0⁻¹) ^ i) * (1 - (g1⁻¹) ^ i)) := by
    intro i
    rw [factor g0 h0 i, factor g1 h1 i, mul_pow]
    ring
  have hp := Finset.prod_pow_eq_pow_sum (Ico 1 r) (fun i => i) (g0 * g1)
  rw [Finset.prod_congr rfl (fun i _ => e i), Finset.prod_mul_distrib, hp, gauss]
end GeoProdPow
