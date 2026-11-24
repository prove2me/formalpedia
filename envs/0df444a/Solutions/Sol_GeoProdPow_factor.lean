-- Prove2me | solution 1 for GeoProdPow.factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:51:26.395062+00:00
-- url     : https://prove2.me/submissions/c9360e9d-b5e4-4648-ba1d-c1206320b467

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GeometricProductPowers_GaussianProductPowerBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeometricProductBound_OneSubSumLeProd

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
theorem _root_.solution (g : ℝ) (hg : 0 < g) (i : ℕ) : g ^ i - 1 = g ^ i * (1 - (g⁻¹) ^ i) := by
  rw [inv_pow, mul_sub, mul_one, mul_inv_cancel₀ (pow_ne_zero _ hg.ne')]
end GeoProdPow
