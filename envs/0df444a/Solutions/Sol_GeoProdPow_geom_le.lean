-- Prove2me | solution 1 for GeoProdPow.geom_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:52:57.91313+00:00
-- url     : https://prove2.me/submissions/07f1c297-0939-45f9-b6e7-659c9eefd116

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
theorem _root_.solution (g : ℝ) (hg : 1 < g) (r : ℕ) :
    ∑ i ∈ Ico 1 r, (g⁻¹) ^ i ≤ 1 / (g - 1) := by
  have hg0 : (0 : ℝ) < g := by linarith
  have hlt : g⁻¹ < 1 := inv_lt_one_of_one_lt₀ hg
  have h := geom_sum_Ico_le_of_lt_one (m := 1) (n := r) (inv_nonneg.2 hg0.le) hlt
  have he : g⁻¹ ^ 1 / (1 - g⁻¹) = 1 / (g - 1) := by
    have h1 : g - 1 ≠ 0 := by linarith
    field_simp
  linarith [he ▸ h]
end GeoProdPow
