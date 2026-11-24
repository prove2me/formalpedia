-- Prove2me | solution 1 for GeoProdPow.one_sub_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:52:58.544148+00:00
-- url     : https://prove2.me/submissions/64a6bbe4-cd4c-494b-9a19-ca85af68e3c7

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
theorem _root_.solution (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) (i : ℕ) :
    0 ≤ 1 - x ^ i ∧ 1 - x ^ i ≤ 1 :=
  ⟨sub_nonneg.2 (pow_le_one₀ h0 h1), by linarith [pow_nonneg h0 i]⟩
end GeoProdPow
