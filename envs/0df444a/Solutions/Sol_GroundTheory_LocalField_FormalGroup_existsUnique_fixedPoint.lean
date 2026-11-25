-- Prove2me | solution 1 for GroundTheory.LocalField.FormalGroup.existsUnique_fixedPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:32:21.999517+00:00
-- url     : https://prove2.me/submissions/900746c0-45e2-45c7-b719-3457a6476270

import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Ydb5_existsUnique_fixedPoint__f2868b5b329d
import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsUniqueFixedPoint
import Definitions.Def_GroundTheory_LocalFields_FormalGroups_Truncation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open MvPowerSeries
variable {σ R : Type*} [CommRing R]
namespace GroundTheory.LocalField.FormalGroup
theorem _root_.solution (Φ : MvPowerSeries σ R → MvPowerSeries σ R)
    (hΦ : ∀ f g : MvPowerSeries σ R, ∀ n : ℕ, (n : ℕ∞) ≤ order (f - g) →
      ((n + 1 : ℕ) : ℕ∞) ≤ order (Φ f - Φ g)) :
    ∃! f, Φ f = f :=
  _root_.P2M_UpperTheory_Reformulated_B_Ydb5_existsUnique_fixedPoint__f2868b5b329d Φ hΦ
end GroundTheory.LocalField.FormalGroup
