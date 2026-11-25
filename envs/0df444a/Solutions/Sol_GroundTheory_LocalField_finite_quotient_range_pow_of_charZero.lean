-- Prove2me | solution 1 for GroundTheory.LocalField.finite_quotient_range_pow_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:19:46.758075+00:00
-- url     : https://prove2.me/submissions/7d78cdf0-9bf2-4520-adf7-af11d548b09a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsRootOfAdicComplete
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Theorems.Thm_GroundTheory_LocalField_finite_quotient_range_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Polynomial
open scoped WithZero
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {K}
namespace GroundTheory.LocalField
theorem _root_.solution [CharZero K] {m : ℕ} (hm : m ≠ 0) :
    Finite (Kˣ ⧸ (powMonoidHom m : Kˣ →* Kˣ).range) :=
  finite_quotient_range_pow (Nat.cast_ne_zero.mpr hm)
end GroundTheory.LocalField
