-- Prove2me | solution 1 for GlobalTheory.OnePoint.isIntegrallyClosedIn_laurentSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:30:56.812098+00:00
-- url     : https://prove2.me/submissions/12eb0ea6-3416-436b-8ae7-a8ac5d2ca8b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsIntegrallyClosedInFractionFieldPowerSeries
import Theorems.Thm_GlobalTheory_OnePoint_isIntegrallyClosedIn_fractionField_powerSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped LaurentSeries PowerSeries
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.OnePoint
universe u v w
variable {K : Type u} [Field K]
namespace GlobalTheory.OnePoint
theorem _root_.solution : IsIntegrallyClosedIn K K⸨X⸩ :=
  @isIntegrallyClosedIn_fractionField_powerSeries K _ K⸨X⸩ _ _ _ _
    (IsScalarTower.of_algebraMap_eq fun _ ↦ rfl)
end GlobalTheory.OnePoint
