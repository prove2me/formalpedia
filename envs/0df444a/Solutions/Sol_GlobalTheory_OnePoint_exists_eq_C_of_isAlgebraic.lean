-- Prove2me | solution 1 for GlobalTheory.OnePoint.exists_eq_C_of_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:45:06.532903+00:00
-- url     : https://prove2.me/submissions/b0d803b7-a15a-4d05-a469-83be6fda3185

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsIntegrallyClosedInFractionFieldPowerSeries
import Theorems.Thm_GlobalTheory_OnePoint_algebraMap_laurentSeries
import Theorems.Thm_GlobalTheory_OnePoint_isIntegrallyClosedIn_laurentSeries

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
theorem _root_.solution {x : K⸨X⸩} (hx : IsAlgebraic K x) :
    ∃ c : K, x = HahnSeries.C c := by
  obtain ⟨c, hc⟩ := (isIntegrallyClosedIn_iff.mp isIntegrallyClosedIn_laurentSeries).2
    hx.isIntegral
  exact ⟨c, by rw [← hc, algebraMap_laurentSeries]⟩
end GlobalTheory.OnePoint
