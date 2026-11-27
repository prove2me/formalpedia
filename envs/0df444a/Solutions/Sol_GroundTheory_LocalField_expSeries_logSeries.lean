-- Prove2me | solution 1 for GroundTheory.LocalField.expSeries_logSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:47:41.992836+00:00
-- url     : https://prove2.me/submissions/ba1c9eea-1421-4f02-a82c-8482216f7cce

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogHom
import Definitions.Def_GroundTheory_LocalFields_PadicExp

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
open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]
namespace GroundTheory.LocalField
theorem _root_.solution {n : ℕ} (hn : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * n)
    (u : unitFiltrationUnits K n) :
    expSeries (logSeries (((u : Kˣ) : K) - 1)) = ((u : Kˣ) : K) := by
  have := congrArg (fun v ↦ (((Additive.toMul v : unitFiltrationUnits K n) : Kˣ) : K))
    ((logValBallEquiv p n hn).symm_apply_apply (Additive.ofMul u))
  exact this
end GroundTheory.LocalField
