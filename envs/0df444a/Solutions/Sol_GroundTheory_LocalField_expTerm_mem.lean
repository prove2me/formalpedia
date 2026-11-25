-- Prove2me | solution 1 for GroundTheory.LocalField.expTerm_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:46:21.989729+00:00
-- url     : https://prove2.me/submissions/b3291874-6cbb-418d-904c-60e3f7e9ccf0

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExamplesCharZero
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Theorems.Thm_GroundTheory_LocalField_pow_mem_valBall
import Theorems.Thm_GroundTheory_LocalField_div_natCast_mem_valBall

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
theorem _root_.solution {a : ℤ} {x : K} (hx : x ∈ valBall K a) (k : ℕ) :
    x ^ k / (k.factorial : K) ∈
      valBall K (k * a - absRamificationIndex K * padicValNat p k.factorial) :=
  div_natCast_mem_valBall p (pow_mem_valBall hx k) (Nat.factorial_ne_zero k)
end GroundTheory.LocalField
