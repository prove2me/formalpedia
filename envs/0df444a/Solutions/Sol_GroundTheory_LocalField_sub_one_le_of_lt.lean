-- Prove2me | solution 1 for GroundTheory.LocalField.sub_one_le_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:29:32.460867+00:00
-- url     : https://prove2.me/submissions/842136f9-9778-4e73-aae7-65d35a7adfbe

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Definitions.Def_GroundTheory_LocalFields_PadicLogHom

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
omit [CharP 𝓀[K] p] [CharZero K]
namespace GroundTheory.LocalField
theorem _root_.solution {a : ℤ} (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a) {b : ℤ}
    (hab : a ≤ b) : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * b := by
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
  nlinarith
end GroundTheory.LocalField
