-- Prove2me | solution 1 for GroundTheory.LocalField.PadicRank.lt_sub_one_mul_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:47:53.631007+00:00
-- url     : https://prove2.me/submissions/4bb4034a-9702-446a-98a5-c076e2cfe4b5

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogLinear
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_PrincipalUnitsRank

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
open GroundTheory.LocalField.PadicRank
variable (p : ℕ) [hp : Fact p.Prime]
variable [CharP 𝓀[K] p] [CharZero K]
attribute [local instance] algebraK algebraInteger
omit [CharP 𝓀[K] p] [CharZero K]
namespace GroundTheory.LocalField.PadicRank
theorem _root_.solution : (absRamificationIndex K : ℤ) <
    (p - 1 : ℤ) * ((absRamificationIndex K + 1 : ℕ) : ℤ) := by
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
  push_cast
  nlinarith
end GroundTheory.LocalField.PadicRank
