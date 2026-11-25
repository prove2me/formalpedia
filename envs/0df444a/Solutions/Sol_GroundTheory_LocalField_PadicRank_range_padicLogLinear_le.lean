-- Prove2me | solution 1 for GroundTheory.LocalField.PadicRank.range_padicLogLinear_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:36:29.202239+00:00
-- url     : https://prove2.me/submissions/6491fa39-4379-4b03-beac-7f45204e580c

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogLinear
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_PrincipalUnitsRank
import Theorems.Thm_GroundTheory_LocalField_PadicRank_padicLog_mem_valBall_bound

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
namespace GroundTheory.LocalField.PadicRank
theorem _root_.solution : LinearMap.range (padicLogLinear K p) ≤
    valBallSubmodule K p (absRamificationIndex K + 1 -
      absRamificationIndex K * absRamificationIndex K) := by
  rintro _ ⟨u, rfl⟩
  exact padicLog_mem_valBall_bound p u
end GroundTheory.LocalField.PadicRank
