-- Prove2me | solution 1 for GroundTheory.LocalField.PadicRank.padicLog_nsmul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:02:41.099569+00:00
-- url     : https://prove2.me/submissions/0526ee45-e643-416b-b062-55e4669e5425

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogLinear
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_PrincipalUnitsRank
import Theorems.Thm_GroundTheory_LocalField_PadicRank_mem_principalFiltration_zero
import Theorems.Thm_GroundTheory_LocalField_padicLog_mem_valBall_of_mem


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
theorem _root_.solution (u : Additive (unitFiltrationUnits K 1)) :
    padicLog K (p ^ absRamificationIndex K • u) ∈ valBall K (absRamificationIndex K + 1) := by
  have := nsmul_prime_pow_mem_principalFiltration p (mem_principalFiltration_zero u)
    (absRamificationIndex K)
  rw [zero_add] at this
  exact_mod_cast padicLog_mem_valBall_of_mem p le_rfl this
end GroundTheory.LocalField.PadicRank
