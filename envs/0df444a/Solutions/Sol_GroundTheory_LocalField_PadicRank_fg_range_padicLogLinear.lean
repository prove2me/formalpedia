-- Prove2me | solution 1 for GroundTheory.LocalField.PadicRank.fg_range_padicLogLinear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:42:44.310894+00:00
-- url     : https://prove2.me/submissions/8cffe4bb-2866-4c0c-93db-235d9cf2f7fa

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogLinear
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_PrincipalUnitsRank
import Theorems.Thm_GroundTheory_LocalField_PadicRank_finite_and_finrank_valBallSubmodule
import Theorems.Thm_GroundTheory_LocalField_PadicRank_range_padicLogLinear_le

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
theorem _root_.solution : (LinearMap.range (padicLogLinear K p)).FG := by
  set c : ℤ := absRamificationIndex K + 1 - absRamificationIndex K * absRamificationIndex K
  have : Module.Finite ℤ_[p] (valBallSubmodule K p c) :=
    (finite_and_finrank_valBallSubmodule (K := K) p c).1
  have : IsNoetherian ℤ_[p] (valBallSubmodule K p c) := inferInstance
  have : IsNoetherian ℤ_[p] (LinearMap.range (padicLogLinear K p)) :=
    isNoetherian_of_le (range_padicLogLinear_le p)
  exact (Submodule.fg_top _).mp (IsNoetherian.noetherian ⊤)
end GroundTheory.LocalField.PadicRank
