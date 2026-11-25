-- Prove2me | solution 1 for GroundTheory.LocalField.PadicRank.valBallSubmodule_le_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:01:29.732138+00:00
-- url     : https://prove2.me/submissions/2ce317fa-6acf-4961-bc04-f7b2ad9c472e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogLinear
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_PrincipalUnitsRank
import Theorems.Thm_GroundTheory_LocalField_PadicRank_lt_sub_one_mul_succ
import Theorems.Thm_GroundTheory_LocalField_unitFiltrationUnits_antitone


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
theorem _root_.solution : valBallSubmodule K p ((absRamificationIndex K + 1 : ℕ) : ℤ) ≤
    LinearMap.range (padicLogLinear K p) := by
  intro y hy
  set n := absRamificationIndex K + 1
  have hn := lt_sub_one_mul_succ (K := K) p
  set w := (logValBallEquiv p n hn).symm ⟨y, hy⟩
  have h1 : 1 ≤ n := by omega
  refine ⟨Additive.ofMul ⟨((Additive.toMul w : unitFiltrationUnits K n) : Kˣ),
    unitFiltrationUnits_antitone h1 (Additive.toMul w).2⟩, ?_⟩
  have := congrArg Subtype.val ((logValBallEquiv p n hn).apply_symm_apply ⟨y, hy⟩)
  exact this
end GroundTheory.LocalField.PadicRank
