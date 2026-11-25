-- Prove2me | solution 1 for GroundTheory.LocalField.padicHom_padicInt_mem_valBall_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:56:47.923809+00:00
-- url     : https://prove2.me/submissions/f8b526ec-3872-4213-872a-8078c7ce993b

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PrincipalUnitsModule
import Definitions.Def_GroundTheory_LocalFields_PadicLogLinear
import Theorems.Thm_GroundTheory_LocalField_CharZero_valuation_padicHom_padicInt_le_one
import Theorems.Thm_GroundTheory_LocalField_mem_valBall


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
theorem _root_.solution (t : ℤ_[p]) :
    CharZero.padicHom K p (t : ℚ_[p]) ∈ valBall K 0 := by
  rw [mem_valBall, neg_zero, WithZero.exp_zero, ← map_one (normalizedValuation K),
    normalizedValuation_le_iff, map_one]
  exact CharZero.valuation_padicHom_padicInt_le_one K p t
end GroundTheory.LocalField
