-- Prove2me | solution 1 for GroundTheory.LocalField.padicLog_mem_valBall_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:57:46.436511+00:00
-- url     : https://prove2.me/submissions/c70dd0e2-f986-410e-8e60-99d2dfa23197

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PrincipalUnitsModule
import Definitions.Def_GroundTheory_LocalFields_PadicLogLinear
import Theorems.Thm_GroundTheory_LocalField_logSeries_mem_valBall
import Theorems.Thm_GroundTheory_LocalField_padicLog_apply


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
include p
namespace GroundTheory.LocalField
theorem _root_.solution {k : ℕ} (hk : absRamificationIndex K ≤ k)
    {w : Additive (unitFiltrationUnits K 1)} (hw : w ∈ principalFiltration K k) :
    padicLog K w ∈ valBall K (k + 1) := by
  rw [mem_principalFiltration] at hw
  rw [padicLog_apply]
  refine logSeries_mem_valBall p hw ?_
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
  have : (absRamificationIndex K : ℤ) ≤ k := by exact_mod_cast hk
  nlinarith
end GroundTheory.LocalField
