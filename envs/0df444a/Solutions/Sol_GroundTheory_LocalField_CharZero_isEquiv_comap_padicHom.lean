-- Prove2me | solution 1 for GroundTheory.LocalField.CharZero.isEquiv_comap_padicHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:18:11.89547+00:00
-- url     : https://prove2.me/submissions/7d9f6a5b-84a6-48e4-b3fb-6fd087b3ce50

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Examples
import Definitions.Def_GroundTheory_LocalFields_ExamplesCharZero
import Theorems.Thm_GroundTheory_LocalField_CharZero_valuation_padicHom_le_one_iff

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
open ValuativeRel WithZero Topology
open GroundTheory.LocalField.CharZero
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (p : ℕ) [CharP 𝓀[K] p]
variable [Fact p.Prime]
variable [CharZero K]
namespace GroundTheory.LocalField.CharZero
theorem _root_.solution :
    ((valuation K).comap (padicHom K p)).IsEquiv Padic.mulValuation :=
  Valuation.isEquiv_of_val_le_one fun x => by
    rw [Valuation.comap_apply, valuation_padicHom_le_one_iff]
    simpa using (GroundTheory.LocalField.Padic.mulValuation_le_iff_norm_le p x 1).symm
end GroundTheory.LocalField.CharZero
