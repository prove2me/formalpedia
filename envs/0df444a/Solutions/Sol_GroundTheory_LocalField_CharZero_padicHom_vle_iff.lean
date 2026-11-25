-- Prove2me | solution 1 for GroundTheory.LocalField.CharZero.padicHom_vle_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:29:28.710597+00:00
-- url     : https://prove2.me/submissions/2ffb452f-3089-47e0-b769-3e777ef57b67

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Examples
import Definitions.Def_GroundTheory_LocalFields_ExamplesCharZero
import Theorems.Thm_GroundTheory_LocalField_CharZero_isEquiv_comap_padicHom

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
theorem _root_.solution (a b : ℚ_[p]) : padicHom K p a ≤ᵥ padicHom K p b ↔ a ≤ᵥ b := by
  rw [Valuation.Compatible.vle_iff_le (v := valuation K),
    Valuation.Compatible.vle_iff_le (v := Padic.mulValuation)]
  simpa using (isEquiv_comap_padicHom K p).le_iff_le (x := a) (y := b)
end GroundTheory.LocalField.CharZero
