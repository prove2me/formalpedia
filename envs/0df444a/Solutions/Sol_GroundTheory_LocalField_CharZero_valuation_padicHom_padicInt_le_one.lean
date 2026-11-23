-- Prove2me | solution 1 for GroundTheory.LocalField.CharZero.valuation_padicHom_padicInt_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:09.42901+00:00
-- url     : https://prove2.me/submissions/10edaa32-dfc5-41e2-910a-7b9facb376cb

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Examples
import Definitions.Def_GroundTheory_LocalFields_ExamplesCharZero
import Theorems.Thm_GroundTheory_LocalField_CharZero_continuous_padicHom

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
theorem _root_.solution (x : ℤ_[p]) :
    valuation K (padicHom K p (x : ℚ_[p])) ≤ 1 := by
  refine PadicInt.denseRange_intCast.induction_on x ?_ fun n => ?_
  · exact (Valuation.isClosed_integer (v := valuation K)).preimage
      ((continuous_padicHom K p).comp continuous_subtype_val)
  · simpa using valuation_intCast_le_one K n
end GroundTheory.LocalField.CharZero
