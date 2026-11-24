-- Prove2me | solution 1 for GlobalTheory.UnitarySwap.inv_one_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:12:56.587607+00:00
-- url     : https://prove2.me/submissions/f49f8080-d436-48ba-af6c-9c83957e6093

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ImportsTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Theorems.Thm_GlobalTheory_UnitarySwap_mem_int
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix
noncomputable section
open GlobalTheory GlobalTheory.UnitarySwap
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.UnitarySwap
theorem _root_.solution {x : L} (hx : Valued.v x < 1) : (1 - x) ≠ 0 ∧ (1 - x)⁻¹ ∈ intL L := by
  have h : Valued.v (1 - x) = 1 := Valuation.map_one_sub_of_lt _ hx
  refine ⟨fun h0 => ?_, ?_⟩
  · rw [h0, map_zero] at h; exact zero_ne_one h
  · rw [mem_int, map_inv₀, h, inv_one]
end GlobalTheory.UnitarySwap
