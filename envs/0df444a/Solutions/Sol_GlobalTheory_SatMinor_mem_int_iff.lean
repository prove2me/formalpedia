-- Prove2me | solution 1 for GlobalTheory.SatMinor.mem_int_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:32:44.772807+00:00
-- url     : https://prove2.me/submissions/a339eebb-8a40-44f3-96d9-9d485ad5530a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitMinorOfIntegralMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.SatMinor
variable {p : ℕ} [Fact p.Prime]
namespace GlobalTheory.SatMinor
theorem _root_.solution (x : ℂ_[p]) : x ∈ PadicComplexInt p ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplex.norm_eq_norm]
  unfold PadicComplexInt
  rw [Valuation.mem_valuationSubring_iff]
  simp [Valuation.norm_def]
end GlobalTheory.SatMinor
