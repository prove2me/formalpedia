-- Prove2me | solution 1 for GroundTheory.LocalField.mem_integer_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:12.328779+00:00
-- url     : https://prove2.me/submissions/51336008-37ed-4199-8117-962c778cdc0b

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Polynomial
variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
omit [TopologicalSpace L] [IsNonarchimedeanLocalField L]
namespace GroundTheory.LocalField
theorem _root_.solution {m : ℕ} (hm : m ≠ 0) {x : L} (hx : x ^ m = 1) : x ∈ 𝒪[L] := by
  rw [Valuation.mem_integer_iff]
  have h : valuation L x ^ m = 1 := by rw [← map_pow, hx, map_one]
  refine le_of_not_gt fun h1 ↦ ?_
  have := one_lt_pow₀ h1 hm
  rw [h] at this
  exact this.false
end GroundTheory.LocalField
