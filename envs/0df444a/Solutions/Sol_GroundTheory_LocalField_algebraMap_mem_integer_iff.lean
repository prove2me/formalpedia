-- Prove2me | solution 1 for GroundTheory.LocalField.algebraMap_mem_integer_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:25.33129+00:00
-- url     : https://prove2.me/submissions/cfa00cc9-5079-4df9-9118-b9db6e548dad

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface

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
open ValuativeRel
variable (K L : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]
namespace GroundTheory.LocalField
theorem _root_.solution (x : K) : algebraMap K L x ∈ 𝒪[L] ↔ x ∈ 𝒪[K] := by
  simp only [Valuation.mem_integer_iff]
  exact Valuation.HasExtension.val_map_le_one_iff (valuation K) (valuation L) x
end GroundTheory.LocalField
