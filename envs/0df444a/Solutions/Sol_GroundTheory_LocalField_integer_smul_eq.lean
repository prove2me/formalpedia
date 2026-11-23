-- Prove2me | solution 1 for GroundTheory.LocalField.integer_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:37.817953+00:00
-- url     : https://prove2.me/submissions/5116cee3-d657-4ca4-b447-55ad2730187c

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_NormalLattice

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
open ValuativeRel Finset
variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [Algebra K L]
namespace GroundTheory.LocalField
theorem _root_.solution (c : 𝒪[K]) (y : L) : c • y = algebraMap K L (c : K) * y := by
  rw [← Algebra.smul_def]
  rfl
end GroundTheory.LocalField
