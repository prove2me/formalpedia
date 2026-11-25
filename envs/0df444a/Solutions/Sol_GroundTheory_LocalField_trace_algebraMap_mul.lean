-- Prove2me | solution 1 for GroundTheory.LocalField.trace_algebraMap_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:33:47.80462+00:00
-- url     : https://prove2.me/submissions/08ccb440-45fe-4e24-a41f-040eb49ee453

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Different
import Definitions.Def_GroundTheory_LocalFields_LocalFourierExistence
import Definitions.Def_GroundTheory_LocalFields_LocalFourierTrace

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
open scoped nonZeroDivisors
attribute [local instance high] FaithfulSMul.to_isTorsionFree
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
namespace GroundTheory.LocalField
theorem _root_.solution (a : K) (x : L) :
    Algebra.trace K L (algebraMap K L a * x) = a * Algebra.trace K L x := by
  rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
end GroundTheory.LocalField
