-- Prove2me | solution 1 for GroundTheory.LocalField.traceChar_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:33:42.507695+00:00
-- url     : https://prove2.me/submissions/cf92dca6-2a04-4b06-8543-59f03a61ee27

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
theorem _root_.solution (ψ : AddChar K Circle) (x : L) :
    traceChar L ψ x = ψ (Algebra.trace K L x) := rfl
end GroundTheory.LocalField
