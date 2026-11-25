-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.isClosed_multiples
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:18:21.325829+00:00
-- url     : https://prove2.me/submissions/d34b47e5-0fad-4e4e-91b1-eaa658700adc

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Frobenius
import Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.Abstract.cosetConj_mk



set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open ProfiniteInteger
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution (N : ℕ) : IsClosed (multiples N : Set ℤ̂) := by
  have : (multiples N : Set ℤ̂) = Set.range (fun y : ℤ̂ => (N : ℤ̂) * y) := by
    ext x
    simp [multiples]
  rw [this]
  exact (isCompact_range (continuous_const.mul continuous_id)).isClosed
end GroundTheory.LocalField.Abstract
