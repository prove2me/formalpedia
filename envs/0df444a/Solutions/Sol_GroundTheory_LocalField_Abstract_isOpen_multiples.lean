-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.isOpen_multiples
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:25:01.097357+00:00
-- url     : https://prove2.me/submissions/78721b06-d702-46d1-b6c3-2115b3588351

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Frobenius
import Theorems.Thm_GroundTheory_LocalField_Abstract_isClosed_multiples

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open ProfiniteInteger
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution (N : ℕ+) : IsOpen (multiples N : Set ℤ̂) :=
  AddSubgroup.isOpen_of_isClosed_of_finiteIndex _ (isClosed_multiples N)
end GroundTheory.LocalField.Abstract
