-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ProfiniteInteger.ker_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:28:26.649156+00:00
-- url     : https://prove2.me/submissions/b5234810-f192-47eb-a481-90ac302f3c2b

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_proj_eq_zero_iff

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
open GroundTheory.LocalField.Abstract.ProfiniteInteger
namespace GroundTheory.LocalField.Abstract.ProfiniteInteger
theorem _root_.solution (n : ℕ+) : (proj n).toAddMonoidHom.ker = multiples n := by
  ext x
  exact proj_eq_zero_iff
end GroundTheory.LocalField.Abstract.ProfiniteInteger
