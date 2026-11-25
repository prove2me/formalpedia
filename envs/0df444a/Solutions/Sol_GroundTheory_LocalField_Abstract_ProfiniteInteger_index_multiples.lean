-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ProfiniteInteger.index_multiples
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:35:13.584573+00:00
-- url     : https://prove2.me/submissions/828fd5a8-335e-414d-86e0-e3a3d5b40803

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_proj_surjective
import Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_ker_proj

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
theorem _root_.solution (n : ℕ+) : (multiples n).index = n := by
  rw [← ker_proj, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 (proj_surjective n)]
  simp
end GroundTheory.LocalField.Abstract.ProfiniteInteger
