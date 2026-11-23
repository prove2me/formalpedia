-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ProfiniteInteger.continuous_proj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:37.386824+00:00
-- url     : https://prove2.me/submissions/45ca5fdb-09e0-4494-bac6-0f7cf0577f05

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger

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
theorem _root_.solution (n : ℕ+) : Continuous (proj n) :=
  (continuous_apply n).comp continuous_subtype_val
end GroundTheory.LocalField.Abstract.ProfiniteInteger
