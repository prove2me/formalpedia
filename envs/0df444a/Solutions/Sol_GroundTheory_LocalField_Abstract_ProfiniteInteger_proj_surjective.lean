-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ProfiniteInteger.proj_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:10:45.143885+00:00
-- url     : https://prove2.me/submissions/e6bfe8fc-bace-4f75-aee9-be38b22749c7

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero

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
theorem _root_.solution (n : ℕ+) : Function.Surjective (proj n) := fun z =>
  ⟨((z.val : ℕ) : ℤ̂), by rw [map_natCast, ZMod.natCast_zmod_val]⟩
end GroundTheory.LocalField.Abstract.ProfiniteInteger
