-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.isClosed_map_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:54:13.767529+00:00
-- url     : https://prove2.me/submissions/e18fdc06-a49e-4957-919b-8a1cba2be25d

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ReciprocityMap
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_NormFormula
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Functoriality

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
variable {G : Type*} [Group G]
variable [TopologicalSpace G] [IsTopologicalGroup G]
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution {H : Subgroup G} (hH : IsClosed (H : Set G)) (σ : G) :
    IsClosed (H.map (MulAut.conj σ).toMonoidHom : Set G) := by
  rw [coe_map_conj]
  exact hH.preimage ((continuous_const.mul continuous_id).mul continuous_const)
end GroundTheory.LocalField.Abstract
