-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.tateZeroIncl_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:50:42.317051+00:00
-- url     : https://prove2.me/submissions/9c211bc8-4920-4b95-847a-a9d52a1b6b17

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Functoriality
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_FunctorialityNorm
import Theorems.Thm_GroundTheory_LocalField_Abstract_fixedModule_anti


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
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type*} [CommGroup A] [MulDistribMulAction G A]
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution {K K' L : OpenSubgroup G} (hLK' : L ≤ K') (hK'K : K' ≤ K)
    [((L : Subgroup G).subgroupOf K).Normal] (a : fixedModule A (K : Subgroup G)) :
    tateZeroIncl hLK' hK'K (QuotientGroup.mk a : tateZero A (K : Subgroup G) (L : Subgroup G)) =
      (QuotientGroup.mk ⟨(a : A), fixedModule_anti hK'K a.2⟩ : tateZero A (K' : Subgroup G) (L : Subgroup G)) :=
  rfl
end GroundTheory.LocalField.Abstract
