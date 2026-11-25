-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.normTateZero_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:56:45.239305+00:00
-- url     : https://prove2.me/submissions/e0d62f68-265d-4fb9-85cd-5efbc48f89f3

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
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type*} [CommGroup A] [MulDistribMulAction G A]
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution {K L K' L' : OpenSubgroup G} (hK : K' ≤ K) (hL : L' ≤ L)
    (hL'K' : L' ≤ K') (hLK : L ≤ K) (a : fixedModule A (K' : Subgroup G)) :
    normTateZero hK hL hL'K' hLK (QuotientGroup.mk a : tateZero A (K' : Subgroup G) (L' : Subgroup G)) =
      (QuotientGroup.mk (norm A (K : Subgroup G) (K' : Subgroup G) a) :
        tateZero A (K : Subgroup G) (L : Subgroup G)) :=
  rfl
end GroundTheory.LocalField.Abstract
