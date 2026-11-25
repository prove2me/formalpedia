-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.tateZeroConj_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:59:30.273319+00:00
-- url     : https://prove2.me/submissions/db3119bb-5443-44c2-9166-6e9be91976e0

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
theorem _root_.solution (σ : G) (K L : OpenSubgroup G) (a : fixedModule A (K : Subgroup G)) :
    tateZeroConj σ K L (QuotientGroup.mk a : tateZero A (K : Subgroup G) (L : Subgroup G)) =
      (QuotientGroup.mk (conjFixed σ K a) : tateZero A _ _) :=
  rfl
end GroundTheory.LocalField.Abstract
