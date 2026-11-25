-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.galRestrict_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:59:14.703027+00:00
-- url     : https://prove2.me/submissions/c73188f3-d62d-484c-8dcf-0263e9d61d71

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
omit [IsTopologicalGroup G] [CompactSpace G]
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution {K L K' L' : OpenSubgroup G} [((L : Subgroup G).subgroupOf K).Normal]
    [((L' : Subgroup G).subgroupOf K').Normal] (hK : K' ≤ K) (hL : L' ≤ L) (τ : (K' : Subgroup G)) :
    galRestrict hK hL (τ : (K' : Subgroup G) ⧸ (L' : Subgroup G).subgroupOf K') =
      ((⟨τ, hK τ.2⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :=
  rfl
end GroundTheory.LocalField.Abstract
