-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.galConj_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:44:00.648358+00:00
-- url     : https://prove2.me/submissions/1dbacf5e-cd86-4bc2-8fa5-e2ea63f5c5a7

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
omit [CompactSpace G]
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution (σ : G) (K L : OpenSubgroup G) [((L : Subgroup G).subgroupOf K).Normal]
    (τ : (K : Subgroup G)) :
    galConj σ K L (τ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
      ((⟨σ * τ * σ⁻¹, τ, τ.2, rfl⟩ : ((conjOpen σ K : OpenSubgroup G) : Subgroup G)) : _ ⧸ _) :=
  rfl
end GroundTheory.LocalField.Abstract
