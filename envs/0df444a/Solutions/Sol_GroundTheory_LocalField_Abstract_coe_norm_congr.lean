-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.coe_norm_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:44.831659+00:00
-- url     : https://prove2.me/submissions/d3791948-0086-4d33-a6ae-993111de1eef

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_NormFormula

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
variable {G : Type*} [Group G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution {K K' L L' : Subgroup G} (hK : K = K') (hL : L = L')
    [(L.subgroupOf K).FiniteIndex] [(L'.subgroupOf K').FiniteIndex] (a : fixedModule A L) :
    (norm A K L a : A) = norm A K' L' ⟨a, hL ▸ a.2⟩ := by
  subst hK
  subst hL
  rfl
end GroundTheory.LocalField.Abstract
