-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.cosetConj_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:26:45.180371+00:00
-- url     : https://prove2.me/submissions/dafb9d83-7c9b-436c-8ed0-d0e42f5b1fef

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf

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
variable {K L : Subgroup G}
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution (σ : G) (τ : K) :
    cosetConj (L := L) σ (τ : K ⧸ L.subgroupOf K) =
      ((⟨σ * τ * σ⁻¹, τ, τ.2, rfl⟩ : K.map (MulAut.conj σ).toMonoidHom) : _ ⧸ _) :=
  rfl
end GroundTheory.LocalField.Abstract
