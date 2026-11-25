-- Prove2me | solution 1 for GroundTheory.ProfCoh.finite_quotient_range_toAdditive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:24:44.265951+00:00
-- url     : https://prove2.me/submissions/9d617a31-c23d-4d7b-8caa-cc5dd1f0ac44

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
universe u
open GroundTheory.LocalField ValuativeRel IsLocalRing
namespace GroundTheory.ProfCoh
theorem _root_.solution {G : Type*} [CommGroup G] (H : Subgroup G)
    [H.FiniteIndex] : Finite (Additive G ⧸ (H.subtype.toAdditive).range) := by
  have h : (H.subtype.toAdditive).range = H.toAddSubgroup := by
    ext x
    rw [AddMonoidHom.mem_range]
    change _ ↔ x.toMul ∈ H
    constructor
    · rintro ⟨a, rfl⟩
      exact a.toMul.2
    · intro hx
      exact ⟨Additive.ofMul ⟨x.toMul, hx⟩, rfl⟩
  rw [h]
  have : H.toAddSubgroup.FiniteIndex :=
    ⟨by rw [Subgroup.index_toAddSubgroup]; exact Subgroup.FiniteIndex.index_ne_zero⟩
  infer_instance
end GroundTheory.ProfCoh
