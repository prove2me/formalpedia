-- Prove2me | solution 1 for GroundTheory.ProfCoh.ordHom_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:25:24.22575+00:00
-- url     : https://prove2.me/submissions/e4e9538c-cd11-4f8f-9d85-35851ba4b57e

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
import Theorems.Thm_GroundTheory_ProfCoh_ordHom_apply
import Theorems.Thm_GroundTheory_LocalField_unitsEquivIntProd_fst


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
variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {F}
namespace GroundTheory.ProfCoh
theorem _root_.solution : Function.Surjective (ordHom F) := by
  intro m
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  refine ⟨Additive.ofMul ((unitsEquivIntProd hϖ).symm (Multiplicative.ofAdd m.down, 1)), ?_⟩
  apply ULift.ext
  have := unitsEquivIntProd_fst hϖ ((unitsEquivIntProd hϖ).symm (Multiplicative.ofAdd m.down, 1))
  rw [MulEquiv.apply_symm_apply] at this
  rw [ordHom_apply]
  exact (Multiplicative.ofAdd.injective this).symm
end GroundTheory.ProfCoh
