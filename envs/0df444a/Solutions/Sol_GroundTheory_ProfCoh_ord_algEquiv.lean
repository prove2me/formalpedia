-- Prove2me | solution 1 for GroundTheory.ProfCoh.ord_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:40:55.042906+00:00
-- url     : https://prove2.me/submissions/b9146aff-98f2-4ecf-ad21-c3483e1c4c99

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
import Theorems.Thm_GroundTheory_LocalField_valuation_algEquiv_apply


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
variable {E F : Type u} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra E F] [ValuativeExtension E F] [FiniteDimensional E F]
namespace GroundTheory.ProfCoh
theorem _root_.solution (σ : F ≃ₐ[E] F) (x : F) : ord (σ x) = ord x := by
  rw [ord, ord, (normalizedValuation_eq_iff).mpr (valuation_algEquiv_apply E F σ x)]
end GroundTheory.ProfCoh
