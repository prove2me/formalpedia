-- Prove2me | solution 1 for GroundTheory.ProfCoh.ordHom_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:50:17.931991+00:00
-- url     : https://prove2.me/submissions/52664864-4f68-49ff-8914-f9bc9b4075c2

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
import Theorems.Thm_GroundTheory_ProfCoh_ordHom_apply
import Theorems.Thm_GroundTheory_ProfCoh_ord_algEquiv

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
theorem _root_.solution (σ : F ≃ₐ[E] F) (x : Additive Fˣ) : ordHom F (σ • x) = ordHom F x := by
  rw [ordHom_apply, ordHom_apply]
  exact congrArg ULift.up (ord_algEquiv σ ((x.toMul : Fˣ) : F))
end GroundTheory.ProfCoh
