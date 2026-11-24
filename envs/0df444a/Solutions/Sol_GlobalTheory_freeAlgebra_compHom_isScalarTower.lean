-- Prove2me | solution 1 for GlobalTheory.freeAlgebra_compHom_isScalarTower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:59:05.5365+00:00
-- url     : https://prove2.me/submissions/86611014-acc2-4c21-a839-ab54cec55904

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CancelArtinianNoetherianSummandStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EndomorphismFamilyDirectSummandCancellation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {k ι W : Type} [Field k] [AddCommGroup W] [Module k W]
    (φ : FreeAlgebra k ι →ₐ[k] Module.End k W) :
    @IsScalarTower k (FreeAlgebra k ι) W _ (Module.compHom W φ.toRingHom).toSMul _ := by
  letI : Module (FreeAlgebra k ι) W := Module.compHom W φ.toRingHom
  refine ⟨fun c r w => ?_⟩
  show φ (c • r) w = c • φ r w
  rw [map_smul]
  rfl
end GlobalTheory
