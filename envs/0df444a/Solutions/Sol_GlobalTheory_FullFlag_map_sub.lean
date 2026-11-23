-- Prove2me | solution 1 for GlobalTheory.FullFlag.map_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:45:31.518878+00:00
-- url     : https://prove2.me/submissions/7afa0ba8-94d4-4066-b17c-7ec917dcd8ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsAdaptedOfIsLocalRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TensorProduct
open GlobalTheory
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
open GlobalTheory.FullFlag
variable {n : ℕ}
namespace GlobalTheory.FullFlag
theorem _root_.solution {M' : Type*} [AddCommGroup M'] [Module R M'] (F : FullFlag R M n)
    (e : M ≃ₗ[R] M') (k : Fin (n + 1)) : (F.map e).sub k = (F.sub k).map e.toLinearMap := rfl
end GlobalTheory.FullFlag
