-- Prove2me | solution 1 for GlobalTheory.FullFlag.isAdapted_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:47:03.893803+00:00
-- url     : https://prove2.me/submissions/bc0c0a1b-d4cd-4f12-9b3a-de6bf4341202

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
theorem _root_.solution {F : FullFlag R M n} {b : Basis (Fin n) R M} :
    F.IsAdapted b ↔ ofBasis b = F := ⟨fun h => FullFlag.ext h, fun h => h ▸ rfl⟩
end GlobalTheory.FullFlag
