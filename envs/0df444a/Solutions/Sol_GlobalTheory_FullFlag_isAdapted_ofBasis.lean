-- Prove2me | solution 1 for GlobalTheory.FullFlag.isAdapted_ofBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:50:11.329442+00:00
-- url     : https://prove2.me/submissions/52b46c09-49d8-4b4e-881d-38eca1e9c916

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
theorem _root_.solution (b : Basis (Fin n) R M) : (ofBasis b).IsAdapted b := rfl
end GlobalTheory.FullFlag
