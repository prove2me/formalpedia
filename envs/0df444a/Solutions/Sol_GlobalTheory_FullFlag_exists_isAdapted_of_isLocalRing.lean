-- Prove2me | solution 1 for GlobalTheory.FullFlag.exists_isAdapted_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:29:17.121004+00:00
-- url     : https://prove2.me/submissions/ccfc223b-0bda-4f62-88a7-4fe69a642e24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsAdaptedOfIsLocalRing
import Theorems.Thm_GlobalTheory_FullFlag_exists_isAdapted_of_free

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
theorem _root_.solution [IsLocalRing R] (F : FullFlag R M n) :
    ∃ b : Basis (Fin n) R M, F.IsAdapted b :=
  F.exists_isAdapted_of_free fun _ => Module.free_of_flat_of_isLocalRing
end GlobalTheory.FullFlag
