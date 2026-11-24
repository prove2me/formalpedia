-- Prove2me | solution 1 for GlobalTheory.FullFlag.monotone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:47:06.23849+00:00
-- url     : https://prove2.me/submissions/38862c3d-1efc-476d-847d-2aefd501db1b

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
theorem _root_.solution (F : FullFlag R M n) : Monotone F.sub :=
  Fin.monotone_iff_le_succ.2 F.castSucc_le_succ
end GlobalTheory.FullFlag
