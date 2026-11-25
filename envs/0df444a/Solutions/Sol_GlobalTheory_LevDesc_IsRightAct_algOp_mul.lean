-- Prove2me | solution 1 for GlobalTheory.LevDesc.IsRightAct.algOp_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:04:51.629989+00:00
-- url     : https://prove2.me/submissions/4b6e7fc6-b0c6-4a57-92bc-891a04b41cb1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsRightActFunPull
import Theorems.Thm_GlobalTheory_LevDesc_IsRightAct_algOp_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LevDesc
variable {G K R : Type} [Group G] [Field K] [CommRing R] [Algebra K R]
variable (st : G → R →ₐ[K] R)
namespace GlobalTheory.LevDesc
namespace IsRightAct
theorem _root_.solution {st : G → R →ₐ[K] R} (hs : IsRightAct st) (e e' : MonoidAlgebra K G) :
    algOp st (e * e') = algOp st e * algOp st e' := by
  rw [hs.algOp_eq, hs.algOp_eq, hs.algOp_eq, map_mul]
end IsRightAct
end GlobalTheory.LevDesc
