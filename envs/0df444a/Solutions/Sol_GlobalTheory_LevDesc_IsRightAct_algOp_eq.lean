-- Prove2me | solution 1 for GlobalTheory.LevDesc.IsRightAct.algOp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:55:45.255971+00:00
-- url     : https://prove2.me/submissions/f939ac55-7a06-4829-98e0-eef421b26ed6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsRightActFunPull
import Theorems.Thm_GlobalTheory_LevDesc_algOp_single

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
theorem _root_.solution {st : G → R →ₐ[K] R} (hs : IsRightAct st) (e : MonoidAlgebra K G) :
    algOp st e = hs.leftRep.asAlgebraHom e := by
  induction e using MonoidAlgebra.induction_linear with
  | zero => simp [algOp]
  | add a b ha hb => rw [map_add, ← ha, ← hb]; simp [algOp]
  | single g a => ext x; rw [algOp_single, Representation.asAlgebraHom_single]; rfl
end IsRightAct
end GlobalTheory.LevDesc
