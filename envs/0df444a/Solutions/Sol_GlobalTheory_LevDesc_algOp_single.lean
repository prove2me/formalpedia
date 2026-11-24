-- Prove2me | solution 1 for GlobalTheory.LevDesc.algOp_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:41:26.61186+00:00
-- url     : https://prove2.me/submissions/2fe4fb16-6b1d-4cba-8e75-6336025dc7e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsRightActFunPull

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
theorem _root_.solution (g : G) (a : K) (x : R) : algOp st (MonoidAlgebra.single g a) x = a • st g⁻¹ x := by
  simp [algOp]
end GlobalTheory.LevDesc
