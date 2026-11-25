-- Prove2me | solution 1 for GlobalTheory.LevDesc.isRightAct_funPull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:04:10.064745+00:00
-- url     : https://prove2.me/submissions/48743ce1-ee25-47a7-81a2-37cbf845cba0

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
namespace GlobalTheory.LevDesc
theorem _root_.solution {Z : Type} [MulAction G Z] : IsRightAct (funPull K (Z := Z) (G := G)) :=
  ⟨fun x => funext fun z => congrArg x (one_smul G z), fun h h' x => funext fun z => congrArg x (mul_smul h h' z)⟩
end GlobalTheory.LevDesc
