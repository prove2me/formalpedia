-- Prove2me | solution 1 for GlobalTheory.GradedFixed.WA_union
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:36:37.912393+00:00
-- url     : https://prove2.me/submissions/57738551-4369-4184-a13b-7f3aa9f41b03

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FixedMemOfOrbitHeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Submodule MulAction
open GlobalTheory GlobalTheory.GradedFixed
variable {G ι M : Type} [Group G] [MulAction G ι] [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.GradedFixed
theorem _root_.solution (V : ι → Submodule ℂ M) (A B : Set ι) : WA V (A ∪ B) = WA V A ⊔ WA V B :=
  iSup_union
end GlobalTheory.GradedFixed
