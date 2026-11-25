-- Prove2me | solution 1 for GlobalTheory.PDivGroup.Test.level_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:05:34.927117+00:00
-- url     : https://prove2.me/submissions/6c9d5651-b21f-4c69-8e00-96ec296abb14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PadicActionConstInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module CategoryTheory
open GlobalTheory GlobalTheory.PDivGroup GlobalTheory.PDivGroup.Test
open PDiv
variable {p : ℕ} {O : Type} [CommRing O]
namespace GlobalTheory.PDivGroup.Test
theorem _root_.solution (G : PDivGroup p O) (a : G.A 0) : a = algebraMap O _ (counit a) := by
  have h := G.mulBy_pow_self 0 a
  rwa [pow_zero, mulBy, pow_one] at h
end GlobalTheory.PDivGroup.Test
