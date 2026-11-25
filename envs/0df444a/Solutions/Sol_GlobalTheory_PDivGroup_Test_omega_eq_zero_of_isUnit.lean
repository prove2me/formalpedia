-- Prove2me | solution 1 for GlobalTheory.PDivGroup.Test.omega_eq_zero_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:08:31.614239+00:00
-- url     : https://prove2.me/submissions/20082956-1870-4b2d-b600-b83e3fb5646c

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
theorem _root_.solution (G : PDivGroup p O) (hp : IsUnit (p : O)) (w : G.omega) :
    w = 0 := Subtype.ext (funext fun n =>
  (hp.pow n).smul_left_cancel.1 ((G.pow_smul_cot n _).trans (smul_zero _).symm))
end GlobalTheory.PDivGroup.Test
