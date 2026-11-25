-- Prove2me | solution 1 for GlobalTheory.PDivGroup.Test.swap_mul_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:00:54.083282+00:00
-- url     : https://prove2.me/submissions/337c9bf5-2286-4ec2-bbde-74c65583508f

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
theorem _root_.solution (G : PDivGroup p O) : swap G * swap G = 1 :=
  hom_ext fun _ => BialgHom.coe_toAlgHom_injective (Algebra.TensorProduct.ext' fun _ _ => rfl)
end GlobalTheory.PDivGroup.Test
