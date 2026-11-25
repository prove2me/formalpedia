-- Prove2me | solution 1 for GlobalTheory.PDivGroup.Test.mu_tate_char_p
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:08:25.903158+00:00
-- url     : https://prove2.me/submissions/ab7ee704-85c5-4aaf-ab49-14d3ac351728

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
theorem _root_.solution [Fact p.Prime] (k : Type) [Field k] [CharP k p] (x : (mu p k).Tate) :
    x = 0 := muRoot_ext fun n => by
  rw [muRoot_zero]
  have h := muRoot_pow_self x n
  have h2 : (muRoot x n - 1) ^ p ^ n = 0 := by rw [sub_pow_char_pow, h, one_pow, sub_self]
  exact sub_eq_zero.1 (pow_eq_zero_iff (pow_pos (Fact.out : p.Prime).pos n).ne' |>.1 h2)
end GlobalTheory.PDivGroup.Test
