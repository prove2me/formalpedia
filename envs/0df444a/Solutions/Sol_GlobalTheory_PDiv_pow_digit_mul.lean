-- Prove2me | solution 1 for GlobalTheory.PDiv.pow_digit_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:48:45.966367+00:00
-- url     : https://prove2.me/submissions/9f88d136-827c-4aee-9522-2721048306e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_KerIdealCompOfSurjective
import Theorems.Thm_GlobalTheory_PDiv_cast_digit
import Theorems.Thm_GlobalTheory_PDiv_pow_digit_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv
open GlobalTheory GlobalTheory.PDiv
variable {p : ℕ} [Fact p.Prime] {M : Type*} [Monoid M]
namespace GlobalTheory.PDiv
theorem _root_.solution {n : ℕ} {x : M} (hx : x ^ p ^ n = 1) (a b : ℤ_[p]) :
    x ^ digit n (a * b) = (x ^ digit n b) ^ digit n a := by
  rw [← pow_mul]
  exact pow_digit_eq hx (by rw [Nat.cast_mul, cast_digit, cast_digit, map_mul, mul_comm])
end GlobalTheory.PDiv
