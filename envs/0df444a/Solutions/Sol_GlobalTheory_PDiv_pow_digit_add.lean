-- Prove2me | solution 1 for GlobalTheory.PDiv.pow_digit_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:48:45.330075+00:00
-- url     : https://prove2.me/submissions/2ca6f439-2c97-43d9-9283-d8aa1413014c

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
    x ^ digit n (a + b) = x ^ digit n a * x ^ digit n b := by
  rw [← pow_add]
  exact pow_digit_eq hx (by rw [Nat.cast_add, cast_digit, cast_digit, map_add])
end GlobalTheory.PDiv
