-- Prove2me | solution 1 for GlobalTheory.PDiv.pow_digit_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:38:55.993997+00:00
-- url     : https://prove2.me/submissions/ccfc14b9-53dc-40f7-ac09-90bb3b9c0b0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_KerIdealCompOfSurjective

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
theorem _root_.solution {n : ℕ} {x : M} (hx : x ^ p ^ n = 1) {a : ℤ_[p]} {k : ℕ}
    (h : (k : ZMod (p ^ n)) = PadicInt.toZModPow n a) : x ^ digit n a = x ^ k := by
  rw [digit, ← h, ZMod.val_natCast, ← pow_eq_pow_mod _ hx]
end GlobalTheory.PDiv
