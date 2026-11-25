-- Prove2me | solution 1 for GlobalTheory.PDiv.pow_dvd_sub_digit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:48:49.657741+00:00
-- url     : https://prove2.me/submissions/adcaf47b-469d-464f-a189-53333c3a0331

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_KerIdealCompOfSurjective
import Theorems.Thm_GlobalTheory_PDiv_cast_digit

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
theorem _root_.solution (n : ℕ) (a : ℤ_[p]) : (p : ℤ_[p]) ^ n ∣ a - digit n a := by
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
    map_natCast, cast_digit, sub_self]
end GlobalTheory.PDiv
