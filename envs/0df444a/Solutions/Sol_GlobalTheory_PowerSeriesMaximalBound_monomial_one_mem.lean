-- Prove2me | solution 1 for GlobalTheory.PowerSeriesMaximalBound.monomial_one_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:45:07.560917+00:00
-- url     : https://prove2.me/submissions/6bd90749-8290-4024-8526-495def1a185c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MonomialOneMem
import Theorems.Thm_GlobalTheory_PowerSeriesMaximalBound_X_mem_max

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PowerSeriesMaximalBound
open MvPowerSeries
variable {O : Type} [CommRing O] [IsLocalRing O] {a : ℕ}
namespace GlobalTheory.PowerSeriesMaximalBound
theorem _root_.solution (v : Fin a →₀ ℕ) :
    (monomial v (1 : O)) ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ^ (Finsupp.degree v) := by
  induction v using Finsupp.induction with
  | zero => simp
  | single_add i k w hi hk ih =>
    rw [← one_mul (1 : O), ← monomial_mul_monomial, map_add, Finsupp.degree_single, pow_add, ← X_pow_eq]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (X_mem_max i) k) ih
end GlobalTheory.PowerSeriesMaximalBound
