-- Prove2me | solution 1 for GlobalTheory.PowerSeriesMaximalBound.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:03:23.023181+00:00
-- url     : https://prove2.me/submissions/f7130ffd-c318-4f8d-9b79-9d21ec649793

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MonomialOneMem
import Theorems.Thm_GlobalTheory_PowerSeriesMaximalBound_map_le_max
import Theorems.Thm_GlobalTheory_PowerSeriesMaximalBound_monomial_one_mem

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
theorem _root_.solution : ∀ {O : Type} [inst : CommRing O] [inst_1 : IsLocalRing O] {a N : ℕ} (v : Fin a →₀ ℕ) {c : O}, c ∈ IsLocalRing.maximalIdeal O ^ (N - (Finsupp.degree : (Fin a →₀ ℕ) → ℕ) v) → (MvPowerSeries.monomial v : O → MvPowerSeries (Fin a) O) c ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ^ N := by
  intro O _ _ a N v c hc
  have h1 : (C c : MvPowerSeries (Fin a) O) ∈
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ^ (N - Finsupp.degree v) := by
    have : (C c : MvPowerSeries (Fin a) O) ∈
        Ideal.map (C : O →+* MvPowerSeries (Fin a) O) (IsLocalRing.maximalIdeal O ^ (N - Finsupp.degree v)) :=
      Ideal.mem_map_of_mem _ hc
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono map_le_max _ this
  have h2 : monomial v c = C c * monomial v (1 : O) := by
    rw [← monomial_zero_eq_C, monomial_mul_monomial, zero_add, mul_one]
  rw [h2]
  refine Ideal.pow_le_pow_right (by omega : N ≤ (N - Finsupp.degree v) + Finsupp.degree v) ?_
  rw [pow_add]
  exact Ideal.mul_mem_mul h1 (monomial_one_mem v)
end GlobalTheory.PowerSeriesMaximalBound
