-- Prove2me | solution 1 for GlobalTheory.PowerSeriesCoeffSum.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:03:21.270781+00:00
-- url     : https://prove2.me/submissions/fc932f20-2402-4982-be91-e1eba26f4732

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_CoeffXMulPart
import Theorems.Thm_GlobalTheory_PowerSeriesCoeffSum_coeff_part
import Theorems.Thm_GlobalTheory_PowerSeriesCoeffSum_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PowerSeriesCoeffSum
open MvPowerSeries Finsupp
variable {O : Type} [CommRing O] {a : ℕ}
namespace GlobalTheory.PowerSeriesCoeffSum
theorem _root_.solution : ∀ (O : Type) [inst : CommRing O] (a n : ℕ) (f : MvPowerSeries (Fin a) O),
    (∀ (m : Fin a →₀ ℕ), (Finsupp.degree : (Fin a →₀ ℕ) → ℕ) m < n →
      (MvPowerSeries.coeff m : MvPowerSeries (Fin a) O → O) f = (0 : O)) →
    f ∈ Ideal.span (Set.range MvPowerSeries.X) ^ n := by
  intro O _ a n
  induction n with
  | zero => intro f _; simp
  | succ n ih =>
    intro f hf
    have h0 : coeff 0 f = 0 := hf 0 (by simp)
    rw [eq_sum f h0, pow_succ']
    refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul (Ideal.subset_span ⟨i, rfl⟩) (ih _ ?_)
    intro e he
    rw [coeff_part]
    split_ifs
    · apply hf
      rw [map_add, degree_single]; omega
    · rfl
end GlobalTheory.PowerSeriesCoeffSum
