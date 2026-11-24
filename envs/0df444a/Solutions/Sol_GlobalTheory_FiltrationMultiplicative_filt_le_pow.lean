-- Prove2me | solution 1 for GlobalTheory.FiltrationMultiplicative.filt_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:45:13.928133+00:00
-- url     : https://prove2.me/submissions/fe134f34-35ed-4a6d-9e05-96e57ee7b202

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FiltLePow
import Theorems.Thm_GlobalTheory_FiltrationMultiplicative_mem_max_iff
import Theorems.Thm_GlobalTheory_FiltrationMultiplicative_decomp
import Theorems.Thm_GlobalTheory_FiltrationMultiplicative_part_mem
import Theorems.Thm_GlobalTheory_FiltrationMultiplicative_C_mem_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open GlobalTheory GlobalTheory.FiltrationMultiplicative
variable {O : Type} [CommRing O] [IsLocalRing O]
namespace GlobalTheory.FiltrationMultiplicative
theorem _root_.solution {a : ℕ} (N : ℕ) : ∀ f : MvPowerSeries (Fin a) O, f ∈ Filt O (Fin a) N →
    f ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ^ N := by
  induction N with
  | zero => intro f _; simp
  | succ n ih =>
    intro f hf
    rw [decomp f]
    refine Ideal.add_mem _ ?_ (Ideal.sum_mem _ fun i _ => ?_)
    · apply C_mem_pow
      simpa using hf 0
    · rw [pow_succ']
      exact Ideal.mul_mem_mul ((mem_max_iff _).mpr (by simp)) (ih _ (part_mem hf i))
end GlobalTheory.FiltrationMultiplicative
