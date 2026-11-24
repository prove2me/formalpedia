-- Prove2me | solution 1 for GlobalTheory.LimitSeriesPowSmul.exists_limit_series
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:58:23.579836+00:00
-- url     : https://prove2.me/submissions/98ce7382-f4e4-42c1-8d67-23bd9ef358d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLimitSeries
import Theorems.Thm_GlobalTheory_LimitSeriesPowSmul_mem_pow_smul_top_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LimitSeriesPowSmul
namespace GlobalTheory.LimitSeriesPowSmul
theorem _root_.solution {R : Type} [CommRing R] (p : R) [IsPrecomplete (Ideal.span {p}) R]
    (f : ℕ → R) : ∃ (L : R), ∀ (k : ℕ), p ^ k ∣ ∑ i ∈ Finset.range k, p ^ i * f i - L := by
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {p})
    (fun k => ∑ i ∈ Finset.range k, p ^ i * f i) (by
      intro m n hmn
      rw [SModEq.sub_mem, mem_pow_smul_top_iff, ← Finset.sum_range_add_sum_Ico _ hmn,
        sub_add_cancel_left, dvd_neg]
      refine Finset.dvd_sum fun i hi => ?_
      exact Dvd.dvd.mul_right (pow_dvd_pow p (Finset.mem_Ico.mp hi).1) _)
  exact ⟨L, fun k => (mem_pow_smul_top_iff p k _).mp ((SModEq.sub_mem).mp (hL k))⟩
end GlobalTheory.LimitSeriesPowSmul
