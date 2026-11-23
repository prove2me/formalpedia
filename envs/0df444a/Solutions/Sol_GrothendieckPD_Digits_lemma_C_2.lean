-- Prove2me | solution 1 for GrothendieckPD.Digits.lemma_C_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:34:41.417842+00:00
-- url     : https://prove2.me/submissions/c2e4cd20-9aff-4777-ab9f-48d4111bb1f7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GrothendieckPD_Digits_claim_C_2_4
import Theorems.Thm_GrothendieckPD_Digits_claim_C_2_5

open GrothendieckPD.Digits

theorem solution :
    (∀ i ∈ insert 14 (Finset.Icc 17 31), Summable fun k => |Hcoef i (k + 682)|) ∧
      lam 14 * ∑' k, |Hcoef 14 (k + 682)| +
          ∑ i ∈ Finset.Icc 17 31, lam i * ∑' k, |Hcoef i (k + 682)| <
        (0.000003878150168295 : ℝ) := by
  constructor
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_Icc] at hi
    rcases hi with rfl | ⟨hi17, hi31⟩
    · exact claim_C_2_4.1
    · exact claim_C_2_5.1 i (Finset.mem_Icc.mpr ⟨hi17, hi31⟩)
  · calc
      lam 14 * ∑' k, |Hcoef 14 (k + 682)| +
          ∑ i ∈ Finset.Icc 17 31, lam i * ∑' k, |Hcoef i (k + 682)| <
          (0.000001254728050780 : ℝ) + 0.000002623422117515 :=
        add_lt_add claim_C_2_4.2 claim_C_2_5.2
      _ = 0.000003878150168295 := by norm_num