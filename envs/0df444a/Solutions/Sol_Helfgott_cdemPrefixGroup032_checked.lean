-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup032_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T02:27:46.410368+00:00
-- url     : https://prove2.me/submissions/f8c27427-d35e-43a9-ad83-dc0bc26d8893

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset
open scoped BigOperators
namespace Helfgott
private theorem cdemPrefixStats_131072_131136 :
    (∑ n ∈ Ico 131072 131136, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 131072 131136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 131072 131136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (76286 : ℤ) ∧
    (∑ n ∈ Ico 131072 131136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1525745135546531231831221534 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_131136_131200 :
    (∑ n ∈ Ico 131136 131200, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 131136 131200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 131136 131200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (266827 : ℤ) ∧
    (∑ n ∈ Ico 131136 131200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5336638520947945796205451261 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_131072_131200 :
    (∑ n ∈ Ico 131072 131200, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 131072 131200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 131072 131200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (343113 : ℤ) ∧
    (∑ n ∈ Ico 131072 131200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6862383656494477028036672795 : ℤ) := by
  rcases cdemPrefixStats_131072_131136 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_131136_131200 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 131072 ≤ 131136) (by norm_num : 131136 ≤ 131200), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 131072 ≤ 131136) (by norm_num : 131136 ≤ 131200), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 131072 ≤ 131136) (by norm_num : 131136 ≤ 131200), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 131072 ≤ 131136) (by norm_num : 131136 ≤ 131200), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_131200_131264 :
    (∑ n ∈ Ico 131200 131264, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 131200 131264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 131200 131264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (266679 : ℤ) ∧
    (∑ n ∈ Ico 131200 131264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5333635261570265789103082446 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_131264_131328 :
    (∑ n ∈ Ico 131264 131328, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 131264 131328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 131264 131328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (228489 : ℤ) ∧
    (∑ n ∈ Ico 131264 131328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4569780574414991973139675414 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_131200_131328 :
    (∑ n ∈ Ico 131200 131328, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 131200 131328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 131200 131328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (495168 : ℤ) ∧
    (∑ n ∈ Ico 131200 131328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9903415835985257762242757860 : ℤ) := by
  rcases cdemPrefixStats_131200_131264 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_131264_131328 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 131200 ≤ 131264) (by norm_num : 131264 ≤ 131328), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 131200 ≤ 131264) (by norm_num : 131264 ≤ 131328), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 131200 ≤ 131264) (by norm_num : 131264 ≤ 131328), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 131200 ≤ 131264) (by norm_num : 131264 ≤ 131328), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_131072_131328 :
    (∑ n ∈ Ico 131072 131328, mobiusTreeValue 16 mobiusTable1200001 n) = (22 : ℤ) ∧
    (∑ n ∈ Ico 131072 131328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 131072 131328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (838281 : ℤ) ∧
    (∑ n ∈ Ico 131072 131328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (16765799492479734790279430655 : ℤ) := by
  rcases cdemPrefixStats_131072_131200 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_131200_131328 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 131072 ≤ 131200) (by norm_num : 131200 ≤ 131328), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 131072 ≤ 131200) (by norm_num : 131200 ≤ 131328), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 131072 ≤ 131200) (by norm_num : 131200 ≤ 131328), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 131072 ≤ 131200) (by norm_num : 131200 ≤ 131328), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_131328_131392 :
    (∑ n ∈ Ico 131328 131392, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 131328 131392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 131328 131392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (304514 : ℤ) ∧
    (∑ n ∈ Ico 131328 131392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6090325417702075322878488615 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_131392_131456 :
    (∑ n ∈ Ico 131392 131456, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 131392 131456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 131392 131456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-76056 : ℤ) ∧
    (∑ n ∈ Ico 131392 131456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1521143742156866429376286678 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_131328_131456 :
    (∑ n ∈ Ico 131328 131456, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 131328 131456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 131328 131456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (228458 : ℤ) ∧
    (∑ n ∈ Ico 131328 131456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4569181675545208893502201937 : ℤ) := by
  rcases cdemPrefixStats_131328_131392 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_131392_131456 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 131328 ≤ 131392) (by norm_num : 131392 ≤ 131456), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 131328 ≤ 131392) (by norm_num : 131392 ≤ 131456), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 131328 ≤ 131392) (by norm_num : 131392 ≤ 131456), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 131328 ≤ 131392) (by norm_num : 131392 ≤ 131456), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_131456_131520 :
    (∑ n ∈ Ico 131456 131520, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 131456 131520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 131456 131520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-190079 : ℤ) ∧
    (∑ n ∈ Ico 131456 131520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3801662483685393665680635447 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_131520_131584 :
    (∑ n ∈ Ico 131520 131584, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 131520 131584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 131520 131584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (29 : ℤ) ∧
    (∑ n ∈ Ico 131520 131584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (571949157592975677031187 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_131456_131584 :
    (∑ n ∈ Ico 131456 131584, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 131456 131584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 131456 131584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-190050 : ℤ) ∧
    (∑ n ∈ Ico 131456 131584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3801090534527800690003604260 : ℤ) := by
  rcases cdemPrefixStats_131456_131520 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_131520_131584 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 131456 ≤ 131520) (by norm_num : 131520 ≤ 131584), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 131456 ≤ 131520) (by norm_num : 131520 ≤ 131584), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 131456 ≤ 131520) (by norm_num : 131520 ≤ 131584), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 131456 ≤ 131520) (by norm_num : 131520 ≤ 131584), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_131328_131584 :
    (∑ n ∈ Ico 131328 131584, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 131328 131584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 131328 131584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (38408 : ℤ) ∧
    (∑ n ∈ Ico 131328 131584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (768091141017408203498597677 : ℤ) := by
  rcases cdemPrefixStats_131328_131456 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_131456_131584 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 131328 ≤ 131456) (by norm_num : 131456 ≤ 131584), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 131328 ≤ 131456) (by norm_num : 131456 ≤ 131584), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 131328 ≤ 131456) (by norm_num : 131456 ≤ 131584), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 131328 ≤ 131456) (by norm_num : 131456 ≤ 131584), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_131072_131584 :
    (∑ n ∈ Ico 131072 131584, mobiusTreeValue 16 mobiusTable1200001 n) = (23 : ℤ) ∧
    (∑ n ∈ Ico 131072 131584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 131072 131584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (876689 : ℤ) ∧
    (∑ n ∈ Ico 131072 131584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17533890633497142993778028332 : ℤ) := by
  rcases cdemPrefixStats_131072_131328 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_131328_131584 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 131072 ≤ 131328) (by norm_num : 131328 ≤ 131584), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 131072 ≤ 131328) (by norm_num : 131328 ≤ 131584), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 131072 ≤ 131328) (by norm_num : 131328 ≤ 131584), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 131072 ≤ 131328) (by norm_num : 131328 ≤ 131584), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_131584_131648 :
    (∑ n ∈ Ico 131584 131648, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 131584 131648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 131584 131648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-265918 : ℤ) ∧
    (∑ n ∈ Ico 131584 131648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5318410019023153724337058500 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_131648_131712 :
    (∑ n ∈ Ico 131648 131712, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 131648 131712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 131648 131712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (227851 : ℤ) ∧
    (∑ n ∈ Ico 131648 131712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4557071528456407755845313272 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_131584_131712 :
    (∑ n ∈ Ico 131584 131712, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 131584 131712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 131584 131712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-38067 : ℤ) ∧
    (∑ n ∈ Ico 131584 131712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-761338490566745968491745228 : ℤ) := by
  rcases cdemPrefixStats_131584_131648 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_131648_131712 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 131584 ≤ 131648) (by norm_num : 131648 ≤ 131712), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 131584 ≤ 131648) (by norm_num : 131648 ≤ 131712), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 131584 ≤ 131648) (by norm_num : 131648 ≤ 131712), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 131584 ≤ 131648) (by norm_num : 131648 ≤ 131712), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_131712_131776 :
    (∑ n ∈ Ico 131712 131776, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 131712 131776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 131712 131776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-151778 : ℤ) ∧
    (∑ n ∈ Ico 131712 131776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3035598120991699178017763696 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_131776_131840 :
    (∑ n ∈ Ico 131776 131840, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 131776 131840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 131776 131840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-341399 : ℤ) ∧
    (∑ n ∈ Ico 131776 131840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6827964242328693656216274861 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_131712_131840 :
    (∑ n ∈ Ico 131712 131840, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 131712 131840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 131712 131840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-493177 : ℤ) ∧
    (∑ n ∈ Ico 131712 131840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9863562363320392834234038557 : ℤ) := by
  rcases cdemPrefixStats_131712_131776 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_131776_131840 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 131712 ≤ 131776) (by norm_num : 131776 ≤ 131840), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 131712 ≤ 131776) (by norm_num : 131776 ≤ 131840), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 131712 ≤ 131776) (by norm_num : 131776 ≤ 131840), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 131712 ≤ 131776) (by norm_num : 131776 ≤ 131840), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_131584_131840 :
    (∑ n ∈ Ico 131584 131840, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 131584 131840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 131584 131840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-531244 : ℤ) ∧
    (∑ n ∈ Ico 131584 131840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10624900853887138802725783785 : ℤ) := by
  rcases cdemPrefixStats_131584_131712 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_131712_131840 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 131584 ≤ 131712) (by norm_num : 131712 ≤ 131840), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 131584 ≤ 131712) (by norm_num : 131712 ≤ 131840), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 131584 ≤ 131712) (by norm_num : 131712 ≤ 131840), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 131584 ≤ 131712) (by norm_num : 131712 ≤ 131840), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_131840_131904 :
    (∑ n ∈ Ico 131840 131904, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 131840 131904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 131840 131904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (227517 : ℤ) ∧
    (∑ n ∈ Ico 131840 131904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4550435954512731538032813480 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_131904_131968 :
    (∑ n ∈ Ico 131904 131968, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 131904 131968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 131904 131968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (37861 : ℤ) ∧
    (∑ n ∈ Ico 131904 131968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (757242529933190716473633644 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_131840_131968 :
    (∑ n ∈ Ico 131840 131968, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 131840 131968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 131840 131968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (265378 : ℤ) ∧
    (∑ n ∈ Ico 131840 131968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5307678484445922254506447124 : ℤ) := by
  rcases cdemPrefixStats_131840_131904 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_131904_131968 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 131840 ≤ 131904) (by norm_num : 131904 ≤ 131968), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 131840 ≤ 131904) (by norm_num : 131904 ≤ 131968), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 131840 ≤ 131904) (by norm_num : 131904 ≤ 131968), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 131840 ≤ 131904) (by norm_num : 131904 ≤ 131968), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_131968_132032 :
    (∑ n ∈ Ico 131968 132032, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 131968 132032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 131968 132032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (189411 : ℤ) ∧
    (∑ n ∈ Ico 131968 132032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3788315046549955847020458249 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_132032_132096 :
    (∑ n ∈ Ico 132032 132096, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 132032 132096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 132032 132096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (264938 : ℤ) ∧
    (∑ n ∈ Ico 132032 132096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5298883690659300843382789014 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_131968_132096 :
    (∑ n ∈ Ico 131968 132096, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 131968 132096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 131968 132096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (454349 : ℤ) ∧
    (∑ n ∈ Ico 131968 132096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9087198737209256690403247263 : ℤ) := by
  rcases cdemPrefixStats_131968_132032 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_132032_132096 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 131968 ≤ 132032) (by norm_num : 132032 ≤ 132096), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 131968 ≤ 132032) (by norm_num : 132032 ≤ 132096), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 131968 ≤ 132032) (by norm_num : 132032 ≤ 132096), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 131968 ≤ 132032) (by norm_num : 132032 ≤ 132096), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_131840_132096 :
    (∑ n ∈ Ico 131840 132096, mobiusTreeValue 16 mobiusTable1200001 n) = (19 : ℤ) ∧
    (∑ n ∈ Ico 131840 132096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 131840 132096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (719727 : ℤ) ∧
    (∑ n ∈ Ico 131840 132096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14394877221655178944909694387 : ℤ) := by
  rcases cdemPrefixStats_131840_131968 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_131968_132096 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 131840 ≤ 131968) (by norm_num : 131968 ≤ 132096), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 131840 ≤ 131968) (by norm_num : 131968 ≤ 132096), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 131840 ≤ 131968) (by norm_num : 131968 ≤ 132096), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 131840 ≤ 131968) (by norm_num : 131968 ≤ 132096), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_131584_132096 :
    (∑ n ∈ Ico 131584 132096, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 131584 132096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 131584 132096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (188483 : ℤ) ∧
    (∑ n ∈ Ico 131584 132096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3769976367768040142183910602 : ℤ) := by
  rcases cdemPrefixStats_131584_131840 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_131840_132096 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 131584 ≤ 131840) (by norm_num : 131840 ≤ 132096), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 131584 ≤ 131840) (by norm_num : 131840 ≤ 132096), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 131584 ≤ 131840) (by norm_num : 131840 ≤ 132096), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 131584 ≤ 131840) (by norm_num : 131840 ≤ 132096), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_131072_132096 :
    (∑ n ∈ Ico 131072 132096, mobiusTreeValue 16 mobiusTable1200001 n) = (28 : ℤ) ∧
    (∑ n ∈ Ico 131072 132096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (622 : ℕ) ∧
    (∑ n ∈ Ico 131072 132096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1065172 : ℤ) ∧
    (∑ n ∈ Ico 131072 132096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (21303867001265183135961938934 : ℤ) := by
  rcases cdemPrefixStats_131072_131584 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_131584_132096 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 131072 ≤ 131584) (by norm_num : 131584 ≤ 132096), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 131072 ≤ 131584) (by norm_num : 131584 ≤ 132096), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 131072 ≤ 131584) (by norm_num : 131584 ≤ 132096), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 131072 ≤ 131584) (by norm_num : 131584 ≤ 132096), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_132096_132160 :
    (∑ n ∈ Ico 132096 132160, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 132096 132160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 132096 132160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-37868 : ℤ) ∧
    (∑ n ∈ Ico 132096 132160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-757454903013312805902925736 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_132160_132224 :
    (∑ n ∈ Ico 132160 132224, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 132160 132224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 132160 132224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (75628 : ℤ) ∧
    (∑ n ∈ Ico 132160 132224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1512601793670964828569230909 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_132096_132224 :
    (∑ n ∈ Ico 132096 132224, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 132096 132224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 132096 132224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (37760 : ℤ) ∧
    (∑ n ∈ Ico 132096 132224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (755146890657652022666305173 : ℤ) := by
  rcases cdemPrefixStats_132096_132160 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_132160_132224 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 132096 ≤ 132160) (by norm_num : 132160 ≤ 132224), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 132096 ≤ 132160) (by norm_num : 132160 ≤ 132224), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 132096 ≤ 132160) (by norm_num : 132160 ≤ 132224), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 132096 ≤ 132160) (by norm_num : 132160 ≤ 132224), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_132224_132288 :
    (∑ n ∈ Ico 132224 132288, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 132224 132288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 132224 132288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-415887 : ℤ) ∧
    (∑ n ∈ Ico 132224 132288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8317837761979758087397196568 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_132288_132352 :
    (∑ n ∈ Ico 132288 132352, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 132288 132352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 132288 132352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-151122 : ℤ) ∧
    (∑ n ∈ Ico 132288 132352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3022483413520863429461524596 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_132224_132352 :
    (∑ n ∈ Ico 132224 132352, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 132224 132352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 132224 132352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-567009 : ℤ) ∧
    (∑ n ∈ Ico 132224 132352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11340321175500621516858721164 : ℤ) := by
  rcases cdemPrefixStats_132224_132288 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_132288_132352 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 132224 ≤ 132288) (by norm_num : 132288 ≤ 132352), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 132224 ≤ 132288) (by norm_num : 132288 ≤ 132352), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 132224 ≤ 132288) (by norm_num : 132288 ≤ 132352), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 132224 ≤ 132288) (by norm_num : 132288 ≤ 132352), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_132096_132352 :
    (∑ n ∈ Ico 132096 132352, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 132096 132352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 132096 132352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-529249 : ℤ) ∧
    (∑ n ∈ Ico 132096 132352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10585174284842969494192415991 : ℤ) := by
  rcases cdemPrefixStats_132096_132224 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_132224_132352 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 132096 ≤ 132224) (by norm_num : 132224 ≤ 132352), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 132096 ≤ 132224) (by norm_num : 132224 ≤ 132352), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 132096 ≤ 132224) (by norm_num : 132224 ≤ 132352), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 132096 ≤ 132224) (by norm_num : 132224 ≤ 132352), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_132352_132416 :
    (∑ n ∈ Ico 132352 132416, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 132352 132416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 132352 132416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (113317 : ℤ) ∧
    (∑ n ∈ Ico 132352 132416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2266328927693870882836780298 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_132416_132480 :
    (∑ n ∈ Ico 132416 132480, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 132416 132480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 132416 132480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-226532 : ℤ) ∧
    (∑ n ∈ Ico 132416 132480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4530723835465431013405841229 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_132352_132480 :
    (∑ n ∈ Ico 132352 132480, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 132352 132480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 132352 132480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-113215 : ℤ) ∧
    (∑ n ∈ Ico 132352 132480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2264394907771560130569060931 : ℤ) := by
  rcases cdemPrefixStats_132352_132416 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_132416_132480 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 132352 ≤ 132416) (by norm_num : 132416 ≤ 132480), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 132352 ≤ 132416) (by norm_num : 132416 ≤ 132480), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 132352 ≤ 132416) (by norm_num : 132416 ≤ 132480), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 132352 ≤ 132416) (by norm_num : 132416 ≤ 132480), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_132480_132544 :
    (∑ n ∈ Ico 132480 132544, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 132480 132544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 132480 132544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-226371 : ℤ) ∧
    (∑ n ∈ Ico 132480 132544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4527458971384802844350567906 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_132544_132608 :
    (∑ n ∈ Ico 132544 132608, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 132544 132608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 132544 132608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-37710 : ℤ) ∧
    (∑ n ∈ Ico 132544 132608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-754210510765719977670900103 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_132480_132608 :
    (∑ n ∈ Ico 132480 132608, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 132480 132608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 132480 132608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-264081 : ℤ) ∧
    (∑ n ∈ Ico 132480 132608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5281669482150522822021468009 : ℤ) := by
  rcases cdemPrefixStats_132480_132544 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_132544_132608 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 132480 ≤ 132544) (by norm_num : 132544 ≤ 132608), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 132480 ≤ 132544) (by norm_num : 132544 ≤ 132608), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 132480 ≤ 132544) (by norm_num : 132544 ≤ 132608), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 132480 ≤ 132544) (by norm_num : 132544 ≤ 132608), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_132352_132608 :
    (∑ n ∈ Ico 132352 132608, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 132352 132608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 132352 132608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-377296 : ℤ) ∧
    (∑ n ∈ Ico 132352 132608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7546064389922082952590528940 : ℤ) := by
  rcases cdemPrefixStats_132352_132480 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_132480_132608 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 132352 ≤ 132480) (by norm_num : 132480 ≤ 132608), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 132352 ≤ 132480) (by norm_num : 132480 ≤ 132608), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 132352 ≤ 132480) (by norm_num : 132480 ≤ 132608), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 132352 ≤ 132480) (by norm_num : 132480 ≤ 132608), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_132096_132608 :
    (∑ n ∈ Ico 132096 132608, mobiusTreeValue 16 mobiusTable1200001 n) = (-24 : ℤ) ∧
    (∑ n ∈ Ico 132096 132608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 132096 132608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-906545 : ℤ) ∧
    (∑ n ∈ Ico 132096 132608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-18131238674765052446782944931 : ℤ) := by
  rcases cdemPrefixStats_132096_132352 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_132352_132608 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 132096 ≤ 132352) (by norm_num : 132352 ≤ 132608), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 132096 ≤ 132352) (by norm_num : 132352 ≤ 132608), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 132096 ≤ 132352) (by norm_num : 132352 ≤ 132608), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 132096 ≤ 132352) (by norm_num : 132352 ≤ 132608), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_132608_132672 :
    (∑ n ∈ Ico 132608 132672, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 132608 132672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 132608 132672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-565401 : ℤ) ∧
    (∑ n ∈ Ico 132608 132672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11308169418532874344343160672 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_132672_132736 :
    (∑ n ∈ Ico 132672 132736, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 132672 132736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 132672 132736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (188413 : ℤ) ∧
    (∑ n ∈ Ico 132672 132736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3768278096338508253015774004 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_132608_132736 :
    (∑ n ∈ Ico 132608 132736, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 132608 132736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 132608 132736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-376988 : ℤ) ∧
    (∑ n ∈ Ico 132608 132736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7539891322194366091327386668 : ℤ) := by
  rcases cdemPrefixStats_132608_132672 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_132672_132736 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 132608 ≤ 132672) (by norm_num : 132672 ≤ 132736), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 132608 ≤ 132672) (by norm_num : 132672 ≤ 132736), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 132608 ≤ 132672) (by norm_num : 132672 ≤ 132736), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 132608 ≤ 132672) (by norm_num : 132672 ≤ 132736), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_132736_132800 :
    (∑ n ∈ Ico 132736 132800, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 132736 132800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 132736 132800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-376590 : ℤ) ∧
    (∑ n ∈ Ico 132736 132800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7531805142649338538119498841 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_132800_132864 :
    (∑ n ∈ Ico 132800 132864, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 132800 132864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 132800 132864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (150622 : ℤ) ∧
    (∑ n ∈ Ico 132800 132864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3012433449114800877263051829 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_132736_132864 :
    (∑ n ∈ Ico 132736 132864, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 132736 132864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (74 : ℕ) ∧
    (∑ n ∈ Ico 132736 132864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-225968 : ℤ) ∧
    (∑ n ∈ Ico 132736 132864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4519371693534537660856447012 : ℤ) := by
  rcases cdemPrefixStats_132736_132800 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_132800_132864 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 132736 ≤ 132800) (by norm_num : 132800 ≤ 132864), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 132736 ≤ 132800) (by norm_num : 132800 ≤ 132864), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 132736 ≤ 132800) (by norm_num : 132800 ≤ 132864), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 132736 ≤ 132800) (by norm_num : 132800 ≤ 132864), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_132608_132864 :
    (∑ n ∈ Ico 132608 132864, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 132608 132864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 132608 132864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-602956 : ℤ) ∧
    (∑ n ∈ Ico 132608 132864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12059263015728903752183833680 : ℤ) := by
  rcases cdemPrefixStats_132608_132736 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_132736_132864 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 132608 ≤ 132736) (by norm_num : 132736 ≤ 132864), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 132608 ≤ 132736) (by norm_num : 132736 ≤ 132864), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 132608 ≤ 132736) (by norm_num : 132736 ≤ 132864), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 132608 ≤ 132736) (by norm_num : 132736 ≤ 132864), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_132864_132928 :
    (∑ n ∈ Ico 132864 132928, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 132864 132928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 132864 132928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-225746 : ℤ) ∧
    (∑ n ∈ Ico 132864 132928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4514989937616230744250662365 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_132928_132992 :
    (∑ n ∈ Ico 132928 132992, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 132928 132992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 132928 132992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-263265 : ℤ) ∧
    (∑ n ∈ Ico 132928 132992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5265346555513458212257391712 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_132864_132992 :
    (∑ n ∈ Ico 132864 132992, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 132864 132992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 132864 132992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-489011 : ℤ) ∧
    (∑ n ∈ Ico 132864 132992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9780336493129688956508054077 : ℤ) := by
  rcases cdemPrefixStats_132864_132928 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_132928_132992 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 132864 ≤ 132928) (by norm_num : 132928 ≤ 132992), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 132864 ≤ 132928) (by norm_num : 132928 ≤ 132992), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 132864 ≤ 132928) (by norm_num : 132928 ≤ 132992), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 132864 ≤ 132928) (by norm_num : 132928 ≤ 132992), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_132992_133056 :
    (∑ n ∈ Ico 132992 133056, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 132992 133056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 132992 133056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-75188 : ℤ) ∧
    (∑ n ∈ Ico 132992 133056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1503787668945536339354490164 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_133056_133120 :
    (∑ n ∈ Ico 133056 133120, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 133056 133120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 133056 133120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (112751 : ℤ) ∧
    (∑ n ∈ Ico 133056 133120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2255034035798103538508115034 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_132992_133120 :
    (∑ n ∈ Ico 132992 133120, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 132992 133120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 132992 133120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (37563 : ℤ) ∧
    (∑ n ∈ Ico 132992 133120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (751246366852567199153624870 : ℤ) := by
  rcases cdemPrefixStats_132992_133056 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_133056_133120 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 132992 ≤ 133056) (by norm_num : 133056 ≤ 133120), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 132992 ≤ 133056) (by norm_num : 133056 ≤ 133120), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 132992 ≤ 133056) (by norm_num : 133056 ≤ 133120), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 132992 ≤ 133056) (by norm_num : 133056 ≤ 133120), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_132864_133120 :
    (∑ n ∈ Ico 132864 133120, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 132864 133120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 132864 133120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-451448 : ℤ) ∧
    (∑ n ∈ Ico 132864 133120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9029090126277121757354429207 : ℤ) := by
  rcases cdemPrefixStats_132864_132992 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_132992_133120 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 132864 ≤ 132992) (by norm_num : 132992 ≤ 133120), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 132864 ≤ 132992) (by norm_num : 132992 ≤ 133120), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 132864 ≤ 132992) (by norm_num : 132992 ≤ 133120), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 132864 ≤ 132992) (by norm_num : 132992 ≤ 133120), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_132608_133120 :
    (∑ n ∈ Ico 132608 133120, mobiusTreeValue 16 mobiusTable1200001 n) = (-28 : ℤ) ∧
    (∑ n ∈ Ico 132608 133120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 132608 133120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1054404 : ℤ) ∧
    (∑ n ∈ Ico 132608 133120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-21088353142006025509538262887 : ℤ) := by
  rcases cdemPrefixStats_132608_132864 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_132864_133120 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 132608 ≤ 132864) (by norm_num : 132864 ≤ 133120), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 132608 ≤ 132864) (by norm_num : 132864 ≤ 133120), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 132608 ≤ 132864) (by norm_num : 132864 ≤ 133120), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 132608 ≤ 132864) (by norm_num : 132864 ≤ 133120), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_132096_133120 :
    (∑ n ∈ Ico 132096 133120, mobiusTreeValue 16 mobiusTable1200001 n) = (-52 : ℤ) ∧
    (∑ n ∈ Ico 132096 133120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (620 : ℕ) ∧
    (∑ n ∈ Ico 132096 133120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1960949 : ℤ) ∧
    (∑ n ∈ Ico 132096 133120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-39219591816771077956321207818 : ℤ) := by
  rcases cdemPrefixStats_132096_132608 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_132608_133120 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 132096 ≤ 132608) (by norm_num : 132608 ≤ 133120), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 132096 ≤ 132608) (by norm_num : 132608 ≤ 133120), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 132096 ≤ 132608) (by norm_num : 132608 ≤ 133120), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 132096 ≤ 132608) (by norm_num : 132608 ≤ 133120), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_131072_133120 :
    (∑ n ∈ Ico 131072 133120, mobiusTreeValue 16 mobiusTable1200001 n) = (-24 : ℤ) ∧
    (∑ n ∈ Ico 131072 133120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1242 : ℕ) ∧
    (∑ n ∈ Ico 131072 133120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-895777 : ℤ) ∧
    (∑ n ∈ Ico 131072 133120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-17915724815505894820359268884 : ℤ) := by
  rcases cdemPrefixStats_131072_132096 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_132096_133120 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 131072 ≤ 132096) (by norm_num : 132096 ≤ 133120), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 131072 ≤ 132096) (by norm_num : 132096 ≤ 133120), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 131072 ≤ 132096) (by norm_num : 132096 ≤ 133120), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 131072 ≤ 132096) (by norm_num : 132096 ≤ 133120), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_133120_133184 :
    (∑ n ∈ Ico 133120 133184, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 133120 133184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 133120 133184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-37516 : ℤ) ∧
    (∑ n ∈ Ico 133120 133184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-750322002650868527323574114 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_133184_133248 :
    (∑ n ∈ Ico 133184 133248, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 133184 133248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 133184 133248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (225206 : ℤ) ∧
    (∑ n ∈ Ico 133184 133248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4504166456501944806160014829 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_133120_133248 :
    (∑ n ∈ Ico 133120 133248, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 133120 133248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 133120 133248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (187690 : ℤ) ∧
    (∑ n ∈ Ico 133120 133248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3753844453851076278836440715 : ℤ) := by
  rcases cdemPrefixStats_133120_133184 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_133184_133248 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 133120 ≤ 133184) (by norm_num : 133184 ≤ 133248), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 133120 ≤ 133184) (by norm_num : 133184 ≤ 133248), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 133120 ≤ 133184) (by norm_num : 133184 ≤ 133248), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 133120 ≤ 133184) (by norm_num : 133184 ≤ 133248), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_133248_133312 :
    (∑ n ∈ Ico 133248 133312, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 133248 133312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 133248 133312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-262623 : ℤ) ∧
    (∑ n ∈ Ico 133248 133312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5252494943109985987239033691 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_133312_133376 :
    (∑ n ∈ Ico 133312 133376, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 133312 133376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 133312 133376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (224959 : ℤ) ∧
    (∑ n ∈ Ico 133312 133376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4499235225435209740789134049 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_133248_133376 :
    (∑ n ∈ Ico 133248 133376, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 133248 133376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 133248 133376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-37664 : ℤ) ∧
    (∑ n ∈ Ico 133248 133376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-753259717674776246449899642 : ℤ) := by
  rcases cdemPrefixStats_133248_133312 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_133312_133376 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 133248 ≤ 133312) (by norm_num : 133312 ≤ 133376), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 133248 ≤ 133312) (by norm_num : 133312 ≤ 133376), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 133248 ≤ 133312) (by norm_num : 133312 ≤ 133376), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 133248 ≤ 133312) (by norm_num : 133312 ≤ 133376), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_133120_133376 :
    (∑ n ∈ Ico 133120 133376, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 133120 133376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 133120 133376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (150026 : ℤ) ∧
    (∑ n ∈ Ico 133120 133376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3000584736176300032386541073 : ℤ) := by
  rcases cdemPrefixStats_133120_133248 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_133248_133376 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 133120 ≤ 133248) (by norm_num : 133248 ≤ 133376), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 133120 ≤ 133248) (by norm_num : 133248 ≤ 133376), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 133120 ≤ 133248) (by norm_num : 133248 ≤ 133376), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 133120 ≤ 133248) (by norm_num : 133248 ≤ 133376), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_133376_133440 :
    (∑ n ∈ Ico 133376 133440, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 133376 133440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 133376 133440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-187423 : ℤ) ∧
    (∑ n ∈ Ico 133376 133440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3748463293269107982115560042 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_133440_133504 :
    (∑ n ∈ Ico 133440 133504, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 133440 133504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 133440 133504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (299623 : ℤ) ∧
    (∑ n ∈ Ico 133440 133504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5992565385715907665393148910 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_133376_133504 :
    (∑ n ∈ Ico 133376 133504, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 133376 133504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 133376 133504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (112200 : ℤ) ∧
    (∑ n ∈ Ico 133376 133504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2244102092446799683277588868 : ℤ) := by
  rcases cdemPrefixStats_133376_133440 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_133440_133504 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 133376 ≤ 133440) (by norm_num : 133440 ≤ 133504), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 133376 ≤ 133440) (by norm_num : 133440 ≤ 133504), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 133376 ≤ 133440) (by norm_num : 133440 ≤ 133504), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 133376 ≤ 133440) (by norm_num : 133440 ≤ 133504), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_133504_133568 :
    (∑ n ∈ Ico 133504 133568, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 133504 133568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 133504 133568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (74838 : ℤ) ∧
    (∑ n ∈ Ico 133504 133568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1496820732358293928078456551 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_133568_133632 :
    (∑ n ∈ Ico 133568 133632, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 133568 133632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 133568 133632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (37435 : ℤ) ∧
    (∑ n ∈ Ico 133568 133632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (748665410233724866013094093 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_133504_133632 :
    (∑ n ∈ Ico 133504 133632, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 133504 133632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 133504 133632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (112273 : ℤ) ∧
    (∑ n ∈ Ico 133504 133632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2245486142592018794091550644 : ℤ) := by
  rcases cdemPrefixStats_133504_133568 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_133568_133632 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 133504 ≤ 133568) (by norm_num : 133568 ≤ 133632), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 133504 ≤ 133568) (by norm_num : 133568 ≤ 133632), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 133504 ≤ 133568) (by norm_num : 133568 ≤ 133632), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 133504 ≤ 133568) (by norm_num : 133568 ≤ 133632), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_133376_133632 :
    (∑ n ∈ Ico 133376 133632, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 133376 133632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 133376 133632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (224473 : ℤ) ∧
    (∑ n ∈ Ico 133376 133632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4489588235038818477369139512 : ℤ) := by
  rcases cdemPrefixStats_133376_133504 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_133504_133632 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 133376 ≤ 133504) (by norm_num : 133504 ≤ 133632), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 133376 ≤ 133504) (by norm_num : 133504 ≤ 133632), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 133376 ≤ 133504) (by norm_num : 133504 ≤ 133632), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 133376 ≤ 133504) (by norm_num : 133504 ≤ 133632), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_133120_133632 :
    (∑ n ∈ Ico 133120 133632, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 133120 133632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 133120 133632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (374499 : ℤ) ∧
    (∑ n ∈ Ico 133120 133632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7490172971215118509755680585 : ℤ) := by
  rcases cdemPrefixStats_133120_133376 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_133376_133632 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 133120 ≤ 133376) (by norm_num : 133376 ≤ 133632), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 133120 ≤ 133376) (by norm_num : 133376 ≤ 133632), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 133120 ≤ 133376) (by norm_num : 133376 ≤ 133632), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 133120 ≤ 133376) (by norm_num : 133376 ≤ 133632), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_133632_133696 :
    (∑ n ∈ Ico 133632 133696, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 133632 133696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 133632 133696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-149646 : ℤ) ∧
    (∑ n ∈ Ico 133632 133696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2992981385799060016711518924 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_133696_133760 :
    (∑ n ∈ Ico 133696 133760, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 133696 133760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 133696 133760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (149481 : ℤ) ∧
    (∑ n ∈ Ico 133696 133760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2989642081000140216043662386 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_133632_133760 :
    (∑ n ∈ Ico 133632 133760, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 133632 133760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 133632 133760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-165 : ℤ) ∧
    (∑ n ∈ Ico 133632 133760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3339304798919800667856538 : ℤ) := by
  rcases cdemPrefixStats_133632_133696 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_133696_133760 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 133632 ≤ 133696) (by norm_num : 133696 ≤ 133760), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 133632 ≤ 133696) (by norm_num : 133696 ≤ 133760), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 133632 ≤ 133696) (by norm_num : 133696 ≤ 133760), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 133632 ≤ 133696) (by norm_num : 133696 ≤ 133760), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_133760_133824 :
    (∑ n ∈ Ico 133760 133824, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 133760 133824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 133760 133824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-37371 : ℤ) ∧
    (∑ n ∈ Ico 133760 133824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-747445689747425278642234109 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_133824_133888 :
    (∑ n ∈ Ico 133824 133888, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 133824 133888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 133824 133888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (261430 : ℤ) ∧
    (∑ n ∈ Ico 133824 133888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5228613031793609189014700056 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_133760_133888 :
    (∑ n ∈ Ico 133760 133888, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 133760 133888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 133760 133888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (224059 : ℤ) ∧
    (∑ n ∈ Ico 133760 133888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4481167342046183910372465947 : ℤ) := by
  rcases cdemPrefixStats_133760_133824 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_133824_133888 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 133760 ≤ 133824) (by norm_num : 133824 ≤ 133888), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 133760 ≤ 133824) (by norm_num : 133824 ≤ 133888), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 133760 ≤ 133824) (by norm_num : 133824 ≤ 133888), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 133760 ≤ 133824) (by norm_num : 133824 ≤ 133888), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_133632_133888 :
    (∑ n ∈ Ico 133632 133888, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 133632 133888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 133632 133888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (223894 : ℤ) ∧
    (∑ n ∈ Ico 133632 133888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4477828037247264109704609409 : ℤ) := by
  rcases cdemPrefixStats_133632_133760 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_133760_133888 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 133632 ≤ 133760) (by norm_num : 133760 ≤ 133888), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 133632 ≤ 133760) (by norm_num : 133760 ≤ 133888), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 133632 ≤ 133760) (by norm_num : 133760 ≤ 133888), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 133632 ≤ 133760) (by norm_num : 133760 ≤ 133888), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_133888_133952 :
    (∑ n ∈ Ico 133888 133952, mobiusTreeValue 16 mobiusTable1200001 n) = (18 : ℤ) ∧
    (∑ n ∈ Ico 133888 133952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 133888 133952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (672078 : ℤ) ∧
    (∑ n ∈ Ico 133888 133952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13441791559391562166728671942 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_133952_134016 :
    (∑ n ∈ Ico 133952 134016, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 133952 134016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 133952 134016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-74649 : ℤ) ∧
    (∑ n ∈ Ico 133952 134016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1493044114332472238808688640 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_133888_134016 :
    (∑ n ∈ Ico 133888 134016, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 133888 134016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 133888 134016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (597429 : ℤ) ∧
    (∑ n ∈ Ico 133888 134016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11948747445059089927919983302 : ℤ) := by
  rcases cdemPrefixStats_133888_133952 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_133952_134016 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 133888 ≤ 133952) (by norm_num : 133952 ≤ 134016), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 133888 ≤ 133952) (by norm_num : 133952 ≤ 134016), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 133888 ≤ 133952) (by norm_num : 133952 ≤ 134016), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 133888 ≤ 133952) (by norm_num : 133952 ≤ 134016), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_134016_134080 :
    (∑ n ∈ Ico 134016 134080, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 134016 134080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 134016 134080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (37300 : ℤ) ∧
    (∑ n ∈ Ico 134016 134080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (746018173160060611273510016 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_134080_134144 :
    (∑ n ∈ Ico 134080 134144, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 134080 134144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 134080 134144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (37262 : ℤ) ∧
    (∑ n ∈ Ico 134080 134144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (745284046882011270139289426 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_134016_134144 :
    (∑ n ∈ Ico 134016 134144, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 134016 134144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 134016 134144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (74562 : ℤ) ∧
    (∑ n ∈ Ico 134016 134144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1491302220042071881412799442 : ℤ) := by
  rcases cdemPrefixStats_134016_134080 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_134080_134144 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 134016 ≤ 134080) (by norm_num : 134080 ≤ 134144), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 134016 ≤ 134080) (by norm_num : 134080 ≤ 134144), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 134016 ≤ 134080) (by norm_num : 134080 ≤ 134144), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 134016 ≤ 134080) (by norm_num : 134080 ≤ 134144), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_133888_134144 :
    (∑ n ∈ Ico 133888 134144, mobiusTreeValue 16 mobiusTable1200001 n) = (18 : ℤ) ∧
    (∑ n ∈ Ico 133888 134144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 133888 134144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (671991 : ℤ) ∧
    (∑ n ∈ Ico 133888 134144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13440049665101161809332782744 : ℤ) := by
  rcases cdemPrefixStats_133888_134016 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_134016_134144 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 133888 ≤ 134016) (by norm_num : 134016 ≤ 134144), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 133888 ≤ 134016) (by norm_num : 134016 ≤ 134144), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 133888 ≤ 134016) (by norm_num : 134016 ≤ 134144), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 133888 ≤ 134016) (by norm_num : 134016 ≤ 134144), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_133632_134144 :
    (∑ n ∈ Ico 133632 134144, mobiusTreeValue 16 mobiusTable1200001 n) = (24 : ℤ) ∧
    (∑ n ∈ Ico 133632 134144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (314 : ℕ) ∧
    (∑ n ∈ Ico 133632 134144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (895885 : ℤ) ∧
    (∑ n ∈ Ico 133632 134144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17917877702348425919037392153 : ℤ) := by
  rcases cdemPrefixStats_133632_133888 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_133888_134144 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 133632 ≤ 133888) (by norm_num : 133888 ≤ 134144), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 133632 ≤ 133888) (by norm_num : 133888 ≤ 134144), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 133632 ≤ 133888) (by norm_num : 133888 ≤ 134144), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 133632 ≤ 133888) (by norm_num : 133888 ≤ 134144), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_133120_134144 :
    (∑ n ∈ Ico 133120 134144, mobiusTreeValue 16 mobiusTable1200001 n) = (34 : ℤ) ∧
    (∑ n ∈ Ico 133120 134144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (624 : ℕ) ∧
    (∑ n ∈ Ico 133120 134144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1270384 : ℤ) ∧
    (∑ n ∈ Ico 133120 134144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (25408050673563544428793072738 : ℤ) := by
  rcases cdemPrefixStats_133120_133632 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_133632_134144 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 133120 ≤ 133632) (by norm_num : 133632 ≤ 134144), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 133120 ≤ 133632) (by norm_num : 133632 ≤ 134144), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 133120 ≤ 133632) (by norm_num : 133632 ≤ 134144), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 133120 ≤ 133632) (by norm_num : 133632 ≤ 134144), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_134144_134208 :
    (∑ n ∈ Ico 134144 134208, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 134144 134208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 134144 134208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-335384 : ℤ) ∧
    (∑ n ∈ Ico 134144 134208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6707774602462426733001736335 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_134208_134272 :
    (∑ n ∈ Ico 134208 134272, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 134208 134272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 134208 134272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-260737 : ℤ) ∧
    (∑ n ∈ Ico 134208 134272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5214874200980172738702049508 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_134144_134272 :
    (∑ n ∈ Ico 134144 134272, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 134144 134272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 134144 134272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-596121 : ℤ) ∧
    (∑ n ∈ Ico 134144 134272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11922648803442599471703785843 : ℤ) := by
  rcases cdemPrefixStats_134144_134208 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_134208_134272 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 134144 ≤ 134208) (by norm_num : 134208 ≤ 134272), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 134144 ≤ 134208) (by norm_num : 134208 ≤ 134272), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 134144 ≤ 134208) (by norm_num : 134208 ≤ 134272), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 134144 ≤ 134208) (by norm_num : 134208 ≤ 134272), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_134272_134336 :
    (∑ n ∈ Ico 134272 134336, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 134272 134336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 134272 134336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (148912 : ℤ) ∧
    (∑ n ∈ Ico 134272 134336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2978245705878304914832178429 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_134336_134400 :
    (∑ n ∈ Ico 134336 134400, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 134336 134400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 134336 134400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-37286 : ℤ) ∧
    (∑ n ∈ Ico 134336 134400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-745781242208168129360591564 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_134272_134400 :
    (∑ n ∈ Ico 134272 134400, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 134272 134400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 134272 134400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (111626 : ℤ) ∧
    (∑ n ∈ Ico 134272 134400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2232464463670136785471586865 : ℤ) := by
  rcases cdemPrefixStats_134272_134336 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_134336_134400 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 134272 ≤ 134336) (by norm_num : 134336 ≤ 134400), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 134272 ≤ 134336) (by norm_num : 134336 ≤ 134400), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 134272 ≤ 134336) (by norm_num : 134336 ≤ 134400), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 134272 ≤ 134336) (by norm_num : 134336 ≤ 134400), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_134144_134400 :
    (∑ n ∈ Ico 134144 134400, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 134144 134400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 134144 134400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-484495 : ℤ) ∧
    (∑ n ∈ Ico 134144 134400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9690184339772462686232198978 : ℤ) := by
  rcases cdemPrefixStats_134144_134272 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_134272_134400 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 134144 ≤ 134272) (by norm_num : 134272 ≤ 134400), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 134144 ≤ 134272) (by norm_num : 134272 ≤ 134400), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 134144 ≤ 134272) (by norm_num : 134272 ≤ 134400), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 134144 ≤ 134272) (by norm_num : 134272 ≤ 134400), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_134400_134464 :
    (∑ n ∈ Ico 134400 134464, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 134400 134464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 134400 134464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (409108 : ℤ) ∧
    (∑ n ∈ Ico 134400 134464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8182243676013049051998001006 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_134464_134528 :
    (∑ n ∈ Ico 134464 134528, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 134464 134528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 134464 134528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (15 : ℤ) ∧
    (∑ n ∈ Ico 134464 134528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (188063610524959846420598 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_134400_134528 :
    (∑ n ∈ Ico 134400 134528, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 134400 134528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 134400 134528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (409123 : ℤ) ∧
    (∑ n ∈ Ico 134400 134528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8182431739623574011844421604 : ℤ) := by
  rcases cdemPrefixStats_134400_134464 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_134464_134528 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 134400 ≤ 134464) (by norm_num : 134464 ≤ 134528), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 134400 ≤ 134464) (by norm_num : 134464 ≤ 134528), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 134400 ≤ 134464) (by norm_num : 134464 ≤ 134528), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 134400 ≤ 134464) (by norm_num : 134464 ≤ 134528), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_134528_134592 :
    (∑ n ∈ Ico 134528 134592, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 134528 134592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 134528 134592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (37217 : ℤ) ∧
    (∑ n ∈ Ico 134528 134592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (744355842326752201323147135 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_134592_134656 :
    (∑ n ∈ Ico 134592 134656, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 134592 134656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 134592 134656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (185695 : ℤ) ∧
    (∑ n ∈ Ico 134592 134656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3713932104924977257120725984 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_134528_134656 :
    (∑ n ∈ Ico 134528 134656, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 134528 134656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 134528 134656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (222912 : ℤ) ∧
    (∑ n ∈ Ico 134528 134656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4458287947251729458443873119 : ℤ) := by
  rcases cdemPrefixStats_134528_134592 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_134592_134656 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 134528 ≤ 134592) (by norm_num : 134592 ≤ 134656), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 134528 ≤ 134592) (by norm_num : 134592 ≤ 134656), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 134528 ≤ 134592) (by norm_num : 134592 ≤ 134656), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 134528 ≤ 134592) (by norm_num : 134592 ≤ 134656), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_134400_134656 :
    (∑ n ∈ Ico 134400 134656, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 134400 134656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (159 : ℕ) ∧
    (∑ n ∈ Ico 134400 134656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (632035 : ℤ) ∧
    (∑ n ∈ Ico 134400 134656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12640719686875303470288294723 : ℤ) := by
  rcases cdemPrefixStats_134400_134528 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_134528_134656 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 134400 ≤ 134528) (by norm_num : 134528 ≤ 134656), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 134400 ≤ 134528) (by norm_num : 134528 ≤ 134656), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 134400 ≤ 134528) (by norm_num : 134528 ≤ 134656), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 134400 ≤ 134528) (by norm_num : 134528 ≤ 134656), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_134144_134656 :
    (∑ n ∈ Ico 134144 134656, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 134144 134656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 134144 134656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (147540 : ℤ) ∧
    (∑ n ∈ Ico 134144 134656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2950535347102840784056095745 : ℤ) := by
  rcases cdemPrefixStats_134144_134400 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_134400_134656 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 134144 ≤ 134400) (by norm_num : 134400 ≤ 134656), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 134144 ≤ 134400) (by norm_num : 134400 ≤ 134656), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 134144 ≤ 134400) (by norm_num : 134400 ≤ 134656), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 134144 ≤ 134400) (by norm_num : 134400 ≤ 134656), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_134656_134720 :
    (∑ n ∈ Ico 134656 134720, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 134656 134720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (35 : ℕ) ∧
    (∑ n ∈ Ico 134656 134720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-259826 : ℤ) ∧
    (∑ n ∈ Ico 134656 134720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5196595723504927614725312575 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_134720_134784 :
    (∑ n ∈ Ico 134720 134784, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 134720 134784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 134720 134784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (333943 : ℤ) ∧
    (∑ n ∈ Ico 134720 134784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6678936259031189052256880701 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_134656_134784 :
    (∑ n ∈ Ico 134656 134784, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 134656 134784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (74 : ℕ) ∧
    (∑ n ∈ Ico 134656 134784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (74117 : ℤ) ∧
    (∑ n ∈ Ico 134656 134784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1482340535526261437531568126 : ℤ) := by
  rcases cdemPrefixStats_134656_134720 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_134720_134784 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 134656 ≤ 134720) (by norm_num : 134720 ≤ 134784), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 134656 ≤ 134720) (by norm_num : 134720 ≤ 134784), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 134656 ≤ 134720) (by norm_num : 134720 ≤ 134784), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 134656 ≤ 134720) (by norm_num : 134720 ≤ 134784), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_134784_134848 :
    (∑ n ∈ Ico 134784 134848, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 134784 134848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 134784 134848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (111271 : ℤ) ∧
    (∑ n ∈ Ico 134784 134848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2225486110492738716872791729 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_134848_134912 :
    (∑ n ∈ Ico 134848 134912, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 134848 134912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 134848 134912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (74138 : ℤ) ∧
    (∑ n ∈ Ico 134848 134912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1482766614361870189693087590 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_134784_134912 :
    (∑ n ∈ Ico 134784 134912, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 134784 134912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 134784 134912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (185409 : ℤ) ∧
    (∑ n ∈ Ico 134784 134912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3708252724854608906565879319 : ℤ) := by
  rcases cdemPrefixStats_134784_134848 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_134848_134912 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 134784 ≤ 134848) (by norm_num : 134848 ≤ 134912), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 134784 ≤ 134848) (by norm_num : 134848 ≤ 134912), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 134784 ≤ 134848) (by norm_num : 134848 ≤ 134912), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 134784 ≤ 134848) (by norm_num : 134848 ≤ 134912), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_134656_134912 :
    (∑ n ∈ Ico 134656 134912, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 134656 134912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (151 : ℕ) ∧
    (∑ n ∈ Ico 134656 134912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (259526 : ℤ) ∧
    (∑ n ∈ Ico 134656 134912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5190593260380870344097447445 : ℤ) := by
  rcases cdemPrefixStats_134656_134784 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_134784_134912 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 134656 ≤ 134784) (by norm_num : 134784 ≤ 134912), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 134656 ≤ 134784) (by norm_num : 134784 ≤ 134912), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 134656 ≤ 134784) (by norm_num : 134784 ≤ 134912), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 134656 ≤ 134784) (by norm_num : 134784 ≤ 134912), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_134912_134976 :
    (∑ n ∈ Ico 134912 134976, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 134912 134976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 134912 134976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (222269 : ℤ) ∧
    (∑ n ∈ Ico 134912 134976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4445421277628272974018105819 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_134976_135040 :
    (∑ n ∈ Ico 134976 135040, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 134976 135040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 134976 135040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-222179 : ℤ) ∧
    (∑ n ∈ Ico 134976 135040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4443638041840506211895458818 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_134912_135040 :
    (∑ n ∈ Ico 134912 135040, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 134912 135040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 134912 135040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (90 : ℤ) ∧
    (∑ n ∈ Ico 134912 135040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1783235787766762122647001 : ℤ) := by
  rcases cdemPrefixStats_134912_134976 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_134976_135040 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 134912 ≤ 134976) (by norm_num : 134976 ≤ 135040), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 134912 ≤ 134976) (by norm_num : 134976 ≤ 135040), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 134912 ≤ 134976) (by norm_num : 134976 ≤ 135040), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 134912 ≤ 134976) (by norm_num : 134976 ≤ 135040), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_135040_135104 :
    (∑ n ∈ Ico 135040 135104, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 135040 135104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 135040 135104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (333195 : ℤ) ∧
    (∑ n ∈ Ico 135040 135104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6663968145283132252179347007 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_135104_135168 :
    (∑ n ∈ Ico 135104 135168, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 135104 135168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 135104 135168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-185034 : ℤ) ∧
    (∑ n ∈ Ico 135104 135168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3700693763880018822008440742 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_135040_135168 :
    (∑ n ∈ Ico 135040 135168, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 135040 135168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 135040 135168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (148161 : ℤ) ∧
    (∑ n ∈ Ico 135040 135168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2963274381403113430170906265 : ℤ) := by
  rcases cdemPrefixStats_135040_135104 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_135104_135168 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 135040 ≤ 135104) (by norm_num : 135104 ≤ 135168), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 135040 ≤ 135104) (by norm_num : 135104 ≤ 135168), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 135040 ≤ 135104) (by norm_num : 135104 ≤ 135168), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 135040 ≤ 135104) (by norm_num : 135104 ≤ 135168), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_134912_135168 :
    (∑ n ∈ Ico 134912 135168, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 134912 135168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 134912 135168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (148251 : ℤ) ∧
    (∑ n ∈ Ico 134912 135168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2965057617190880192293553266 : ℤ) := by
  rcases cdemPrefixStats_134912_135040 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_135040_135168 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 134912 ≤ 135040) (by norm_num : 135040 ≤ 135168), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 134912 ≤ 135040) (by norm_num : 135040 ≤ 135168), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 134912 ≤ 135040) (by norm_num : 135040 ≤ 135168), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 134912 ≤ 135040) (by norm_num : 135040 ≤ 135168), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_134656_135168 :
    (∑ n ∈ Ico 134656 135168, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 134656 135168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (305 : ℕ) ∧
    (∑ n ∈ Ico 134656 135168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (407777 : ℤ) ∧
    (∑ n ∈ Ico 134656 135168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8155650877571750536391000711 : ℤ) := by
  rcases cdemPrefixStats_134656_134912 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_134912_135168 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 134656 ≤ 134912) (by norm_num : 134912 ≤ 135168), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 134656 ≤ 134912) (by norm_num : 134912 ≤ 135168), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 134656 ≤ 134912) (by norm_num : 134912 ≤ 135168), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 134656 ≤ 134912) (by norm_num : 134912 ≤ 135168), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_134144_135168 :
    (∑ n ∈ Ico 134144 135168, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 134144 135168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (617 : ℕ) ∧
    (∑ n ∈ Ico 134144 135168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (555317 : ℤ) ∧
    (∑ n ∈ Ico 134144 135168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11106186224674591320447096456 : ℤ) := by
  rcases cdemPrefixStats_134144_134656 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_134656_135168 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 134144 ≤ 134656) (by norm_num : 134656 ≤ 135168), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 134144 ≤ 134656) (by norm_num : 134656 ≤ 135168), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 134144 ≤ 134656) (by norm_num : 134656 ≤ 135168), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 134144 ≤ 134656) (by norm_num : 134656 ≤ 135168), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_133120_135168 :
    (∑ n ∈ Ico 133120 135168, mobiusTreeValue 16 mobiusTable1200001 n) = (49 : ℤ) ∧
    (∑ n ∈ Ico 133120 135168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1241 : ℕ) ∧
    (∑ n ∈ Ico 133120 135168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1825701 : ℤ) ∧
    (∑ n ∈ Ico 133120 135168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (36514236898238135749240169194 : ℤ) := by
  rcases cdemPrefixStats_133120_134144 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_134144_135168 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 133120 ≤ 134144) (by norm_num : 134144 ≤ 135168), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 133120 ≤ 134144) (by norm_num : 134144 ≤ 135168), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 133120 ≤ 134144) (by norm_num : 134144 ≤ 135168), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 133120 ≤ 134144) (by norm_num : 134144 ≤ 135168), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_131072_135168 :
    (∑ n ∈ Ico 131072 135168, mobiusTreeValue 16 mobiusTable1200001 n) = (25 : ℤ) ∧
    (∑ n ∈ Ico 131072 135168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2483 : ℕ) ∧
    (∑ n ∈ Ico 131072 135168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (929924 : ℤ) ∧
    (∑ n ∈ Ico 131072 135168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18598512082732240928880900310 : ℤ) := by
  rcases cdemPrefixStats_131072_133120 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_133120_135168 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 131072 ≤ 133120) (by norm_num : 133120 ≤ 135168), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 131072 ≤ 133120) (by norm_num : 133120 ≤ 135168), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 131072 ≤ 133120) (by norm_num : 133120 ≤ 135168), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 131072 ≤ 133120) (by norm_num : 133120 ≤ 135168), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup032_checked_complete :
    (∑ n ∈ Ico 131072 135168, mobiusTreeValue 16 mobiusTable1200001 n) = (25 : ℤ) ∧
    (∑ n ∈ Ico 131072 135168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2483 : ℕ) ∧
    (∑ n ∈ Ico 131072 135168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (929924 : ℤ) ∧
    (∑ n ∈ Ico 131072 135168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18598512082732240928880900310 : ℤ) := cdemPrefixStats_131072_135168
end Helfgott
#print axioms Helfgott.cdemPrefixGroup032_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 131072 135168, mobiusTreeValue 16 mobiusTable1200001 n) = (25 : ℤ) ∧
    (∑ n ∈ Ico 131072 135168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2483 : ℕ) ∧
    (∑ n ∈ Ico 131072 135168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (929924 : ℤ) ∧
    (∑ n ∈ Ico 131072 135168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18598512082732240928880900310 : ℤ) := Helfgott.cdemPrefixGroup032_checked_complete
#print axioms solution
