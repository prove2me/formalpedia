-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup011_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:35:43.790321+00:00
-- url     : https://prove2.me/submissions/5a74b26c-90b5-4dff-82f4-f3879f965caf

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
private theorem cdemPrefixStats_45056_45120 :
    (∑ n ∈ Ico 45056 45120, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 45056 45120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 45056 45120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-443883 : ℤ) ∧
    (∑ n ∈ Ico 45056 45120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8877694243747134118290204001 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_45120_45184 :
    (∑ n ∈ Ico 45120 45184, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 45120 45184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (34 : ℕ) ∧
    (∑ n ∈ Ico 45120 45184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-664561 : ℤ) ∧
    (∑ n ∈ Ico 45120 45184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13291294868196900830211379850 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_45056_45184 :
    (∑ n ∈ Ico 45056 45184, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 45056 45184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 45056 45184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1108444 : ℤ) ∧
    (∑ n ∈ Ico 45056 45184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-22168989111944034948501583851 : ℤ) := by
  rcases cdemPrefixStats_45056_45120 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_45120_45184 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 45056 ≤ 45120) (by norm_num : 45120 ≤ 45184), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 45056 ≤ 45120) (by norm_num : 45120 ≤ 45184), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 45056 ≤ 45120) (by norm_num : 45120 ≤ 45184), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 45056 ≤ 45120) (by norm_num : 45120 ≤ 45184), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_45184_45248 :
    (∑ n ∈ Ico 45184 45248, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 45184 45248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 45184 45248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (331728 : ℤ) ∧
    (∑ n ∈ Ico 45184 45248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6634573743167520298455220531 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_45248_45312 :
    (∑ n ∈ Ico 45248 45312, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 45248 45312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 45248 45312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (772912 : ℤ) ∧
    (∑ n ∈ Ico 45248 45312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15458345395078237162363652317 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_45184_45312 :
    (∑ n ∈ Ico 45184 45312, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 45184 45312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 45184 45312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1104640 : ℤ) ∧
    (∑ n ∈ Ico 45184 45312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (22092919138245757460818872848 : ℤ) := by
  rcases cdemPrefixStats_45184_45248 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_45248_45312 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 45184 ≤ 45248) (by norm_num : 45248 ≤ 45312), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 45184 ≤ 45248) (by norm_num : 45248 ≤ 45312), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 45184 ≤ 45248) (by norm_num : 45248 ≤ 45312), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 45184 ≤ 45248) (by norm_num : 45248 ≤ 45312), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_45056_45312 :
    (∑ n ∈ Ico 45056 45312, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 45056 45312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 45056 45312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3804 : ℤ) ∧
    (∑ n ∈ Ico 45056 45312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-76069973698277487682711003 : ℤ) := by
  rcases cdemPrefixStats_45056_45184 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_45184_45312 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 45056 ≤ 45184) (by norm_num : 45184 ≤ 45312), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 45056 ≤ 45184) (by norm_num : 45184 ≤ 45312), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 45056 ≤ 45184) (by norm_num : 45184 ≤ 45312), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 45056 ≤ 45184) (by norm_num : 45184 ≤ 45312), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_45312_45376 :
    (∑ n ∈ Ico 45312 45376, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 45312 45376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 45312 45376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-220755 : ℤ) ∧
    (∑ n ∈ Ico 45312 45376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4415153259346444790149873007 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_45376_45440 :
    (∑ n ∈ Ico 45376 45440, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 45376 45440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 45376 45440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-37 : ℤ) ∧
    (∑ n ∈ Ico 45376 45440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-777099200263226275411202 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_45312_45440 :
    (∑ n ∈ Ico 45312 45440, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 45312 45440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 45312 45440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-220792 : ℤ) ∧
    (∑ n ∈ Ico 45312 45440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4415930358546708016425284209 : ℤ) := by
  rcases cdemPrefixStats_45312_45376 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_45376_45440 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 45312 ≤ 45376) (by norm_num : 45376 ≤ 45440), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 45312 ≤ 45376) (by norm_num : 45376 ≤ 45440), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 45312 ≤ 45376) (by norm_num : 45376 ≤ 45440), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 45312 ≤ 45376) (by norm_num : 45376 ≤ 45440), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_45440_45504 :
    (∑ n ∈ Ico 45440 45504, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 45440 45504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 45440 45504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-109472 : ℤ) ∧
    (∑ n ∈ Ico 45440 45504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2189483977008294065549318596 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_45504_45568 :
    (∑ n ∈ Ico 45504 45568, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 45504 45568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 45504 45568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-109742 : ℤ) ∧
    (∑ n ∈ Ico 45504 45568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2194810458328583470105387580 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_45440_45568 :
    (∑ n ∈ Ico 45440 45568, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 45440 45568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 45440 45568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-219214 : ℤ) ∧
    (∑ n ∈ Ico 45440 45568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4384294435336877535654706176 : ℤ) := by
  rcases cdemPrefixStats_45440_45504 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_45504_45568 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 45440 ≤ 45504) (by norm_num : 45504 ≤ 45568), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 45440 ≤ 45504) (by norm_num : 45504 ≤ 45568), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 45440 ≤ 45504) (by norm_num : 45504 ≤ 45568), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 45440 ≤ 45504) (by norm_num : 45504 ≤ 45568), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_45312_45568 :
    (∑ n ∈ Ico 45312 45568, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 45312 45568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 45312 45568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-440006 : ℤ) ∧
    (∑ n ∈ Ico 45312 45568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8800224793883585552079990385 : ℤ) := by
  rcases cdemPrefixStats_45312_45440 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_45440_45568 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 45312 ≤ 45440) (by norm_num : 45440 ≤ 45568), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 45312 ≤ 45440) (by norm_num : 45440 ≤ 45568), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 45312 ≤ 45440) (by norm_num : 45440 ≤ 45568), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 45312 ≤ 45440) (by norm_num : 45440 ≤ 45568), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_45056_45568 :
    (∑ n ∈ Ico 45056 45568, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 45056 45568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (314 : ℕ) ∧
    (∑ n ∈ Ico 45056 45568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-443810 : ℤ) ∧
    (∑ n ∈ Ico 45056 45568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8876294767581863039762701388 : ℤ) := by
  rcases cdemPrefixStats_45056_45312 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_45312_45568 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 45056 ≤ 45312) (by norm_num : 45312 ≤ 45568), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 45056 ≤ 45312) (by norm_num : 45312 ≤ 45568), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 45056 ≤ 45312) (by norm_num : 45312 ≤ 45568), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 45056 ≤ 45312) (by norm_num : 45312 ≤ 45568), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_45568_45632 :
    (∑ n ∈ Ico 45568 45632, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 45568 45632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 45568 45632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-109528 : ℤ) ∧
    (∑ n ∈ Ico 45568 45632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2190530917984209954783375100 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_45632_45696 :
    (∑ n ∈ Ico 45632 45696, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 45632 45696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 45632 45696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (328616 : ℤ) ∧
    (∑ n ∈ Ico 45632 45696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6572321218150920002549679576 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_45568_45696 :
    (∑ n ∈ Ico 45568 45696, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 45568 45696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 45568 45696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (219088 : ℤ) ∧
    (∑ n ∈ Ico 45568 45696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4381790300166710047766304476 : ℤ) := by
  rcases cdemPrefixStats_45568_45632 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_45632_45696 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 45568 ≤ 45632) (by norm_num : 45632 ≤ 45696), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 45568 ≤ 45632) (by norm_num : 45632 ≤ 45696), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 45568 ≤ 45632) (by norm_num : 45632 ≤ 45696), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 45568 ≤ 45632) (by norm_num : 45632 ≤ 45696), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_45696_45760 :
    (∑ n ∈ Ico 45696 45760, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 45696 45760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 45696 45760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (437924 : ℤ) ∧
    (∑ n ∈ Ico 45696 45760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8758518187653726815597387017 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_45760_45824 :
    (∑ n ∈ Ico 45760 45824, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 45760 45824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 45760 45824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1091920 : ℤ) ∧
    (∑ n ∈ Ico 45760 45824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (21838496926401040356463941411 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_45696_45824 :
    (∑ n ∈ Ico 45696 45824, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 45696 45824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 45696 45824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1529844 : ℤ) ∧
    (∑ n ∈ Ico 45696 45824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (30597015114054767172061328428 : ℤ) := by
  rcases cdemPrefixStats_45696_45760 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_45760_45824 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 45696 ≤ 45760) (by norm_num : 45760 ≤ 45824), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 45696 ≤ 45760) (by norm_num : 45760 ≤ 45824), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 45696 ≤ 45760) (by norm_num : 45760 ≤ 45824), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 45696 ≤ 45760) (by norm_num : 45760 ≤ 45824), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_45568_45824 :
    (∑ n ∈ Ico 45568 45824, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 45568 45824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 45568 45824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1748932 : ℤ) ∧
    (∑ n ∈ Ico 45568 45824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (34978805414221477219827632904 : ℤ) := by
  rcases cdemPrefixStats_45568_45696 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_45696_45824 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 45568 ≤ 45696) (by norm_num : 45696 ≤ 45824), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 45568 ≤ 45696) (by norm_num : 45696 ≤ 45824), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 45568 ≤ 45696) (by norm_num : 45696 ≤ 45824), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 45568 ≤ 45696) (by norm_num : 45696 ≤ 45824), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_45824_45888 :
    (∑ n ∈ Ico 45824 45888, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 45824 45888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 45824 45888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-179 : ℤ) ∧
    (∑ n ∈ Ico 45824 45888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3568590141266297494915165 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_45888_45952 :
    (∑ n ∈ Ico 45888 45952, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 45888 45952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 45888 45952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (979801 : ℤ) ∧
    (∑ n ∈ Ico 45888 45952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (19596126965833221947910282051 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_45824_45952 :
    (∑ n ∈ Ico 45824 45952, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 45824 45952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 45824 45952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (979622 : ℤ) ∧
    (∑ n ∈ Ico 45824 45952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (19592558375691955650415366886 : ℤ) := by
  rcases cdemPrefixStats_45824_45888 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_45888_45952 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 45824 ≤ 45888) (by norm_num : 45888 ≤ 45952), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 45824 ≤ 45888) (by norm_num : 45888 ≤ 45952), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 45824 ≤ 45888) (by norm_num : 45888 ≤ 45952), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 45824 ≤ 45888) (by norm_num : 45888 ≤ 45952), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_45952_46016 :
    (∑ n ∈ Ico 45952 46016, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 45952 46016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 45952 46016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (434644 : ℤ) ∧
    (∑ n ∈ Ico 45952 46016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8692861517421463979557734662 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_46016_46080 :
    (∑ n ∈ Ico 46016 46080, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 46016 46080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 46016 46080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (651457 : ℤ) ∧
    (∑ n ∈ Ico 46016 46080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13029177941859786710104490499 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_45952_46080 :
    (∑ n ∈ Ico 45952 46080, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 45952 46080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 45952 46080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1086101 : ℤ) ∧
    (∑ n ∈ Ico 45952 46080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (21722039459281250689662225161 : ℤ) := by
  rcases cdemPrefixStats_45952_46016 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_46016_46080 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 45952 ≤ 46016) (by norm_num : 46016 ≤ 46080), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 45952 ≤ 46016) (by norm_num : 46016 ≤ 46080), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 45952 ≤ 46016) (by norm_num : 46016 ≤ 46080), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 45952 ≤ 46016) (by norm_num : 46016 ≤ 46080), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_45824_46080 :
    (∑ n ∈ Ico 45824 46080, mobiusTreeValue 16 mobiusTable1200001 n) = (19 : ℤ) ∧
    (∑ n ∈ Ico 45824 46080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 45824 46080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2065723 : ℤ) ∧
    (∑ n ∈ Ico 45824 46080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (41314597834973206340077592047 : ℤ) := by
  rcases cdemPrefixStats_45824_45952 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_45952_46080 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 45824 ≤ 45952) (by norm_num : 45952 ≤ 46080), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 45824 ≤ 45952) (by norm_num : 45952 ≤ 46080), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 45824 ≤ 45952) (by norm_num : 45952 ≤ 46080), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 45824 ≤ 45952) (by norm_num : 45952 ≤ 46080), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_45568_46080 :
    (∑ n ∈ Ico 45568 46080, mobiusTreeValue 16 mobiusTable1200001 n) = (35 : ℤ) ∧
    (∑ n ∈ Ico 45568 46080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 45568 46080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3814655 : ℤ) ∧
    (∑ n ∈ Ico 45568 46080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (76293403249194683559905224951 : ℤ) := by
  rcases cdemPrefixStats_45568_45824 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_45824_46080 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 45568 ≤ 45824) (by norm_num : 45824 ≤ 46080), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 45568 ≤ 45824) (by norm_num : 45824 ≤ 46080), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 45568 ≤ 45824) (by norm_num : 45824 ≤ 46080), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 45568 ≤ 45824) (by norm_num : 45824 ≤ 46080), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_45056_46080 :
    (∑ n ∈ Ico 45056 46080, mobiusTreeValue 16 mobiusTable1200001 n) = (31 : ℤ) ∧
    (∑ n ∈ Ico 45056 46080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (625 : ℕ) ∧
    (∑ n ∈ Ico 45056 46080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3370845 : ℤ) ∧
    (∑ n ∈ Ico 45056 46080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (67417108481612820520142523563 : ℤ) := by
  rcases cdemPrefixStats_45056_45568 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_45568_46080 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 45056 ≤ 45568) (by norm_num : 45568 ≤ 46080), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 45056 ≤ 45568) (by norm_num : 45568 ≤ 46080), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 45056 ≤ 45568) (by norm_num : 45568 ≤ 46080), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 45056 ≤ 45568) (by norm_num : 45568 ≤ 46080), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_46080_46144 :
    (∑ n ∈ Ico 46080 46144, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 46080 46144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 46080 46144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (758797 : ℤ) ∧
    (∑ n ∈ Ico 46080 46144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15176057777280728535118480264 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_46144_46208 :
    (∑ n ∈ Ico 46144 46208, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 46144 46208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 46144 46208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-325183 : ℤ) ∧
    (∑ n ∈ Ico 46144 46208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6503683093320859192287563124 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_46080_46208 :
    (∑ n ∈ Ico 46080 46208, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 46080 46208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 46080 46208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (433614 : ℤ) ∧
    (∑ n ∈ Ico 46080 46208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8672374683959869342830917140 : ℤ) := by
  rcases cdemPrefixStats_46080_46144 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_46144_46208 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 46080 ≤ 46144) (by norm_num : 46144 ≤ 46208), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 46080 ≤ 46144) (by norm_num : 46144 ≤ 46208), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 46080 ≤ 46144) (by norm_num : 46144 ≤ 46208), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 46080 ≤ 46144) (by norm_num : 46144 ≤ 46208), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_46208_46272 :
    (∑ n ∈ Ico 46208 46272, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 46208 46272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 46208 46272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-108322 : ℤ) ∧
    (∑ n ∈ Ico 46208 46272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2166465675138235027476522013 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_46272_46336 :
    (∑ n ∈ Ico 46272 46336, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 46272 46336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 46272 46336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (215480 : ℤ) ∧
    (∑ n ∈ Ico 46272 46336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4309628062506777770144042984 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_46208_46336 :
    (∑ n ∈ Ico 46208 46336, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 46208 46336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 46208 46336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (107158 : ℤ) ∧
    (∑ n ∈ Ico 46208 46336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2143162387368542742667520971 : ℤ) := by
  rcases cdemPrefixStats_46208_46272 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_46272_46336 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 46208 ≤ 46272) (by norm_num : 46272 ≤ 46336), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 46208 ≤ 46272) (by norm_num : 46272 ≤ 46336), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 46208 ≤ 46272) (by norm_num : 46272 ≤ 46336), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 46208 ≤ 46272) (by norm_num : 46272 ≤ 46336), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_46080_46336 :
    (∑ n ∈ Ico 46080 46336, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 46080 46336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 46080 46336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (540772 : ℤ) ∧
    (∑ n ∈ Ico 46080 46336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10815537071328412085498438111 : ℤ) := by
  rcases cdemPrefixStats_46080_46208 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_46208_46336 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 46080 ≤ 46208) (by norm_num : 46208 ≤ 46336), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 46080 ≤ 46208) (by norm_num : 46208 ≤ 46336), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 46080 ≤ 46208) (by norm_num : 46208 ≤ 46336), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 46080 ≤ 46208) (by norm_num : 46208 ≤ 46336), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_46336_46400 :
    (∑ n ∈ Ico 46336 46400, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 46336 46400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 46336 46400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (431235 : ℤ) ∧
    (∑ n ∈ Ico 46336 46400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8624731117569376996983152068 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_46400_46464 :
    (∑ n ∈ Ico 46400 46464, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 46400 46464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 46400 46464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (562 : ℤ) ∧
    (∑ n ∈ Ico 46400 46464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11273349991736707595795038 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_46336_46464 :
    (∑ n ∈ Ico 46336 46464, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 46336 46464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 46336 46464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (431797 : ℤ) ∧
    (∑ n ∈ Ico 46336 46464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8636004467561113704578947106 : ℤ) := by
  rcases cdemPrefixStats_46336_46400 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_46400_46464 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 46336 ≤ 46400) (by norm_num : 46400 ≤ 46464), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 46336 ≤ 46400) (by norm_num : 46400 ≤ 46464), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 46336 ≤ 46400) (by norm_num : 46400 ≤ 46464), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 46336 ≤ 46400) (by norm_num : 46400 ≤ 46464), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_46464_46528 :
    (∑ n ∈ Ico 46464 46528, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 46464 46528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 46464 46528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1290242 : ℤ) ∧
    (∑ n ∈ Ico 46464 46528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-25804928623598647118135791215 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_46528_46592 :
    (∑ n ∈ Ico 46528 46592, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 46528 46592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 46528 46592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (429343 : ℤ) ∧
    (∑ n ∈ Ico 46528 46592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8586914705597324948592534068 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_46464_46592 :
    (∑ n ∈ Ico 46464 46592, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 46464 46592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 46464 46592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-860899 : ℤ) ∧
    (∑ n ∈ Ico 46464 46592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-17218013918001322169543257147 : ℤ) := by
  rcases cdemPrefixStats_46464_46528 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_46528_46592 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 46464 ≤ 46528) (by norm_num : 46528 ≤ 46592), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 46464 ≤ 46528) (by norm_num : 46528 ≤ 46592), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 46464 ≤ 46528) (by norm_num : 46528 ≤ 46592), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 46464 ≤ 46528) (by norm_num : 46528 ≤ 46592), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_46336_46592 :
    (∑ n ∈ Ico 46336 46592, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 46336 46592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 46336 46592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-429102 : ℤ) ∧
    (∑ n ∈ Ico 46336 46592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8582009450440208464964310041 : ℤ) := by
  rcases cdemPrefixStats_46336_46464 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_46464_46592 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 46336 ≤ 46464) (by norm_num : 46464 ≤ 46592), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 46336 ≤ 46464) (by norm_num : 46464 ≤ 46592), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 46336 ≤ 46464) (by norm_num : 46464 ≤ 46592), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 46336 ≤ 46464) (by norm_num : 46464 ≤ 46592), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_46080_46592 :
    (∑ n ∈ Ico 46080 46592, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 46080 46592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 46080 46592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (111670 : ℤ) ∧
    (∑ n ∈ Ico 46080 46592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2233527620888203620534128070 : ℤ) := by
  rcases cdemPrefixStats_46080_46336 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_46336_46592 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 46080 ≤ 46336) (by norm_num : 46336 ≤ 46592), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 46080 ≤ 46336) (by norm_num : 46336 ≤ 46592), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 46080 ≤ 46336) (by norm_num : 46336 ≤ 46592), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 46080 ≤ 46336) (by norm_num : 46336 ≤ 46592), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_46592_46656 :
    (∑ n ∈ Ico 46592 46656, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 46592 46656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 46592 46656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (536455 : ℤ) ∧
    (∑ n ∈ Ico 46592 46656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10729154100683367545884227817 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_46656_46720 :
    (∑ n ∈ Ico 46656 46720, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 46656 46720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 46656 46720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-107437 : ℤ) ∧
    (∑ n ∈ Ico 46656 46720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2148759799409320735714277922 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_46592_46720 :
    (∑ n ∈ Ico 46592 46720, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 46592 46720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 46592 46720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (429018 : ℤ) ∧
    (∑ n ∈ Ico 46592 46720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8580394301274046810169949895 : ℤ) := by
  rcases cdemPrefixStats_46592_46656 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_46656_46720 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 46592 ≤ 46656) (by norm_num : 46656 ≤ 46720), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 46592 ≤ 46656) (by norm_num : 46656 ≤ 46720), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 46592 ≤ 46656) (by norm_num : 46656 ≤ 46720), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 46592 ≤ 46656) (by norm_num : 46656 ≤ 46720), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_46720_46784 :
    (∑ n ∈ Ico 46720 46784, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 46720 46784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 46720 46784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-427733 : ℤ) ∧
    (∑ n ∈ Ico 46720 46784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8554732633929302022225998148 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_46784_46848 :
    (∑ n ∈ Ico 46784 46848, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 46784 46848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 46784 46848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-213667 : ℤ) ∧
    (∑ n ∈ Ico 46784 46848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4273366690926643528847845760 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_46720_46848 :
    (∑ n ∈ Ico 46720 46848, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 46720 46848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 46720 46848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-641400 : ℤ) ∧
    (∑ n ∈ Ico 46720 46848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12828099324855945551073843908 : ℤ) := by
  rcases cdemPrefixStats_46720_46784 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_46784_46848 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 46720 ≤ 46784) (by norm_num : 46784 ≤ 46848), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 46720 ≤ 46784) (by norm_num : 46784 ≤ 46848), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 46720 ≤ 46784) (by norm_num : 46784 ≤ 46848), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 46720 ≤ 46784) (by norm_num : 46784 ≤ 46848), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_46592_46848 :
    (∑ n ∈ Ico 46592 46848, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 46592 46848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 46592 46848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-212382 : ℤ) ∧
    (∑ n ∈ Ico 46592 46848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4247705023581898740903894013 : ℤ) := by
  rcases cdemPrefixStats_46592_46720 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_46720_46848 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 46592 ≤ 46720) (by norm_num : 46720 ≤ 46848), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 46592 ≤ 46720) (by norm_num : 46720 ≤ 46848), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 46592 ≤ 46720) (by norm_num : 46720 ≤ 46848), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 46592 ≤ 46720) (by norm_num : 46720 ≤ 46848), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_46848_46912 :
    (∑ n ∈ Ico 46848 46912, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 46848 46912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 46848 46912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (426973 : ℤ) ∧
    (∑ n ∈ Ico 46848 46912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8539476666679089181408772070 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_46912_46976 :
    (∑ n ∈ Ico 46912 46976, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 46912 46976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 46912 46976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (319649 : ℤ) ∧
    (∑ n ∈ Ico 46912 46976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6392955051746180256046073329 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_46848_46976 :
    (∑ n ∈ Ico 46848 46976, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 46848 46976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 46848 46976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (746622 : ℤ) ∧
    (∑ n ∈ Ico 46848 46976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14932431718425269437454845399 : ℤ) := by
  rcases cdemPrefixStats_46848_46912 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_46912_46976 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 46848 ≤ 46912) (by norm_num : 46912 ≤ 46976), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 46848 ≤ 46912) (by norm_num : 46912 ≤ 46976), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 46848 ≤ 46912) (by norm_num : 46912 ≤ 46976), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 46848 ≤ 46912) (by norm_num : 46912 ≤ 46976), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_46976_47040 :
    (∑ n ∈ Ico 46976 47040, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 46976 47040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 46976 47040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1170259 : ℤ) ∧
    (∑ n ∈ Ico 46976 47040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (23405252477714463139141053306 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_47040_47104 :
    (∑ n ∈ Ico 47040 47104, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 47040 47104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 47040 47104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-106414 : ℤ) ∧
    (∑ n ∈ Ico 47040 47104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2128334843712589351020697080 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_46976_47104 :
    (∑ n ∈ Ico 46976 47104, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 46976 47104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 46976 47104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1063845 : ℤ) ∧
    (∑ n ∈ Ico 46976 47104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (21276917634001873788120356226 : ℤ) := by
  rcases cdemPrefixStats_46976_47040 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_47040_47104 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 46976 ≤ 47040) (by norm_num : 47040 ≤ 47104), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 46976 ≤ 47040) (by norm_num : 47040 ≤ 47104), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 46976 ≤ 47040) (by norm_num : 47040 ≤ 47104), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 46976 ≤ 47040) (by norm_num : 47040 ≤ 47104), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_46848_47104 :
    (∑ n ∈ Ico 46848 47104, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 46848 47104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 46848 47104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1810467 : ℤ) ∧
    (∑ n ∈ Ico 46848 47104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (36209349352427143225575201625 : ℤ) := by
  rcases cdemPrefixStats_46848_46976 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_46976_47104 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 46848 ≤ 46976) (by norm_num : 46976 ≤ 47104), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 46848 ≤ 46976) (by norm_num : 46976 ≤ 47104), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 46848 ≤ 46976) (by norm_num : 46976 ≤ 47104), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 46848 ≤ 46976) (by norm_num : 46976 ≤ 47104), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_46592_47104 :
    (∑ n ∈ Ico 46592 47104, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 46592 47104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 46592 47104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1598085 : ℤ) ∧
    (∑ n ∈ Ico 46592 47104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (31961644328845244484671307612 : ℤ) := by
  rcases cdemPrefixStats_46592_46848 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_46848_47104 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 46592 ≤ 46848) (by norm_num : 46848 ≤ 47104), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 46592 ≤ 46848) (by norm_num : 46848 ≤ 47104), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 46592 ≤ 46848) (by norm_num : 46848 ≤ 47104), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 46592 ≤ 46848) (by norm_num : 46848 ≤ 47104), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_46080_47104 :
    (∑ n ∈ Ico 46080 47104, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 46080 47104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (626 : ℕ) ∧
    (∑ n ∈ Ico 46080 47104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1709755 : ℤ) ∧
    (∑ n ∈ Ico 46080 47104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (34195171949733448105205435682 : ℤ) := by
  rcases cdemPrefixStats_46080_46592 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_46592_47104 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 46080 ≤ 46592) (by norm_num : 46592 ≤ 47104), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 46080 ≤ 46592) (by norm_num : 46592 ≤ 47104), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 46080 ≤ 46592) (by norm_num : 46592 ≤ 47104), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 46080 ≤ 46592) (by norm_num : 46592 ≤ 47104), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_45056_47104 :
    (∑ n ∈ Ico 45056 47104, mobiusTreeValue 16 mobiusTable1200001 n) = (47 : ℤ) ∧
    (∑ n ∈ Ico 45056 47104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1251 : ℕ) ∧
    (∑ n ∈ Ico 45056 47104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (5080600 : ℤ) ∧
    (∑ n ∈ Ico 45056 47104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (101612280431346268625347959245 : ℤ) := by
  rcases cdemPrefixStats_45056_46080 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_46080_47104 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 45056 ≤ 46080) (by norm_num : 46080 ≤ 47104), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 45056 ≤ 46080) (by norm_num : 46080 ≤ 47104), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 45056 ≤ 46080) (by norm_num : 46080 ≤ 47104), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 45056 ≤ 46080) (by norm_num : 46080 ≤ 47104), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_47104_47168 :
    (∑ n ∈ Ico 47104 47168, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 47104 47168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 47104 47168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-106330 : ℤ) ∧
    (∑ n ∈ Ico 47104 47168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2126603483718355342619223418 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_47168_47232 :
    (∑ n ∈ Ico 47168 47232, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 47168 47232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 47168 47232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1376957 : ℤ) ∧
    (∑ n ∈ Ico 47168 47232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (27539234484851331240505265032 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_47104_47232 :
    (∑ n ∈ Ico 47104 47232, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 47104 47232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 47104 47232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1270627 : ℤ) ∧
    (∑ n ∈ Ico 47104 47232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (25412631001132975897886041614 : ℤ) := by
  rcases cdemPrefixStats_47104_47168 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_47168_47232 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 47104 ≤ 47168) (by norm_num : 47168 ≤ 47232), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 47104 ≤ 47168) (by norm_num : 47168 ≤ 47232), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 47104 ≤ 47168) (by norm_num : 47168 ≤ 47232), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 47104 ≤ 47168) (by norm_num : 47168 ≤ 47232), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_47232_47296 :
    (∑ n ∈ Ico 47232 47296, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 47232 47296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 47232 47296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (317655 : ℤ) ∧
    (∑ n ∈ Ico 47232 47296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6353100966141739861306089774 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_47296_47360 :
    (∑ n ∈ Ico 47296 47360, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 47296 47360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 47296 47360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-528447 : ℤ) ∧
    (∑ n ∈ Ico 47296 47360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10568994295480246651652924304 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_47232_47360 :
    (∑ n ∈ Ico 47232 47360, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 47232 47360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 47232 47360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-210792 : ℤ) ∧
    (∑ n ∈ Ico 47232 47360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4215893329338506790346834530 : ℤ) := by
  rcases cdemPrefixStats_47232_47296 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_47296_47360 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 47232 ≤ 47296) (by norm_num : 47296 ≤ 47360), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 47232 ≤ 47296) (by norm_num : 47296 ≤ 47360), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 47232 ≤ 47296) (by norm_num : 47296 ≤ 47360), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 47232 ≤ 47296) (by norm_num : 47296 ≤ 47360), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_47104_47360 :
    (∑ n ∈ Ico 47104 47360, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 47104 47360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 47104 47360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1059835 : ℤ) ∧
    (∑ n ∈ Ico 47104 47360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (21196737671794469107539207084 : ℤ) := by
  rcases cdemPrefixStats_47104_47232 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_47232_47360 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 47104 ≤ 47232) (by norm_num : 47232 ≤ 47360), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 47104 ≤ 47232) (by norm_num : 47232 ≤ 47360), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 47104 ≤ 47232) (by norm_num : 47232 ≤ 47360), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 47104 ≤ 47232) (by norm_num : 47232 ≤ 47360), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_47360_47424 :
    (∑ n ∈ Ico 47360 47424, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 47360 47424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 47360 47424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (316756 : ℤ) ∧
    (∑ n ∈ Ico 47360 47424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6335081221581840415006520304 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_47424_47488 :
    (∑ n ∈ Ico 47424 47488, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 47424 47488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 47424 47488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (420822 : ℤ) ∧
    (∑ n ∈ Ico 47424 47488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8416473763146530229502971416 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_47360_47488 :
    (∑ n ∈ Ico 47360 47488, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 47360 47488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 47360 47488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (737578 : ℤ) ∧
    (∑ n ∈ Ico 47360 47488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14751554984728370644509491720 : ℤ) := by
  rcases cdemPrefixStats_47360_47424 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_47424_47488 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 47360 ≤ 47424) (by norm_num : 47424 ≤ 47488), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 47360 ≤ 47424) (by norm_num : 47424 ≤ 47488), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 47360 ≤ 47424) (by norm_num : 47424 ≤ 47488), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 47360 ≤ 47424) (by norm_num : 47424 ≤ 47488), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_47488_47552 :
    (∑ n ∈ Ico 47488 47552, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 47488 47552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 47488 47552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-526240 : ℤ) ∧
    (∑ n ∈ Ico 47488 47552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10524806512793575536482022781 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_47552_47616 :
    (∑ n ∈ Ico 47552 47616, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 47552 47616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 47552 47616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-420026 : ℤ) ∧
    (∑ n ∈ Ico 47552 47616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8400532922026787232599686925 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_47488_47616 :
    (∑ n ∈ Ico 47488 47616, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 47488 47616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 47488 47616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-946266 : ℤ) ∧
    (∑ n ∈ Ico 47488 47616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-18925339434820362769081709706 : ℤ) := by
  rcases cdemPrefixStats_47488_47552 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_47552_47616 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 47488 ≤ 47552) (by norm_num : 47552 ≤ 47616), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 47488 ≤ 47552) (by norm_num : 47552 ≤ 47616), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 47488 ≤ 47552) (by norm_num : 47552 ≤ 47616), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 47488 ≤ 47552) (by norm_num : 47552 ≤ 47616), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_47360_47616 :
    (∑ n ∈ Ico 47360 47616, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 47360 47616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 47360 47616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-208688 : ℤ) ∧
    (∑ n ∈ Ico 47360 47616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4173784450091992124572217986 : ℤ) := by
  rcases cdemPrefixStats_47360_47488 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_47488_47616 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 47360 ≤ 47488) (by norm_num : 47488 ≤ 47616), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 47360 ≤ 47488) (by norm_num : 47488 ≤ 47616), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 47360 ≤ 47488) (by norm_num : 47488 ≤ 47616), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 47360 ≤ 47488) (by norm_num : 47488 ≤ 47616), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_47104_47616 :
    (∑ n ∈ Ico 47104 47616, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 47104 47616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (314 : ℕ) ∧
    (∑ n ∈ Ico 47104 47616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (851147 : ℤ) ∧
    (∑ n ∈ Ico 47104 47616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17022953221702476982966989098 : ℤ) := by
  rcases cdemPrefixStats_47104_47360 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_47360_47616 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 47104 ≤ 47360) (by norm_num : 47360 ≤ 47616), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 47104 ≤ 47360) (by norm_num : 47360 ≤ 47616), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 47104 ≤ 47360) (by norm_num : 47360 ≤ 47616), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 47104 ≤ 47360) (by norm_num : 47360 ≤ 47616), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_47616_47680 :
    (∑ n ∈ Ico 47616 47680, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 47616 47680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 47616 47680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-104807 : ℤ) ∧
    (∑ n ∈ Ico 47616 47680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2096126172046894296446876478 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_47680_47744 :
    (∑ n ∈ Ico 47680 47744, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 47680 47744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 47680 47744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (90 : ℤ) ∧
    (∑ n ∈ Ico 47680 47744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1801530823325652752691043 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_47616_47744 :
    (∑ n ∈ Ico 47616 47744, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 47616 47744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 47616 47744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-104717 : ℤ) ∧
    (∑ n ∈ Ico 47616 47744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2094324641223568643694185435 : ℤ) := by
  rcases cdemPrefixStats_47616_47680 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_47680_47744 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 47616 ≤ 47680) (by norm_num : 47680 ≤ 47744), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 47616 ≤ 47680) (by norm_num : 47680 ≤ 47744), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 47616 ≤ 47680) (by norm_num : 47680 ≤ 47744), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 47616 ≤ 47680) (by norm_num : 47680 ≤ 47744), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_47744_47808 :
    (∑ n ∈ Ico 47744 47808, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 47744 47808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 47744 47808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (418892 : ℤ) ∧
    (∑ n ∈ Ico 47744 47808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8377883199991422232922232325 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_47808_47872 :
    (∑ n ∈ Ico 47808 47872, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 47808 47872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 47808 47872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-522399 : ℤ) ∧
    (∑ n ∈ Ico 47808 47872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10448096559889407538153572408 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_47744_47872 :
    (∑ n ∈ Ico 47744 47872, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 47744 47872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 47744 47872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-103507 : ℤ) ∧
    (∑ n ∈ Ico 47744 47872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2070213359897985305231340083 : ℤ) := by
  rcases cdemPrefixStats_47744_47808 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_47808_47872 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 47744 ≤ 47808) (by norm_num : 47808 ≤ 47872), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 47744 ≤ 47808) (by norm_num : 47808 ≤ 47872), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 47744 ≤ 47808) (by norm_num : 47808 ≤ 47872), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 47744 ≤ 47808) (by norm_num : 47808 ≤ 47872), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_47616_47872 :
    (∑ n ∈ Ico 47616 47872, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 47616 47872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 47616 47872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-208224 : ℤ) ∧
    (∑ n ∈ Ico 47616 47872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4164538001121553948925525518 : ℤ) := by
  rcases cdemPrefixStats_47616_47744 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_47744_47872 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 47616 ≤ 47744) (by norm_num : 47744 ≤ 47872), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 47616 ≤ 47744) (by norm_num : 47744 ≤ 47872), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 47616 ≤ 47744) (by norm_num : 47744 ≤ 47872), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 47616 ≤ 47744) (by norm_num : 47744 ≤ 47872), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_47872_47936 :
    (∑ n ∈ Ico 47872 47936, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 47872 47936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 47872 47936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (313108 : ℤ) ∧
    (∑ n ∈ Ico 47872 47936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6262175241640445376091604038 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_47936_48000 :
    (∑ n ∈ Ico 47936 48000, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 47936 48000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 47936 48000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (208267 : ℤ) ∧
    (∑ n ∈ Ico 47936 48000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4165404946487585115730981725 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_47872_48000 :
    (∑ n ∈ Ico 47872 48000, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 47872 48000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 47872 48000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (521375 : ℤ) ∧
    (∑ n ∈ Ico 47872 48000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10427580188128030491822585763 : ℤ) := by
  rcases cdemPrefixStats_47872_47936 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_47936_48000 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 47872 ≤ 47936) (by norm_num : 47936 ≤ 48000), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 47872 ≤ 47936) (by norm_num : 47936 ≤ 48000), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 47872 ≤ 47936) (by norm_num : 47936 ≤ 48000), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 47872 ≤ 47936) (by norm_num : 47936 ≤ 48000), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_48000_48064 :
    (∑ n ∈ Ico 48000 48064, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 48000 48064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 48000 48064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (520929 : ℤ) ∧
    (∑ n ∈ Ico 48000 48064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10418657513936243699652067285 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_48064_48128 :
    (∑ n ∈ Ico 48064 48128, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 48064 48128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 48064 48128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (623743 : ℤ) ∧
    (∑ n ∈ Ico 48064 48128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12474963944605986833054942843 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_48000_48128 :
    (∑ n ∈ Ico 48000 48128, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 48000 48128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 48000 48128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1144672 : ℤ) ∧
    (∑ n ∈ Ico 48000 48128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (22893621458542230532707010128 : ℤ) := by
  rcases cdemPrefixStats_48000_48064 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_48064_48128 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 48000 ≤ 48064) (by norm_num : 48064 ≤ 48128), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 48000 ≤ 48064) (by norm_num : 48064 ≤ 48128), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 48000 ≤ 48064) (by norm_num : 48064 ≤ 48128), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 48000 ≤ 48064) (by norm_num : 48064 ≤ 48128), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_47872_48128 :
    (∑ n ∈ Ico 47872 48128, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 47872 48128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 47872 48128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1666047 : ℤ) ∧
    (∑ n ∈ Ico 47872 48128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (33321201646670261024529595891 : ℤ) := by
  rcases cdemPrefixStats_47872_48000 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_48000_48128 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 47872 ≤ 48000) (by norm_num : 48000 ≤ 48128), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 47872 ≤ 48000) (by norm_num : 48000 ≤ 48128), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 47872 ≤ 48000) (by norm_num : 48000 ≤ 48128), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 47872 ≤ 48000) (by norm_num : 48000 ≤ 48128), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_47616_48128 :
    (∑ n ∈ Ico 47616 48128, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 47616 48128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (308 : ℕ) ∧
    (∑ n ∈ Ico 47616 48128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1457823 : ℤ) ∧
    (∑ n ∈ Ico 47616 48128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (29156663645548707075604070373 : ℤ) := by
  rcases cdemPrefixStats_47616_47872 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_47872_48128 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 47616 ≤ 47872) (by norm_num : 47872 ≤ 48128), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 47616 ≤ 47872) (by norm_num : 47872 ≤ 48128), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 47616 ≤ 47872) (by norm_num : 47872 ≤ 48128), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 47616 ≤ 47872) (by norm_num : 47872 ≤ 48128), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_47104_48128 :
    (∑ n ∈ Ico 47104 48128, mobiusTreeValue 16 mobiusTable1200001 n) = (22 : ℤ) ∧
    (∑ n ∈ Ico 47104 48128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (622 : ℕ) ∧
    (∑ n ∈ Ico 47104 48128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2308970 : ℤ) ∧
    (∑ n ∈ Ico 47104 48128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (46179616867251184058571059471 : ℤ) := by
  rcases cdemPrefixStats_47104_47616 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_47616_48128 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 47104 ≤ 47616) (by norm_num : 47616 ≤ 48128), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 47104 ≤ 47616) (by norm_num : 47616 ≤ 48128), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 47104 ≤ 47616) (by norm_num : 47616 ≤ 48128), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 47104 ≤ 47616) (by norm_num : 47616 ≤ 48128), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_48128_48192 :
    (∑ n ∈ Ico 48128 48192, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 48128 48192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 48128 48192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (622845 : ℤ) ∧
    (∑ n ∈ Ico 48128 48192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12456962378359969445729408881 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_48192_48256 :
    (∑ n ∈ Ico 48192 48256, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 48192 48256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 48192 48256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (415217 : ℤ) ∧
    (∑ n ∈ Ico 48192 48256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8304342271259870684029535470 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_48128_48256 :
    (∑ n ∈ Ico 48128 48256, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 48128 48256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 48128 48256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1038062 : ℤ) ∧
    (∑ n ∈ Ico 48128 48256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (20761304649619840129758944351 : ℤ) := by
  rcases cdemPrefixStats_48128_48192 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_48192_48256 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 48128 ≤ 48192) (by norm_num : 48192 ≤ 48256), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 48128 ≤ 48192) (by norm_num : 48192 ≤ 48256), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 48128 ≤ 48192) (by norm_num : 48192 ≤ 48256), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 48128 ≤ 48192) (by norm_num : 48192 ≤ 48256), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_48256_48320 :
    (∑ n ∈ Ico 48256 48320, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 48256 48320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 48256 48320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (414151 : ℤ) ∧
    (∑ n ∈ Ico 48256 48320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8283072544416100321829901083 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_48320_48384 :
    (∑ n ∈ Ico 48320 48384, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 48320 48384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 48320 48384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (206591 : ℤ) ∧
    (∑ n ∈ Ico 48320 48384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4131841549399952127250955210 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_48256_48384 :
    (∑ n ∈ Ico 48256 48384, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 48256 48384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (74 : ℕ) ∧
    (∑ n ∈ Ico 48256 48384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (620742 : ℤ) ∧
    (∑ n ∈ Ico 48256 48384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12414914093816052449080856293 : ℤ) := by
  rcases cdemPrefixStats_48256_48320 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_48320_48384 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 48256 ≤ 48320) (by norm_num : 48320 ≤ 48384), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 48256 ≤ 48320) (by norm_num : 48320 ≤ 48384), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 48256 ≤ 48320) (by norm_num : 48320 ≤ 48384), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 48256 ≤ 48320) (by norm_num : 48320 ≤ 48384), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_48128_48384 :
    (∑ n ∈ Ico 48128 48384, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 48128 48384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 48128 48384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1658804 : ℤ) ∧
    (∑ n ∈ Ico 48128 48384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (33176218743435892578839800644 : ℤ) := by
  rcases cdemPrefixStats_48128_48256 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_48256_48384 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 48128 ≤ 48256) (by norm_num : 48256 ≤ 48384), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 48128 ≤ 48256) (by norm_num : 48256 ≤ 48384), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 48128 ≤ 48256) (by norm_num : 48256 ≤ 48384), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 48128 ≤ 48256) (by norm_num : 48256 ≤ 48384), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_48384_48448 :
    (∑ n ∈ Ico 48384 48448, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 48384 48448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 48384 48448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (826048 : ℤ) ∧
    (∑ n ∈ Ico 48384 48448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (16521076145586276415972287430 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_48448_48512 :
    (∑ n ∈ Ico 48448 48512, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 48448 48512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 48448 48512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (102821 : ℤ) ∧
    (∑ n ∈ Ico 48448 48512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2056495258757756769763265761 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_48384_48512 :
    (∑ n ∈ Ico 48384 48512, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 48384 48512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 48384 48512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (928869 : ℤ) ∧
    (∑ n ∈ Ico 48384 48512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18577571404344033185735553191 : ℤ) := by
  rcases cdemPrefixStats_48384_48448 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_48448_48512 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 48384 ≤ 48448) (by norm_num : 48448 ≤ 48512), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 48384 ≤ 48448) (by norm_num : 48448 ≤ 48512), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 48384 ≤ 48448) (by norm_num : 48448 ≤ 48512), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 48384 ≤ 48448) (by norm_num : 48448 ≤ 48512), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_48512_48576 :
    (∑ n ∈ Ico 48512 48576, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 48512 48576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 48512 48576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1236528 : ℤ) ∧
    (∑ n ∈ Ico 48512 48576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-24730710695637874798026011822 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_48576_48640 :
    (∑ n ∈ Ico 48576 48640, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 48576 48640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 48576 48640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-308700 : ℤ) ∧
    (∑ n ∈ Ico 48576 48640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6174024023473278271071056405 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_48512_48640 :
    (∑ n ∈ Ico 48512 48640, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 48512 48640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 48512 48640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1545228 : ℤ) ∧
    (∑ n ∈ Ico 48512 48640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-30904734719111153069097068227 : ℤ) := by
  rcases cdemPrefixStats_48512_48576 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_48576_48640 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 48512 ≤ 48576) (by norm_num : 48576 ≤ 48640), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 48512 ≤ 48576) (by norm_num : 48576 ≤ 48640), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 48512 ≤ 48576) (by norm_num : 48576 ≤ 48640), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 48512 ≤ 48576) (by norm_num : 48576 ≤ 48640), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_48384_48640 :
    (∑ n ∈ Ico 48384 48640, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 48384 48640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 48384 48640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-616359 : ℤ) ∧
    (∑ n ∈ Ico 48384 48640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12327163314767119883361515036 : ℤ) := by
  rcases cdemPrefixStats_48384_48512 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_48512_48640 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 48384 ≤ 48512) (by norm_num : 48512 ≤ 48640), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 48384 ≤ 48512) (by norm_num : 48512 ≤ 48640), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 48384 ≤ 48512) (by norm_num : 48512 ≤ 48640), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 48384 ≤ 48512) (by norm_num : 48512 ≤ 48640), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_48128_48640 :
    (∑ n ∈ Ico 48128 48640, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 48128 48640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 48128 48640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1042445 : ℤ) ∧
    (∑ n ∈ Ico 48128 48640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (20849055428668772695478285608 : ℤ) := by
  rcases cdemPrefixStats_48128_48384 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_48384_48640 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 48128 ≤ 48384) (by norm_num : 48384 ≤ 48640), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 48128 ≤ 48384) (by norm_num : 48384 ≤ 48640), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 48128 ≤ 48384) (by norm_num : 48384 ≤ 48640), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 48128 ≤ 48384) (by norm_num : 48384 ≤ 48640), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_48640_48704 :
    (∑ n ∈ Ico 48640 48704, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 48640 48704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 48640 48704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-205451 : ℤ) ∧
    (∑ n ∈ Ico 48640 48704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4109053893292105717353204335 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_48704_48768 :
    (∑ n ∈ Ico 48704 48768, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 48704 48768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 48704 48768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (364 : ℤ) ∧
    (∑ n ∈ Ico 48704 48768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7283353979738335311394225 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_48640_48768 :
    (∑ n ∈ Ico 48640 48768, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 48640 48768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (74 : ℕ) ∧
    (∑ n ∈ Ico 48640 48768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-205087 : ℤ) ∧
    (∑ n ∈ Ico 48640 48768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4101770539312367382041810110 : ℤ) := by
  rcases cdemPrefixStats_48640_48704 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_48704_48768 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 48640 ≤ 48704) (by norm_num : 48704 ≤ 48768), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 48640 ≤ 48704) (by norm_num : 48704 ≤ 48768), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 48640 ≤ 48704) (by norm_num : 48704 ≤ 48768), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 48640 ≤ 48704) (by norm_num : 48704 ≤ 48768), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_48768_48832 :
    (∑ n ∈ Ico 48768 48832, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 48768 48832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 48768 48832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-512362 : ℤ) ∧
    (∑ n ∈ Ico 48768 48832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10247288107150314261111667561 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_48832_48896 :
    (∑ n ∈ Ico 48832 48896, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 48832 48896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 48832 48896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-306697 : ℤ) ∧
    (∑ n ∈ Ico 48832 48896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6133958370095597111367543612 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_48768_48896 :
    (∑ n ∈ Ico 48768 48896, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 48768 48896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 48768 48896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-819059 : ℤ) ∧
    (∑ n ∈ Ico 48768 48896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-16381246477245911372479211173 : ℤ) := by
  rcases cdemPrefixStats_48768_48832 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_48832_48896 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 48768 ≤ 48832) (by norm_num : 48832 ≤ 48896), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 48768 ≤ 48832) (by norm_num : 48832 ≤ 48896), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 48768 ≤ 48832) (by norm_num : 48832 ≤ 48896), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 48768 ≤ 48832) (by norm_num : 48832 ≤ 48896), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_48640_48896 :
    (∑ n ∈ Ico 48640 48896, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 48640 48896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 48640 48896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1024146 : ℤ) ∧
    (∑ n ∈ Ico 48640 48896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-20483017016558278754521021283 : ℤ) := by
  rcases cdemPrefixStats_48640_48768 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_48768_48896 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 48640 ≤ 48768) (by norm_num : 48768 ≤ 48896), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 48640 ≤ 48768) (by norm_num : 48768 ≤ 48896), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 48640 ≤ 48768) (by norm_num : 48768 ≤ 48896), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 48640 ≤ 48768) (by norm_num : 48768 ≤ 48896), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_48896_48960 :
    (∑ n ∈ Ico 48896 48960, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 48896 48960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 48896 48960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1123897 : ℤ) ∧
    (∑ n ∈ Ico 48896 48960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (22478052075692336572969892055 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_48960_49024 :
    (∑ n ∈ Ico 48960 49024, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 48960 49024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 48960 49024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-714478 : ℤ) ∧
    (∑ n ∈ Ico 48960 49024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14289630619675859659845178663 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_48896_49024 :
    (∑ n ∈ Ico 48896 49024, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 48896 49024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 48896 49024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (409419 : ℤ) ∧
    (∑ n ∈ Ico 48896 49024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8188421456016476913124713392 : ℤ) := by
  rcases cdemPrefixStats_48896_48960 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_48960_49024 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 48896 ≤ 48960) (by norm_num : 48960 ≤ 49024), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 48896 ≤ 48960) (by norm_num : 48960 ≤ 49024), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 48896 ≤ 48960) (by norm_num : 48960 ≤ 49024), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 48896 ≤ 48960) (by norm_num : 48960 ≤ 49024), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_49024_49088 :
    (∑ n ∈ Ico 49024 49088, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 49024 49088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 49024 49088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-204176 : ℤ) ∧
    (∑ n ∈ Ico 49024 49088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4083538529849657520644578653 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_49088_49152 :
    (∑ n ∈ Ico 49088 49152, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 49088 49152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 49088 49152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (509076 : ℤ) ∧
    (∑ n ∈ Ico 49088 49152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10181561045569538799291706439 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_49024_49152 :
    (∑ n ∈ Ico 49024 49152, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 49024 49152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 49024 49152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (304900 : ℤ) ∧
    (∑ n ∈ Ico 49024 49152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6098022515719881278647127786 : ℤ) := by
  rcases cdemPrefixStats_49024_49088 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_49088_49152 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 49024 ≤ 49088) (by norm_num : 49088 ≤ 49152), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 49024 ≤ 49088) (by norm_num : 49088 ≤ 49152), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 49024 ≤ 49088) (by norm_num : 49088 ≤ 49152), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 49024 ≤ 49088) (by norm_num : 49088 ≤ 49152), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_48896_49152 :
    (∑ n ∈ Ico 48896 49152, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 48896 49152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 48896 49152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (714319 : ℤ) ∧
    (∑ n ∈ Ico 48896 49152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14286443971736358191771841178 : ℤ) := by
  rcases cdemPrefixStats_48896_49024 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_49024_49152 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 48896 ≤ 49024) (by norm_num : 49024 ≤ 49152), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 48896 ≤ 49024) (by norm_num : 49024 ≤ 49152), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 48896 ≤ 49024) (by norm_num : 49024 ≤ 49152), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 48896 ≤ 49024) (by norm_num : 49024 ≤ 49152), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_48640_49152 :
    (∑ n ∈ Ico 48640 49152, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 48640 49152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 48640 49152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-309827 : ℤ) ∧
    (∑ n ∈ Ico 48640 49152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6196573044821920562749180105 : ℤ) := by
  rcases cdemPrefixStats_48640_48896 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_48896_49152 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 48640 ≤ 48896) (by norm_num : 48896 ≤ 49152), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 48640 ≤ 48896) (by norm_num : 48896 ≤ 49152), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 48640 ≤ 48896) (by norm_num : 48896 ≤ 49152), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 48640 ≤ 48896) (by norm_num : 48896 ≤ 49152), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_48128_49152 :
    (∑ n ∈ Ico 48128 49152, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 48128 49152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (619 : ℕ) ∧
    (∑ n ∈ Ico 48128 49152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (732618 : ℤ) ∧
    (∑ n ∈ Ico 48128 49152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14652482383846852132729105503 : ℤ) := by
  rcases cdemPrefixStats_48128_48640 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_48640_49152 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 48128 ≤ 48640) (by norm_num : 48640 ≤ 49152), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 48128 ≤ 48640) (by norm_num : 48640 ≤ 49152), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 48128 ≤ 48640) (by norm_num : 48640 ≤ 49152), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 48128 ≤ 48640) (by norm_num : 48640 ≤ 49152), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_47104_49152 :
    (∑ n ∈ Ico 47104 49152, mobiusTreeValue 16 mobiusTable1200001 n) = (29 : ℤ) ∧
    (∑ n ∈ Ico 47104 49152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1241 : ℕ) ∧
    (∑ n ∈ Ico 47104 49152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3041588 : ℤ) ∧
    (∑ n ∈ Ico 47104 49152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (60832099251098036191300164974 : ℤ) := by
  rcases cdemPrefixStats_47104_48128 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_48128_49152 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 47104 ≤ 48128) (by norm_num : 48128 ≤ 49152), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 47104 ≤ 48128) (by norm_num : 48128 ≤ 49152), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 47104 ≤ 48128) (by norm_num : 48128 ≤ 49152), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 47104 ≤ 48128) (by norm_num : 48128 ≤ 49152), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_45056_49152 :
    (∑ n ∈ Ico 45056 49152, mobiusTreeValue 16 mobiusTable1200001 n) = (76 : ℤ) ∧
    (∑ n ∈ Ico 45056 49152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2492 : ℕ) ∧
    (∑ n ∈ Ico 45056 49152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (8122188 : ℤ) ∧
    (∑ n ∈ Ico 45056 49152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (162444379682444304816648124219 : ℤ) := by
  rcases cdemPrefixStats_45056_47104 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_47104_49152 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 45056 ≤ 47104) (by norm_num : 47104 ≤ 49152), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 45056 ≤ 47104) (by norm_num : 47104 ≤ 49152), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 45056 ≤ 47104) (by norm_num : 47104 ≤ 49152), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 45056 ≤ 47104) (by norm_num : 47104 ≤ 49152), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup011_checked_complete :
    (∑ n ∈ Ico 45056 49152, mobiusTreeValue 16 mobiusTable1200001 n) = (76 : ℤ) ∧
    (∑ n ∈ Ico 45056 49152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2492 : ℕ) ∧
    (∑ n ∈ Ico 45056 49152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (8122188 : ℤ) ∧
    (∑ n ∈ Ico 45056 49152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (162444379682444304816648124219 : ℤ) := cdemPrefixStats_45056_49152
end Helfgott
#print axioms Helfgott.cdemPrefixGroup011_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 45056 49152, mobiusTreeValue 16 mobiusTable1200001 n) = (76 : ℤ) ∧
    (∑ n ∈ Ico 45056 49152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2492 : ℕ) ∧
    (∑ n ∈ Ico 45056 49152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (8122188 : ℤ) ∧
    (∑ n ∈ Ico 45056 49152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (162444379682444304816648124219 : ℤ) := Helfgott.cdemPrefixGroup011_checked_complete
#print axioms solution
