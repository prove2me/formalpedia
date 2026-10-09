-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup027_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T02:09:28.454764+00:00
-- url     : https://prove2.me/submissions/c9970ba6-f0ed-4a28-8078-93553bea3df6

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
private theorem cdemPrefixStats_110592_110656 :
    (∑ n ∈ Ico 110592 110656, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 110592 110656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 110592 110656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-225972 : ℤ) ∧
    (∑ n ∈ Ico 110592 110656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4519455599179069080394863371 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_110656_110720 :
    (∑ n ∈ Ico 110656 110720, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 110656 110720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 110656 110720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (587288 : ℤ) ∧
    (∑ n ∈ Ico 110656 110720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11745891504733985573799058010 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_110592_110720 :
    (∑ n ∈ Ico 110592 110720, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 110592 110720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 110592 110720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (361316 : ℤ) ∧
    (∑ n ∈ Ico 110592 110720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7226435905554916493404194639 : ℤ) := by
  rcases cdemPrefixStats_110592_110656 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_110656_110720 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 110592 ≤ 110656) (by norm_num : 110656 ≤ 110720), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 110592 ≤ 110656) (by norm_num : 110656 ≤ 110720), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 110592 ≤ 110656) (by norm_num : 110656 ≤ 110720), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 110592 ≤ 110656) (by norm_num : 110656 ≤ 110720), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_110720_110784 :
    (∑ n ∈ Ico 110720 110784, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 110720 110784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 110720 110784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (270861 : ℤ) ∧
    (∑ n ∈ Ico 110720 110784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5417281497457956284509127195 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_110784_110848 :
    (∑ n ∈ Ico 110784 110848, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 110784 110848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 110784 110848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-45040 : ℤ) ∧
    (∑ n ∈ Ico 110784 110848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-900768070026647990439060145 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_110720_110848 :
    (∑ n ∈ Ico 110720 110848, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 110720 110848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 110720 110848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (225821 : ℤ) ∧
    (∑ n ∈ Ico 110720 110848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4516513427431308294070067050 : ℤ) := by
  rcases cdemPrefixStats_110720_110784 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_110784_110848 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 110720 ≤ 110784) (by norm_num : 110784 ≤ 110848), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 110720 ≤ 110784) (by norm_num : 110784 ≤ 110848), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 110720 ≤ 110784) (by norm_num : 110784 ≤ 110848), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 110720 ≤ 110784) (by norm_num : 110784 ≤ 110848), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_110592_110848 :
    (∑ n ∈ Ico 110592 110848, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 110592 110848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 110592 110848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (587137 : ℤ) ∧
    (∑ n ∈ Ico 110592 110848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11742949332986224787474261689 : ℤ) := by
  rcases cdemPrefixStats_110592_110720 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_110720_110848 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 110592 ≤ 110720) (by norm_num : 110720 ≤ 110848), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 110592 ≤ 110720) (by norm_num : 110720 ≤ 110848), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 110592 ≤ 110720) (by norm_num : 110720 ≤ 110848), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 110592 ≤ 110720) (by norm_num : 110720 ≤ 110848), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_110848_110912 :
    (∑ n ∈ Ico 110848 110912, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 110848 110912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 110848 110912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-315626 : ℤ) ∧
    (∑ n ∈ Ico 110848 110912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6312545808672950050135341807 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_110912_110976 :
    (∑ n ∈ Ico 110912 110976, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 110912 110976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 110912 110976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-585903 : ℤ) ∧
    (∑ n ∈ Ico 110912 110976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11718200596905519098977860934 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_110848_110976 :
    (∑ n ∈ Ico 110848 110976, mobiusTreeValue 16 mobiusTable1200001 n) = (-20 : ℤ) ∧
    (∑ n ∈ Ico 110848 110976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 110848 110976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-901529 : ℤ) ∧
    (∑ n ∈ Ico 110848 110976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-18030746405578469149113202741 : ℤ) := by
  rcases cdemPrefixStats_110848_110912 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_110912_110976 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 110848 ≤ 110912) (by norm_num : 110912 ≤ 110976), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 110848 ≤ 110912) (by norm_num : 110912 ≤ 110976), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 110848 ≤ 110912) (by norm_num : 110912 ≤ 110976), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 110848 ≤ 110912) (by norm_num : 110912 ≤ 110976), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_110976_111040 :
    (∑ n ∈ Ico 110976 111040, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 110976 111040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 110976 111040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (315289 : ℤ) ∧
    (∑ n ∈ Ico 110976 111040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6305811221651287216666476641 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_111040_111104 :
    (∑ n ∈ Ico 111040 111104, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 111040 111104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 111040 111104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-44963 : ℤ) ∧
    (∑ n ∈ Ico 111040 111104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-899255418697287937674797710 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_110976_111104 :
    (∑ n ∈ Ico 110976 111104, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 110976 111104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 110976 111104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (270326 : ℤ) ∧
    (∑ n ∈ Ico 110976 111104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5406555802953999278991678931 : ℤ) := by
  rcases cdemPrefixStats_110976_111040 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_111040_111104 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 110976 ≤ 111040) (by norm_num : 111040 ≤ 111104), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 110976 ≤ 111040) (by norm_num : 111040 ≤ 111104), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 110976 ≤ 111040) (by norm_num : 111040 ≤ 111104), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 110976 ≤ 111040) (by norm_num : 111040 ≤ 111104), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_110848_111104 :
    (∑ n ∈ Ico 110848 111104, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 110848 111104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 110848 111104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-631203 : ℤ) ∧
    (∑ n ∈ Ico 110848 111104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12624190602624469870121523810 : ℤ) := by
  rcases cdemPrefixStats_110848_110976 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_110976_111104 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 110848 ≤ 110976) (by norm_num : 110976 ≤ 111104), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 110848 ≤ 110976) (by norm_num : 110976 ≤ 111104), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 110848 ≤ 110976) (by norm_num : 110976 ≤ 111104), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 110848 ≤ 110976) (by norm_num : 110976 ≤ 111104), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_110592_111104 :
    (∑ n ∈ Ico 110592 111104, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 110592 111104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 110592 111104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-44066 : ℤ) ∧
    (∑ n ∈ Ico 110592 111104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-881241269638245082647262121 : ℤ) := by
  rcases cdemPrefixStats_110592_110848 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_110848_111104 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 110592 ≤ 110848) (by norm_num : 110848 ≤ 111104), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 110592 ≤ 110848) (by norm_num : 110848 ≤ 111104), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 110592 ≤ 110848) (by norm_num : 110848 ≤ 111104), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 110592 ≤ 110848) (by norm_num : 110848 ≤ 111104), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_111104_111168 :
    (∑ n ∈ Ico 111104 111168, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 111104 111168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 111104 111168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-45082 : ℤ) ∧
    (∑ n ∈ Ico 111104 111168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-901668593379745523029293030 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_111168_111232 :
    (∑ n ∈ Ico 111168 111232, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 111168 111232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 111168 111232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-179805 : ℤ) ∧
    (∑ n ∈ Ico 111168 111232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3596006232706825113824811907 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_111104_111232 :
    (∑ n ∈ Ico 111104 111232, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 111104 111232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 111104 111232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-224887 : ℤ) ∧
    (∑ n ∈ Ico 111104 111232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4497674826086570636854104937 : ℤ) := by
  rcases cdemPrefixStats_111104_111168 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_111168_111232 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 111104 ≤ 111168) (by norm_num : 111168 ≤ 111232), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 111104 ≤ 111168) (by norm_num : 111168 ≤ 111232), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 111104 ≤ 111168) (by norm_num : 111168 ≤ 111232), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 111104 ≤ 111168) (by norm_num : 111168 ≤ 111232), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_111232_111296 :
    (∑ n ∈ Ico 111232 111296, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 111232 111296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 111232 111296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (224640 : ℤ) ∧
    (∑ n ∈ Ico 111232 111296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4492863537987932191086272315 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_111296_111360 :
    (∑ n ∈ Ico 111296 111360, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 111296 111360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 111296 111360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-44936 : ℤ) ∧
    (∑ n ∈ Ico 111296 111360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-898722640987144144528828150 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_111232_111360 :
    (∑ n ∈ Ico 111232 111360, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 111232 111360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 111232 111360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (179704 : ℤ) ∧
    (∑ n ∈ Ico 111232 111360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3594140897000788046557444165 : ℤ) := by
  rcases cdemPrefixStats_111232_111296 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_111296_111360 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 111232 ≤ 111296) (by norm_num : 111296 ≤ 111360), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 111232 ≤ 111296) (by norm_num : 111296 ≤ 111360), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 111232 ≤ 111296) (by norm_num : 111296 ≤ 111360), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 111232 ≤ 111296) (by norm_num : 111296 ≤ 111360), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_111104_111360 :
    (∑ n ∈ Ico 111104 111360, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 111104 111360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 111104 111360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-45183 : ℤ) ∧
    (∑ n ∈ Ico 111104 111360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-903533929085782590296660772 : ℤ) := by
  rcases cdemPrefixStats_111104_111232 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_111232_111360 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 111104 ≤ 111232) (by norm_num : 111232 ≤ 111360), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 111104 ≤ 111232) (by norm_num : 111232 ≤ 111360), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 111104 ≤ 111232) (by norm_num : 111232 ≤ 111360), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 111104 ≤ 111232) (by norm_num : 111232 ≤ 111360), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_111360_111424 :
    (∑ n ∈ Ico 111360 111424, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 111360 111424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 111360 111424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (673262 : ℤ) ∧
    (∑ n ∈ Ico 111360 111424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13465354013905325795572769725 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_111424_111488 :
    (∑ n ∈ Ico 111424 111488, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 111424 111488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 111424 111488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (44875 : ℤ) ∧
    (∑ n ∈ Ico 111424 111488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (897480561445079505956335401 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_111360_111488 :
    (∑ n ∈ Ico 111360 111488, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 111360 111488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 111360 111488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (718137 : ℤ) ∧
    (∑ n ∈ Ico 111360 111488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14362834575350405301529105126 : ℤ) := by
  rcases cdemPrefixStats_111360_111424 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_111424_111488 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 111360 ≤ 111424) (by norm_num : 111424 ≤ 111488), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 111360 ≤ 111424) (by norm_num : 111424 ≤ 111488), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 111360 ≤ 111424) (by norm_num : 111424 ≤ 111488), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 111360 ≤ 111424) (by norm_num : 111424 ≤ 111488), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_111488_111552 :
    (∑ n ∈ Ico 111488 111552, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 111488 111552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 111488 111552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-179477 : ℤ) ∧
    (∑ n ∈ Ico 111488 111552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3589526672055370662197378468 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_111552_111616 :
    (∑ n ∈ Ico 111552 111616, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 111552 111616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 111552 111616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (179247 : ℤ) ∧
    (∑ n ∈ Ico 111552 111616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3584976496008887021671535373 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_111488_111616 :
    (∑ n ∈ Ico 111488 111616, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 111488 111616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 111488 111616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-230 : ℤ) ∧
    (∑ n ∈ Ico 111488 111616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4550176046483640525843095 : ℤ) := by
  rcases cdemPrefixStats_111488_111552 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_111552_111616 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 111488 ≤ 111552) (by norm_num : 111552 ≤ 111616), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 111488 ≤ 111552) (by norm_num : 111552 ≤ 111616), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 111488 ≤ 111552) (by norm_num : 111552 ≤ 111616), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 111488 ≤ 111552) (by norm_num : 111552 ≤ 111616), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_111360_111616 :
    (∑ n ∈ Ico 111360 111616, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 111360 111616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 111360 111616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (717907 : ℤ) ∧
    (∑ n ∈ Ico 111360 111616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14358284399303921661003262031 : ℤ) := by
  rcases cdemPrefixStats_111360_111488 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_111488_111616 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 111360 ≤ 111488) (by norm_num : 111488 ≤ 111616), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 111360 ≤ 111488) (by norm_num : 111488 ≤ 111616), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 111360 ≤ 111488) (by norm_num : 111488 ≤ 111616), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 111360 ≤ 111488) (by norm_num : 111488 ≤ 111616), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_111104_111616 :
    (∑ n ∈ Ico 111104 111616, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 111104 111616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (315 : ℕ) ∧
    (∑ n ∈ Ico 111104 111616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (672724 : ℤ) ∧
    (∑ n ∈ Ico 111104 111616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13454750470218139070706601259 : ℤ) := by
  rcases cdemPrefixStats_111104_111360 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_111360_111616 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 111104 ≤ 111360) (by norm_num : 111360 ≤ 111616), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 111104 ≤ 111360) (by norm_num : 111360 ≤ 111616), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 111104 ≤ 111360) (by norm_num : 111360 ≤ 111616), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 111104 ≤ 111360) (by norm_num : 111360 ≤ 111616), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_110592_111616 :
    (∑ n ∈ Ico 110592 111616, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 110592 111616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (624 : ℕ) ∧
    (∑ n ∈ Ico 110592 111616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (628658 : ℤ) ∧
    (∑ n ∈ Ico 110592 111616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12573509200579893988059339138 : ℤ) := by
  rcases cdemPrefixStats_110592_111104 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_111104_111616 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 110592 ≤ 111104) (by norm_num : 111104 ≤ 111616), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 110592 ≤ 111104) (by norm_num : 111104 ≤ 111616), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 110592 ≤ 111104) (by norm_num : 111104 ≤ 111616), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 110592 ≤ 111104) (by norm_num : 111104 ≤ 111616), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_111616_111680 :
    (∑ n ∈ Ico 111616 111680, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 111616 111680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 111616 111680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (179026 : ℤ) ∧
    (∑ n ∈ Ico 111616 111680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3580514547848492561217704836 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_111680_111744 :
    (∑ n ∈ Ico 111680 111744, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 111680 111744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 111680 111744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (134215 : ℤ) ∧
    (∑ n ∈ Ico 111680 111744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2684251114444957071832086819 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_111616_111744 :
    (∑ n ∈ Ico 111616 111744, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 111616 111744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 111616 111744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (313241 : ℤ) ∧
    (∑ n ∈ Ico 111616 111744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6264765662293449633049791655 : ℤ) := by
  rcases cdemPrefixStats_111616_111680 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_111680_111744 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 111616 ≤ 111680) (by norm_num : 111680 ≤ 111744), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 111616 ≤ 111680) (by norm_num : 111680 ≤ 111744), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 111616 ≤ 111680) (by norm_num : 111680 ≤ 111744), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 111616 ≤ 111680) (by norm_num : 111680 ≤ 111744), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_111744_111808 :
    (∑ n ∈ Ico 111744 111808, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 111744 111808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 111744 111808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (178909 : ℤ) ∧
    (∑ n ∈ Ico 111744 111808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3578225734448958770096654694 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_111808_111872 :
    (∑ n ∈ Ico 111808 111872, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 111808 111872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 111808 111872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (134177 : ℤ) ∧
    (∑ n ∈ Ico 111808 111872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2683562834500670376468810325 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_111744_111872 :
    (∑ n ∈ Ico 111744 111872, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 111744 111872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 111744 111872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (313086 : ℤ) ∧
    (∑ n ∈ Ico 111744 111872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6261788568949629146565465019 : ℤ) := by
  rcases cdemPrefixStats_111744_111808 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_111808_111872 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 111744 ≤ 111808) (by norm_num : 111808 ≤ 111872), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 111744 ≤ 111808) (by norm_num : 111808 ≤ 111872), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 111744 ≤ 111808) (by norm_num : 111808 ≤ 111872), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 111744 ≤ 111808) (by norm_num : 111808 ≤ 111872), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_111616_111872 :
    (∑ n ∈ Ico 111616 111872, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 111616 111872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 111616 111872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (626327 : ℤ) ∧
    (∑ n ∈ Ico 111616 111872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12526554231243078779615256674 : ℤ) := by
  rcases cdemPrefixStats_111616_111744 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_111744_111872 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 111616 ≤ 111744) (by norm_num : 111744 ≤ 111872), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 111616 ≤ 111744) (by norm_num : 111744 ≤ 111872), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 111616 ≤ 111744) (by norm_num : 111744 ≤ 111872), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 111616 ≤ 111744) (by norm_num : 111744 ≤ 111872), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_111872_111936 :
    (∑ n ∈ Ico 111872 111936, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 111872 111936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 111872 111936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (268118 : ℤ) ∧
    (∑ n ∈ Ico 111872 111936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5362449472774462741504431715 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_111936_112000 :
    (∑ n ∈ Ico 111936 112000, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 111936 112000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 111936 112000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (4 : ℤ) ∧
    (∑ n ∈ Ico 111936 112000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (119545531220549152722775 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_111872_112000 :
    (∑ n ∈ Ico 111872 112000, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 111872 112000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 111872 112000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (268122 : ℤ) ∧
    (∑ n ∈ Ico 111872 112000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5362569018305683290657154490 : ℤ) := by
  rcases cdemPrefixStats_111872_111936 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_111936_112000 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 111872 ≤ 111936) (by norm_num : 111936 ≤ 112000), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 111872 ≤ 111936) (by norm_num : 111936 ≤ 112000), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 111872 ≤ 111936) (by norm_num : 111936 ≤ 112000), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 111872 ≤ 111936) (by norm_num : 111936 ≤ 112000), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_112000_112064 :
    (∑ n ∈ Ico 112000 112064, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 112000 112064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 112000 112064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (357115 : ℤ) ∧
    (∑ n ∈ Ico 112000 112064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7142338912792470250137739244 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_112064_112128 :
    (∑ n ∈ Ico 112064 112128, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 112064 112128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 112064 112128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-223032 : ℤ) ∧
    (∑ n ∈ Ico 112064 112128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4460645599770188441900472394 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_112000_112128 :
    (∑ n ∈ Ico 112000 112128, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 112000 112128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 112000 112128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (134083 : ℤ) ∧
    (∑ n ∈ Ico 112000 112128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2681693313022281808237266850 : ℤ) := by
  rcases cdemPrefixStats_112000_112064 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_112064_112128 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 112000 ≤ 112064) (by norm_num : 112064 ≤ 112128), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 112000 ≤ 112064) (by norm_num : 112064 ≤ 112128), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 112000 ≤ 112064) (by norm_num : 112064 ≤ 112128), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 112000 ≤ 112064) (by norm_num : 112064 ≤ 112128), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_111872_112128 :
    (∑ n ∈ Ico 111872 112128, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 111872 112128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 111872 112128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (402205 : ℤ) ∧
    (∑ n ∈ Ico 111872 112128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8044262331327965098894421340 : ℤ) := by
  rcases cdemPrefixStats_111872_112000 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_112000_112128 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 111872 ≤ 112000) (by norm_num : 112000 ≤ 112128), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 111872 ≤ 112000) (by norm_num : 112000 ≤ 112128), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 111872 ≤ 112000) (by norm_num : 112000 ≤ 112128), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 111872 ≤ 112000) (by norm_num : 112000 ≤ 112128), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_111616_112128 :
    (∑ n ∈ Ico 111616 112128, mobiusTreeValue 16 mobiusTable1200001 n) = (23 : ℤ) ∧
    (∑ n ∈ Ico 111616 112128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 111616 112128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1028532 : ℤ) ∧
    (∑ n ∈ Ico 111616 112128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (20570816562571043878509678014 : ℤ) := by
  rcases cdemPrefixStats_111616_111872 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_111872_112128 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 111616 ≤ 111872) (by norm_num : 111872 ≤ 112128), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 111616 ≤ 111872) (by norm_num : 111872 ≤ 112128), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 111616 ≤ 111872) (by norm_num : 111872 ≤ 112128), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 111616 ≤ 111872) (by norm_num : 111872 ≤ 112128), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_112128_112192 :
    (∑ n ∈ Ico 112128 112192, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 112128 112192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 112128 112192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (89037 : ℤ) ∧
    (∑ n ∈ Ico 112128 112192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1780766368022514864548580225 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_112192_112256 :
    (∑ n ∈ Ico 112192 112256, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 112192 112256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 112192 112256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-44605 : ℤ) ∧
    (∑ n ∈ Ico 112192 112256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-892146883463785911665925796 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_112128_112256 :
    (∑ n ∈ Ico 112128 112256, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 112128 112256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 112128 112256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (44432 : ℤ) ∧
    (∑ n ∈ Ico 112128 112256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (888619484558728952882654429 : ℤ) := by
  rcases cdemPrefixStats_112128_112192 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_112192_112256 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 112128 ≤ 112192) (by norm_num : 112192 ≤ 112256), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 112128 ≤ 112192) (by norm_num : 112192 ≤ 112256), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 112128 ≤ 112192) (by norm_num : 112192 ≤ 112256), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 112128 ≤ 112192) (by norm_num : 112192 ≤ 112256), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_112256_112320 :
    (∑ n ∈ Ico 112256 112320, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 112256 112320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 112256 112320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-667874 : ℤ) ∧
    (∑ n ∈ Ico 112256 112320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13357602734945336518671725067 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_112320_112384 :
    (∑ n ∈ Ico 112320 112384, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 112320 112384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 112320 112384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (267033 : ℤ) ∧
    (∑ n ∈ Ico 112320 112384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5340715677215483120367335020 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_112256_112384 :
    (∑ n ∈ Ico 112256 112384, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 112256 112384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 112256 112384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-400841 : ℤ) ∧
    (∑ n ∈ Ico 112256 112384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8016887057729853398304390047 : ℤ) := by
  rcases cdemPrefixStats_112256_112320 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_112320_112384 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 112256 ≤ 112320) (by norm_num : 112320 ≤ 112384), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 112256 ≤ 112320) (by norm_num : 112320 ≤ 112384), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 112256 ≤ 112320) (by norm_num : 112320 ≤ 112384), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 112256 ≤ 112320) (by norm_num : 112320 ≤ 112384), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_112128_112384 :
    (∑ n ∈ Ico 112128 112384, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 112128 112384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 112128 112384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-356409 : ℤ) ∧
    (∑ n ∈ Ico 112128 112384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7128267573171124445421735618 : ℤ) := by
  rcases cdemPrefixStats_112128_112256 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_112256_112384 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 112128 ≤ 112256) (by norm_num : 112256 ≤ 112384), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 112128 ≤ 112256) (by norm_num : 112256 ≤ 112384), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 112128 ≤ 112256) (by norm_num : 112256 ≤ 112384), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 112128 ≤ 112256) (by norm_num : 112256 ≤ 112384), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_112384_112448 :
    (∑ n ∈ Ico 112384 112448, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 112384 112448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 112384 112448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (177907 : ℤ) ∧
    (∑ n ∈ Ico 112384 112448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3558172797377075005254593776 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_112448_112512 :
    (∑ n ∈ Ico 112448 112512, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 112448 112512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 112448 112512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (44474 : ℤ) ∧
    (∑ n ∈ Ico 112448 112512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (889450114523965624960430699 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_112384_112512 :
    (∑ n ∈ Ico 112384 112512, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 112384 112512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 112384 112512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (222381 : ℤ) ∧
    (∑ n ∈ Ico 112384 112512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4447622911901040630215024475 : ℤ) := by
  rcases cdemPrefixStats_112384_112448 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_112448_112512 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 112384 ≤ 112448) (by norm_num : 112448 ≤ 112512), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 112384 ≤ 112448) (by norm_num : 112448 ≤ 112512), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 112384 ≤ 112448) (by norm_num : 112448 ≤ 112512), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 112384 ≤ 112448) (by norm_num : 112448 ≤ 112512), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_112512_112576 :
    (∑ n ∈ Ico 112512 112576, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 112512 112576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 112512 112576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (123 : ℤ) ∧
    (∑ n ∈ Ico 112512 112576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2384150670258254396526473 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_112576_112640 :
    (∑ n ∈ Ico 112576 112640, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 112576 112640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 112576 112640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-177644 : ℤ) ∧
    (∑ n ∈ Ico 112576 112640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3552902596156404327411849719 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_112512_112640 :
    (∑ n ∈ Ico 112512 112640, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 112512 112640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 112512 112640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-177521 : ℤ) ∧
    (∑ n ∈ Ico 112512 112640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3550518445486146073015323246 : ℤ) := by
  rcases cdemPrefixStats_112512_112576 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_112576_112640 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 112512 ≤ 112576) (by norm_num : 112576 ≤ 112640), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 112512 ≤ 112576) (by norm_num : 112576 ≤ 112640), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 112512 ≤ 112576) (by norm_num : 112576 ≤ 112640), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 112512 ≤ 112576) (by norm_num : 112576 ≤ 112640), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_112384_112640 :
    (∑ n ∈ Ico 112384 112640, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 112384 112640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 112384 112640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (44860 : ℤ) ∧
    (∑ n ∈ Ico 112384 112640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (897104466414894557199701229 : ℤ) := by
  rcases cdemPrefixStats_112384_112512 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_112512_112640 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 112384 ≤ 112512) (by norm_num : 112512 ≤ 112640), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 112384 ≤ 112512) (by norm_num : 112512 ≤ 112640), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 112384 ≤ 112512) (by norm_num : 112512 ≤ 112640), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 112384 ≤ 112512) (by norm_num : 112512 ≤ 112640), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_112128_112640 :
    (∑ n ∈ Ico 112128 112640, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 112128 112640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 112128 112640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-311549 : ℤ) ∧
    (∑ n ∈ Ico 112128 112640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6231163106756229888222034389 : ℤ) := by
  rcases cdemPrefixStats_112128_112384 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_112384_112640 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 112128 ≤ 112384) (by norm_num : 112384 ≤ 112640), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 112128 ≤ 112384) (by norm_num : 112384 ≤ 112640), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 112128 ≤ 112384) (by norm_num : 112384 ≤ 112640), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 112128 ≤ 112384) (by norm_num : 112384 ≤ 112640), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_111616_112640 :
    (∑ n ∈ Ico 111616 112640, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 111616 112640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (620 : ℕ) ∧
    (∑ n ∈ Ico 111616 112640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (716983 : ℤ) ∧
    (∑ n ∈ Ico 111616 112640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14339653455814813990287643625 : ℤ) := by
  rcases cdemPrefixStats_111616_112128 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_112128_112640 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 111616 ≤ 112128) (by norm_num : 112128 ≤ 112640), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 111616 ≤ 112128) (by norm_num : 112128 ≤ 112640), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 111616 ≤ 112128) (by norm_num : 112128 ≤ 112640), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 111616 ≤ 112128) (by norm_num : 112128 ≤ 112640), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_110592_112640 :
    (∑ n ∈ Ico 110592 112640, mobiusTreeValue 16 mobiusTable1200001 n) = (30 : ℤ) ∧
    (∑ n ∈ Ico 110592 112640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1244 : ℕ) ∧
    (∑ n ∈ Ico 110592 112640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1345641 : ℤ) ∧
    (∑ n ∈ Ico 110592 112640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (26913162656394707978346982763 : ℤ) := by
  rcases cdemPrefixStats_110592_111616 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_111616_112640 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 110592 ≤ 111616) (by norm_num : 111616 ≤ 112640), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 110592 ≤ 111616) (by norm_num : 111616 ≤ 112640), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 110592 ≤ 111616) (by norm_num : 111616 ≤ 112640), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 110592 ≤ 111616) (by norm_num : 111616 ≤ 112640), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_112640_112704 :
    (∑ n ∈ Ico 112640 112704, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 112640 112704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 112640 112704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (399355 : ℤ) ∧
    (∑ n ∈ Ico 112640 112704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7987228413223526410733070026 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_112704_112768 :
    (∑ n ∈ Ico 112704 112768, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 112704 112768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 112704 112768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (221864 : ℤ) ∧
    (∑ n ∈ Ico 112704 112768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4437265206735458125851380775 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_112640_112768 :
    (∑ n ∈ Ico 112640 112768, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 112640 112768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 112640 112768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (621219 : ℤ) ∧
    (∑ n ∈ Ico 112640 112768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12424493619958984536584450801 : ℤ) := by
  rcases cdemPrefixStats_112640_112704 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_112704_112768 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 112640 ≤ 112704) (by norm_num : 112704 ≤ 112768), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 112640 ≤ 112704) (by norm_num : 112704 ≤ 112768), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 112640 ≤ 112704) (by norm_num : 112704 ≤ 112768), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 112640 ≤ 112704) (by norm_num : 112704 ≤ 112768), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_112768_112832 :
    (∑ n ∈ Ico 112768 112832, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 112768 112832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 112768 112832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (310295 : ℤ) ∧
    (∑ n ∈ Ico 112768 112832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6206051199402750575936240759 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_112832_112896 :
    (∑ n ∈ Ico 112832 112896, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 112832 112896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 112832 112896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (177249 : ℤ) ∧
    (∑ n ∈ Ico 112832 112896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3545038450816038803473274703 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_112768_112896 :
    (∑ n ∈ Ico 112768 112896, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 112768 112896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 112768 112896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (487544 : ℤ) ∧
    (∑ n ∈ Ico 112768 112896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9751089650218789379409515462 : ℤ) := by
  rcases cdemPrefixStats_112768_112832 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_112832_112896 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 112768 ≤ 112832) (by norm_num : 112832 ≤ 112896), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 112768 ≤ 112832) (by norm_num : 112832 ≤ 112896), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 112768 ≤ 112832) (by norm_num : 112832 ≤ 112896), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 112768 ≤ 112832) (by norm_num : 112832 ≤ 112896), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_112640_112896 :
    (∑ n ∈ Ico 112640 112896, mobiusTreeValue 16 mobiusTable1200001 n) = (25 : ℤ) ∧
    (∑ n ∈ Ico 112640 112896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 112640 112896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1108763 : ℤ) ∧
    (∑ n ∈ Ico 112640 112896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (22175583270177773915993966263 : ℤ) := by
  rcases cdemPrefixStats_112640_112768 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_112768_112896 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 112640 ≤ 112768) (by norm_num : 112768 ≤ 112896), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 112640 ≤ 112768) (by norm_num : 112768 ≤ 112896), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 112640 ≤ 112768) (by norm_num : 112768 ≤ 112896), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 112640 ≤ 112768) (by norm_num : 112768 ≤ 112896), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_112896_112960 :
    (∑ n ∈ Ico 112896 112960, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 112896 112960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 112896 112960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (221308 : ℤ) ∧
    (∑ n ∈ Ico 112896 112960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4426180750687657912940696258 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_112960_113024 :
    (∑ n ∈ Ico 112960 113024, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 112960 113024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 112960 113024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (59 : ℤ) ∧
    (∑ n ∈ Ico 112960 113024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1174784128043431516020022 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_112896_113024 :
    (∑ n ∈ Ico 112896 113024, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 112896 113024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 112896 113024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (221367 : ℤ) ∧
    (∑ n ∈ Ico 112896 113024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4427355534815701344456716280 : ℤ) := by
  rcases cdemPrefixStats_112896_112960 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_112960_113024 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 112896 ≤ 112960) (by norm_num : 112960 ≤ 113024), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 112896 ≤ 112960) (by norm_num : 112960 ≤ 113024), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 112896 ≤ 112960) (by norm_num : 112960 ≤ 113024), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 112896 ≤ 112960) (by norm_num : 112960 ≤ 113024), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_113024_113088 :
    (∑ n ∈ Ico 113024 113088, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 113024 113088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 113024 113088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-88549 : ℤ) ∧
    (∑ n ∈ Ico 113024 113088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1770975139728150030715522728 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_113088_113152 :
    (∑ n ∈ Ico 113088 113152, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 113088 113152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 113088 113152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-132587 : ℤ) ∧
    (∑ n ∈ Ico 113088 113152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2651722563850761833383254119 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_113024_113152 :
    (∑ n ∈ Ico 113024 113152, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 113024 113152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 113024 113152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-221136 : ℤ) ∧
    (∑ n ∈ Ico 113024 113152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4422697703578911864098776847 : ℤ) := by
  rcases cdemPrefixStats_113024_113088 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_113088_113152 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 113024 ≤ 113088) (by norm_num : 113088 ≤ 113152), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 113024 ≤ 113088) (by norm_num : 113088 ≤ 113152), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 113024 ≤ 113088) (by norm_num : 113088 ≤ 113152), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 113024 ≤ 113088) (by norm_num : 113088 ≤ 113152), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_112896_113152 :
    (∑ n ∈ Ico 112896 113152, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 112896 113152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 112896 113152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (231 : ℤ) ∧
    (∑ n ∈ Ico 112896 113152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4657831236789480357939433 : ℤ) := by
  rcases cdemPrefixStats_112896_113024 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_113024_113152 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 112896 ≤ 113024) (by norm_num : 113024 ≤ 113152), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 112896 ≤ 113024) (by norm_num : 113024 ≤ 113152), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 112896 ≤ 113024) (by norm_num : 113024 ≤ 113152), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 112896 ≤ 113024) (by norm_num : 113024 ≤ 113152), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_112640_113152 :
    (∑ n ∈ Ico 112640 113152, mobiusTreeValue 16 mobiusTable1200001 n) = (25 : ℤ) ∧
    (∑ n ∈ Ico 112640 113152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (307 : ℕ) ∧
    (∑ n ∈ Ico 112640 113152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1108994 : ℤ) ∧
    (∑ n ∈ Ico 112640 113152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (22180241101414563396351905696 : ℤ) := by
  rcases cdemPrefixStats_112640_112896 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_112896_113152 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 112640 ≤ 112896) (by norm_num : 112896 ≤ 113152), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 112640 ≤ 112896) (by norm_num : 112896 ≤ 113152), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 112640 ≤ 112896) (by norm_num : 112896 ≤ 113152), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 112640 ≤ 112896) (by norm_num : 112896 ≤ 113152), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_113152_113216 :
    (∑ n ∈ Ico 113152 113216, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 113152 113216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 113152 113216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-441794 : ℤ) ∧
    (∑ n ∈ Ico 113152 113216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8835952044250883450689438024 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_113216_113280 :
    (∑ n ∈ Ico 113216 113280, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 113216 113280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 113216 113280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (176571 : ℤ) ∧
    (∑ n ∈ Ico 113216 113280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3531385062057208637281853322 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_113152_113280 :
    (∑ n ∈ Ico 113152 113280, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 113152 113280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 113152 113280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-265223 : ℤ) ∧
    (∑ n ∈ Ico 113152 113280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5304566982193674813407584702 : ℤ) := by
  rcases cdemPrefixStats_113152_113216 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_113216_113280 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 113152 ≤ 113216) (by norm_num : 113216 ≤ 113280), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 113152 ≤ 113216) (by norm_num : 113216 ≤ 113280), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 113152 ≤ 113216) (by norm_num : 113216 ≤ 113280), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 113152 ≤ 113216) (by norm_num : 113216 ≤ 113280), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_113280_113344 :
    (∑ n ∈ Ico 113280 113344, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 113280 113344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 113280 113344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-176510 : ℤ) ∧
    (∑ n ∈ Ico 113280 113344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3530317805435716118154485659 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_113344_113408 :
    (∑ n ∈ Ico 113344 113408, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 113344 113408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 113344 113408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (88255 : ℤ) ∧
    (∑ n ∈ Ico 113344 113408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1765131131291407766958255689 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_113280_113408 :
    (∑ n ∈ Ico 113280 113408, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 113280 113408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 113280 113408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-88255 : ℤ) ∧
    (∑ n ∈ Ico 113280 113408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1765186674144308351196229970 : ℤ) := by
  rcases cdemPrefixStats_113280_113344 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_113344_113408 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 113280 ≤ 113344) (by norm_num : 113344 ≤ 113408), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 113280 ≤ 113344) (by norm_num : 113344 ≤ 113408), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 113280 ≤ 113344) (by norm_num : 113344 ≤ 113408), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 113280 ≤ 113344) (by norm_num : 113344 ≤ 113408), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_113152_113408 :
    (∑ n ∈ Ico 113152 113408, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 113152 113408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 113152 113408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-353478 : ℤ) ∧
    (∑ n ∈ Ico 113152 113408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7069753656337983164603814672 : ℤ) := by
  rcases cdemPrefixStats_113152_113280 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_113280_113408 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 113152 ≤ 113280) (by norm_num : 113280 ≤ 113408), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 113152 ≤ 113280) (by norm_num : 113280 ≤ 113408), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 113152 ≤ 113280) (by norm_num : 113280 ≤ 113408), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 113152 ≤ 113280) (by norm_num : 113280 ≤ 113408), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_113408_113472 :
    (∑ n ∈ Ico 113408 113472, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 113408 113472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 113408 113472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (132245 : ℤ) ∧
    (∑ n ∈ Ico 113408 113472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2644942875255489942770779385 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_113472_113536 :
    (∑ n ∈ Ico 113472 113536, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 113472 113536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 113472 113536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (29 : ℤ) ∧
    (∑ n ∈ Ico 113472 113536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (613477864552414839057039 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_113408_113536 :
    (∑ n ∈ Ico 113408 113536, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 113408 113536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 113408 113536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (132274 : ℤ) ∧
    (∑ n ∈ Ico 113408 113536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2645556353120042357609836424 : ℤ) := by
  rcases cdemPrefixStats_113408_113472 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_113472_113536 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 113408 ≤ 113472) (by norm_num : 113472 ≤ 113536), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 113408 ≤ 113472) (by norm_num : 113472 ≤ 113536), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 113408 ≤ 113472) (by norm_num : 113472 ≤ 113536), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 113408 ≤ 113472) (by norm_num : 113472 ≤ 113536), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_113536_113600 :
    (∑ n ∈ Ico 113536 113600, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 113536 113600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 113536 113600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (616355 : ℤ) ∧
    (∑ n ∈ Ico 113536 113600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12327214872603998955793842840 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_113600_113664 :
    (∑ n ∈ Ico 113600 113664, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 113600 113664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 113600 113664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (308003 : ℤ) ∧
    (∑ n ∈ Ico 113600 113664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6160151309982914263718979610 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_113536_113664 :
    (∑ n ∈ Ico 113536 113664, mobiusTreeValue 16 mobiusTable1200001 n) = (21 : ℤ) ∧
    (∑ n ∈ Ico 113536 113664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 113536 113664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (924358 : ℤ) ∧
    (∑ n ∈ Ico 113536 113664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18487366182586913219512822450 : ℤ) := by
  rcases cdemPrefixStats_113536_113600 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_113600_113664 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 113536 ≤ 113600) (by norm_num : 113600 ≤ 113664), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 113536 ≤ 113600) (by norm_num : 113600 ≤ 113664), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 113536 ≤ 113600) (by norm_num : 113600 ≤ 113664), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 113536 ≤ 113600) (by norm_num : 113600 ≤ 113664), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_113408_113664 :
    (∑ n ∈ Ico 113408 113664, mobiusTreeValue 16 mobiusTable1200001 n) = (24 : ℤ) ∧
    (∑ n ∈ Ico 113408 113664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 113408 113664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1056632 : ℤ) ∧
    (∑ n ∈ Ico 113408 113664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (21132922535706955577122658874 : ℤ) := by
  rcases cdemPrefixStats_113408_113536 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_113536_113664 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 113408 ≤ 113536) (by norm_num : 113536 ≤ 113664), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 113408 ≤ 113536) (by norm_num : 113536 ≤ 113664), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 113408 ≤ 113536) (by norm_num : 113536 ≤ 113664), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 113408 ≤ 113536) (by norm_num : 113536 ≤ 113664), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_113152_113664 :
    (∑ n ∈ Ico 113152 113664, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 113152 113664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 113152 113664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (703154 : ℤ) ∧
    (∑ n ∈ Ico 113152 113664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14063168879368972412518844202 : ℤ) := by
  rcases cdemPrefixStats_113152_113408 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_113408_113664 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 113152 ≤ 113408) (by norm_num : 113408 ≤ 113664), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 113152 ≤ 113408) (by norm_num : 113408 ≤ 113664), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 113152 ≤ 113408) (by norm_num : 113408 ≤ 113664), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 113152 ≤ 113408) (by norm_num : 113408 ≤ 113664), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_112640_113664 :
    (∑ n ∈ Ico 112640 113664, mobiusTreeValue 16 mobiusTable1200001 n) = (41 : ℤ) ∧
    (∑ n ∈ Ico 112640 113664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (617 : ℕ) ∧
    (∑ n ∈ Ico 112640 113664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1812148 : ℤ) ∧
    (∑ n ∈ Ico 112640 113664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (36243409980783535808870749898 : ℤ) := by
  rcases cdemPrefixStats_112640_113152 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_113152_113664 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 112640 ≤ 113152) (by norm_num : 113152 ≤ 113664), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 112640 ≤ 113152) (by norm_num : 113152 ≤ 113664), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 112640 ≤ 113152) (by norm_num : 113152 ≤ 113664), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 112640 ≤ 113152) (by norm_num : 113152 ≤ 113664), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_113664_113728 :
    (∑ n ∈ Ico 113664 113728, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 113664 113728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 113664 113728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-131914 : ℤ) ∧
    (∑ n ∈ Ico 113664 113728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2638313687199338099052134538 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_113728_113792 :
    (∑ n ∈ Ico 113728 113792, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 113728 113792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 113728 113792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-43963 : ℤ) ∧
    (∑ n ∈ Ico 113728 113792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-879275382735594154624922418 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_113664_113792 :
    (∑ n ∈ Ico 113664 113792, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 113664 113792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 113664 113792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-175877 : ℤ) ∧
    (∑ n ∈ Ico 113664 113792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3517589069934932253677056956 : ℤ) := by
  rcases cdemPrefixStats_113664_113728 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_113728_113792 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 113664 ≤ 113728) (by norm_num : 113728 ≤ 113792), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 113664 ≤ 113728) (by norm_num : 113728 ≤ 113792), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 113664 ≤ 113728) (by norm_num : 113728 ≤ 113792), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 113664 ≤ 113728) (by norm_num : 113728 ≤ 113792), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_113792_113856 :
    (∑ n ∈ Ico 113792 113856, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 113792 113856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 113792 113856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (43910 : ℤ) ∧
    (∑ n ∈ Ico 113792 113856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (878263726499611106728390151 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_113856_113920 :
    (∑ n ∈ Ico 113856 113920, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 113856 113920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 113856 113920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (746322 : ℤ) ∧
    (∑ n ∈ Ico 113856 113920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14926607077363543856064461920 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_113792_113920 :
    (∑ n ∈ Ico 113792 113920, mobiusTreeValue 16 mobiusTable1200001 n) = (18 : ℤ) ∧
    (∑ n ∈ Ico 113792 113920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 113792 113920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (790232 : ℤ) ∧
    (∑ n ∈ Ico 113792 113920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15804870803863154962792852071 : ℤ) := by
  rcases cdemPrefixStats_113792_113856 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_113856_113920 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 113792 ≤ 113856) (by norm_num : 113856 ≤ 113920), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 113792 ≤ 113856) (by norm_num : 113856 ≤ 113920), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 113792 ≤ 113856) (by norm_num : 113856 ≤ 113920), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 113792 ≤ 113856) (by norm_num : 113856 ≤ 113920), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_113664_113920 :
    (∑ n ∈ Ico 113664 113920, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 113664 113920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 113664 113920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (614355 : ℤ) ∧
    (∑ n ∈ Ico 113664 113920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12287281733928222709115795115 : ℤ) := by
  rcases cdemPrefixStats_113664_113792 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_113792_113920 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 113664 ≤ 113792) (by norm_num : 113792 ≤ 113920), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 113664 ≤ 113792) (by norm_num : 113792 ≤ 113920), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 113664 ≤ 113792) (by norm_num : 113792 ≤ 113920), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 113664 ≤ 113792) (by norm_num : 113792 ≤ 113920), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_113920_113984 :
    (∑ n ∈ Ico 113920 113984, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 113920 113984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 113920 113984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-175497 : ℤ) ∧
    (∑ n ∈ Ico 113920 113984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3509980362105135894321453048 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_113984_114048 :
    (∑ n ∈ Ico 113984 114048, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 113984 114048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 113984 114048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (131598 : ℤ) ∧
    (∑ n ∈ Ico 113984 114048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2632017334511830111923396575 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_113920_114048 :
    (∑ n ∈ Ico 113920 114048, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 113920 114048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 113920 114048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-43899 : ℤ) ∧
    (∑ n ∈ Ico 113920 114048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-877963027593305782398056473 : ℤ) := by
  rcases cdemPrefixStats_113920_113984 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_113984_114048 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 113920 ≤ 113984) (by norm_num : 113984 ≤ 114048), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 113920 ≤ 113984) (by norm_num : 113984 ≤ 114048), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 113920 ≤ 113984) (by norm_num : 113984 ≤ 114048), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 113920 ≤ 113984) (by norm_num : 113984 ≤ 114048), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_114048_114112 :
    (∑ n ∈ Ico 114048 114112, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 114048 114112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 114048 114112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-350630 : ℤ) ∧
    (∑ n ∈ Ico 114048 114112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7012692056598700784562935542 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_114112_114176 :
    (∑ n ∈ Ico 114112 114176, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 114112 114176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 114112 114176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (43899 : ℤ) ∧
    (∑ n ∈ Ico 114112 114176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (877966637091382943800239951 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_114048_114176 :
    (∑ n ∈ Ico 114048 114176, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 114048 114176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 114048 114176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-306731 : ℤ) ∧
    (∑ n ∈ Ico 114048 114176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6134725419507317840762695591 : ℤ) := by
  rcases cdemPrefixStats_114048_114112 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_114112_114176 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 114048 ≤ 114112) (by norm_num : 114112 ≤ 114176), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 114048 ≤ 114112) (by norm_num : 114112 ≤ 114176), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 114048 ≤ 114112) (by norm_num : 114112 ≤ 114176), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 114048 ≤ 114112) (by norm_num : 114112 ≤ 114176), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_113920_114176 :
    (∑ n ∈ Ico 113920 114176, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 113920 114176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 113920 114176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-350630 : ℤ) ∧
    (∑ n ∈ Ico 113920 114176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7012688447100623623160752064 : ℤ) := by
  rcases cdemPrefixStats_113920_114048 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_114048_114176 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 113920 ≤ 114048) (by norm_num : 114048 ≤ 114176), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 113920 ≤ 114048) (by norm_num : 114048 ≤ 114176), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 113920 ≤ 114048) (by norm_num : 114048 ≤ 114176), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 113920 ≤ 114048) (by norm_num : 114048 ≤ 114176), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_113664_114176 :
    (∑ n ∈ Ico 113664 114176, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 113664 114176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 113664 114176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (263725 : ℤ) ∧
    (∑ n ∈ Ico 113664 114176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5274593286827599085955043051 : ℤ) := by
  rcases cdemPrefixStats_113664_113920 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_113920_114176 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 113664 ≤ 113920) (by norm_num : 113920 ≤ 114176), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 113664 ≤ 113920) (by norm_num : 113920 ≤ 114176), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 113664 ≤ 113920) (by norm_num : 113920 ≤ 114176), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 113664 ≤ 113920) (by norm_num : 113920 ≤ 114176), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_114176_114240 :
    (∑ n ∈ Ico 114176 114240, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 114176 114240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 114176 114240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (262617 : ℤ) ∧
    (∑ n ∈ Ico 114176 114240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5252415031471437811415272460 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_114240_114304 :
    (∑ n ∈ Ico 114240 114304, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 114240 114304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 114240 114304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (87509 : ℤ) ∧
    (∑ n ∈ Ico 114240 114304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1750210043302357376379303397 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_114176_114304 :
    (∑ n ∈ Ico 114176 114304, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 114176 114304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (82 : ℕ) ∧
    (∑ n ∈ Ico 114176 114304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (350126 : ℤ) ∧
    (∑ n ∈ Ico 114176 114304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7002625074773795187794575857 : ℤ) := by
  rcases cdemPrefixStats_114176_114240 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_114240_114304 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 114176 ≤ 114240) (by norm_num : 114240 ≤ 114304), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 114176 ≤ 114240) (by norm_num : 114240 ≤ 114304), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 114176 ≤ 114240) (by norm_num : 114240 ≤ 114304), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 114176 ≤ 114240) (by norm_num : 114240 ≤ 114304), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_114304_114368 :
    (∑ n ∈ Ico 114304 114368, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 114304 114368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 114304 114368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-306147 : ℤ) ∧
    (∑ n ∈ Ico 114304 114368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6122956599262320697905254921 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_114368_114432 :
    (∑ n ∈ Ico 114368 114432, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 114368 114432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 114368 114432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (131169 : ℤ) ∧
    (∑ n ∈ Ico 114368 114432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2623393769212922948620193342 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_114304_114432 :
    (∑ n ∈ Ico 114304 114432, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 114304 114432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 114304 114432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-174978 : ℤ) ∧
    (∑ n ∈ Ico 114304 114432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3499562830049397749285061579 : ℤ) := by
  rcases cdemPrefixStats_114304_114368 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_114368_114432 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 114304 ≤ 114368) (by norm_num : 114368 ≤ 114432), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 114304 ≤ 114368) (by norm_num : 114368 ≤ 114432), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 114304 ≤ 114368) (by norm_num : 114368 ≤ 114432), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 114304 ≤ 114368) (by norm_num : 114368 ≤ 114432), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_114176_114432 :
    (∑ n ∈ Ico 114176 114432, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 114176 114432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 114176 114432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (175148 : ℤ) ∧
    (∑ n ∈ Ico 114176 114432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3503062244724397438509514278 : ℤ) := by
  rcases cdemPrefixStats_114176_114304 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_114304_114432 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 114176 ≤ 114304) (by norm_num : 114304 ≤ 114432), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 114176 ≤ 114304) (by norm_num : 114304 ≤ 114432), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 114176 ≤ 114304) (by norm_num : 114304 ≤ 114432), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 114176 ≤ 114304) (by norm_num : 114304 ≤ 114432), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_114432_114496 :
    (∑ n ∈ Ico 114432 114496, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 114432 114496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 114432 114496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-262085 : ℤ) ∧
    (∑ n ∈ Ico 114432 114496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5241761809344775885984499865 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_114496_114560 :
    (∑ n ∈ Ico 114496 114560, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 114496 114560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 114496 114560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (567485 : ℤ) ∧
    (∑ n ∈ Ico 114496 114560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11349808126494113120318000788 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_114432_114560 :
    (∑ n ∈ Ico 114432 114560, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 114432 114560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 114432 114560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (305400 : ℤ) ∧
    (∑ n ∈ Ico 114432 114560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6108046317149337234333500923 : ℤ) := by
  rcases cdemPrefixStats_114432_114496 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_114496_114560 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 114432 ≤ 114496) (by norm_num : 114496 ≤ 114560), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 114432 ≤ 114496) (by norm_num : 114496 ≤ 114560), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 114432 ≤ 114496) (by norm_num : 114496 ≤ 114560), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 114432 ≤ 114496) (by norm_num : 114496 ≤ 114560), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_114560_114624 :
    (∑ n ∈ Ico 114560 114624, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 114560 114624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 114560 114624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (43600 : ℤ) ∧
    (∑ n ∈ Ico 114560 114624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (872029100920515514843854928 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_114624_114688 :
    (∑ n ∈ Ico 114624 114688, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 114624 114688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 114624 114688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-87285 : ℤ) ∧
    (∑ n ∈ Ico 114624 114688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1745732777324381980746122960 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_114560_114688 :
    (∑ n ∈ Ico 114560 114688, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 114560 114688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 114560 114688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-43685 : ℤ) ∧
    (∑ n ∈ Ico 114560 114688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-873703676403866465902268032 : ℤ) := by
  rcases cdemPrefixStats_114560_114624 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_114624_114688 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 114560 ≤ 114624) (by norm_num : 114624 ≤ 114688), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 114560 ≤ 114624) (by norm_num : 114624 ≤ 114688), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 114560 ≤ 114624) (by norm_num : 114624 ≤ 114688), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 114560 ≤ 114624) (by norm_num : 114624 ≤ 114688), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_114432_114688 :
    (∑ n ∈ Ico 114432 114688, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 114432 114688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 114432 114688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (261715 : ℤ) ∧
    (∑ n ∈ Ico 114432 114688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5234342640745470768431232891 : ℤ) := by
  rcases cdemPrefixStats_114432_114560 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_114560_114688 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 114432 ≤ 114560) (by norm_num : 114560 ≤ 114688), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 114432 ≤ 114560) (by norm_num : 114560 ≤ 114688), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 114432 ≤ 114560) (by norm_num : 114560 ≤ 114688), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 114432 ≤ 114560) (by norm_num : 114560 ≤ 114688), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_114176_114688 :
    (∑ n ∈ Ico 114176 114688, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 114176 114688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 114176 114688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (436863 : ℤ) ∧
    (∑ n ∈ Ico 114176 114688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8737404885469868206940747169 : ℤ) := by
  rcases cdemPrefixStats_114176_114432 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_114432_114688 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 114176 ≤ 114432) (by norm_num : 114432 ≤ 114688), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 114176 ≤ 114432) (by norm_num : 114432 ≤ 114688), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 114176 ≤ 114432) (by norm_num : 114432 ≤ 114688), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 114176 ≤ 114432) (by norm_num : 114432 ≤ 114688), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_113664_114688 :
    (∑ n ∈ Ico 113664 114688, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 113664 114688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (624 : ℕ) ∧
    (∑ n ∈ Ico 113664 114688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (700588 : ℤ) ∧
    (∑ n ∈ Ico 113664 114688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14011998172297467292895790220 : ℤ) := by
  rcases cdemPrefixStats_113664_114176 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_114176_114688 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 113664 ≤ 114176) (by norm_num : 114176 ≤ 114688), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 113664 ≤ 114176) (by norm_num : 114176 ≤ 114688), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 113664 ≤ 114176) (by norm_num : 114176 ≤ 114688), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 113664 ≤ 114176) (by norm_num : 114176 ≤ 114688), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_112640_114688 :
    (∑ n ∈ Ico 112640 114688, mobiusTreeValue 16 mobiusTable1200001 n) = (57 : ℤ) ∧
    (∑ n ∈ Ico 112640 114688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1241 : ℕ) ∧
    (∑ n ∈ Ico 112640 114688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2512736 : ℤ) ∧
    (∑ n ∈ Ico 112640 114688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (50255408153081003101766540118 : ℤ) := by
  rcases cdemPrefixStats_112640_113664 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_113664_114688 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 112640 ≤ 113664) (by norm_num : 113664 ≤ 114688), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 112640 ≤ 113664) (by norm_num : 113664 ≤ 114688), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 112640 ≤ 113664) (by norm_num : 113664 ≤ 114688), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 112640 ≤ 113664) (by norm_num : 113664 ≤ 114688), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_110592_114688 :
    (∑ n ∈ Ico 110592 114688, mobiusTreeValue 16 mobiusTable1200001 n) = (87 : ℤ) ∧
    (∑ n ∈ Ico 110592 114688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2485 : ℕ) ∧
    (∑ n ∈ Ico 110592 114688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3858377 : ℤ) ∧
    (∑ n ∈ Ico 110592 114688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (77168570809475711080113522881 : ℤ) := by
  rcases cdemPrefixStats_110592_112640 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_112640_114688 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 110592 ≤ 112640) (by norm_num : 112640 ≤ 114688), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 110592 ≤ 112640) (by norm_num : 112640 ≤ 114688), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 110592 ≤ 112640) (by norm_num : 112640 ≤ 114688), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 110592 ≤ 112640) (by norm_num : 112640 ≤ 114688), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup027_checked_complete :
    (∑ n ∈ Ico 110592 114688, mobiusTreeValue 16 mobiusTable1200001 n) = (87 : ℤ) ∧
    (∑ n ∈ Ico 110592 114688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2485 : ℕ) ∧
    (∑ n ∈ Ico 110592 114688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3858377 : ℤ) ∧
    (∑ n ∈ Ico 110592 114688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (77168570809475711080113522881 : ℤ) := cdemPrefixStats_110592_114688
end Helfgott
#print axioms Helfgott.cdemPrefixGroup027_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 110592 114688, mobiusTreeValue 16 mobiusTable1200001 n) = (87 : ℤ) ∧
    (∑ n ∈ Ico 110592 114688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2485 : ℕ) ∧
    (∑ n ∈ Ico 110592 114688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3858377 : ℤ) ∧
    (∑ n ∈ Ico 110592 114688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (77168570809475711080113522881 : ℤ) := Helfgott.cdemPrefixGroup027_checked_complete
#print axioms solution
