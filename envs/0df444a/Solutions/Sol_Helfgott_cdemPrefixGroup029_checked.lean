-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup029_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T02:20:44.335278+00:00
-- url     : https://prove2.me/submissions/4b154e4e-b4cd-464d-b349-d84bcae76844

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
private theorem cdemPrefixStats_118784_118848 :
    (∑ n ∈ Ico 118784 118848, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 118784 118848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 118784 118848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (294514 : ℤ) ∧
    (∑ n ∈ Ico 118784 118848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5890272635722447375347018393 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_118848_118912 :
    (∑ n ∈ Ico 118848 118912, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 118848 118912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 118848 118912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (23 : ℤ) ∧
    (∑ n ∈ Ico 118848 118912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (438541808273645957678313 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_118784_118912 :
    (∑ n ∈ Ico 118784 118912, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 118784 118912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 118784 118912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (294537 : ℤ) ∧
    (∑ n ∈ Ico 118784 118912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5890711177530721021304696706 : ℤ) := by
  rcases cdemPrefixStats_118784_118848 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_118848_118912 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 118784 ≤ 118848) (by norm_num : 118848 ≤ 118912), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 118784 ≤ 118848) (by norm_num : 118848 ≤ 118912), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 118784 ≤ 118848) (by norm_num : 118848 ≤ 118912), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 118784 ≤ 118848) (by norm_num : 118848 ≤ 118912), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_118912_118976 :
    (∑ n ∈ Ico 118912 118976, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 118912 118976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 118912 118976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-126151 : ℤ) ∧
    (∑ n ∈ Ico 118912 118976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2523015528695152933525222613 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_118976_119040 :
    (∑ n ∈ Ico 118976 119040, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 118976 119040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 118976 119040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (252102 : ℤ) ∧
    (∑ n ∈ Ico 118976 119040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5042157974329493421293743640 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_118912_119040 :
    (∑ n ∈ Ico 118912 119040, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 118912 119040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 118912 119040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (125951 : ℤ) ∧
    (∑ n ∈ Ico 118912 119040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2519142445634340487768521027 : ℤ) := by
  rcases cdemPrefixStats_118912_118976 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_118976_119040 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 118912 ≤ 118976) (by norm_num : 118976 ≤ 119040), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 118912 ≤ 118976) (by norm_num : 118976 ≤ 119040), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 118912 ≤ 118976) (by norm_num : 118976 ≤ 119040), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 118912 ≤ 118976) (by norm_num : 118976 ≤ 119040), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_118784_119040 :
    (∑ n ∈ Ico 118784 119040, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 118784 119040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 118784 119040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (420488 : ℤ) ∧
    (∑ n ∈ Ico 118784 119040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8409853623165061509073217733 : ℤ) := by
  rcases cdemPrefixStats_118784_118912 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_118912_119040 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 118784 ≤ 118912) (by norm_num : 118912 ≤ 119040), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 118784 ≤ 118912) (by norm_num : 118912 ≤ 119040), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 118784 ≤ 118912) (by norm_num : 118912 ≤ 119040), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 118784 ≤ 118912) (by norm_num : 118912 ≤ 119040), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_119040_119104 :
    (∑ n ∈ Ico 119040 119104, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 119040 119104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 119040 119104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-252005 : ℤ) ∧
    (∑ n ∈ Ico 119040 119104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5040110670586925539445045809 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_119104_119168 :
    (∑ n ∈ Ico 119104 119168, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 119104 119168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 119104 119168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (503644 : ℤ) ∧
    (∑ n ∈ Ico 119104 119168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10073029746193427218485769003 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_119040_119168 :
    (∑ n ∈ Ico 119040 119168, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 119040 119168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 119040 119168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (251639 : ℤ) ∧
    (∑ n ∈ Ico 119040 119168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5032919075606501679040723194 : ℤ) := by
  rcases cdemPrefixStats_119040_119104 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_119104_119168 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 119040 ≤ 119104) (by norm_num : 119104 ≤ 119168), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 119040 ≤ 119104) (by norm_num : 119104 ≤ 119168), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 119040 ≤ 119104) (by norm_num : 119104 ≤ 119168), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 119040 ≤ 119104) (by norm_num : 119104 ≤ 119168), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_119168_119232 :
    (∑ n ∈ Ico 119168 119232, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 119168 119232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 119168 119232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-419494 : ℤ) ∧
    (∑ n ∈ Ico 119168 119232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8389937514096832496131496002 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_119232_119296 :
    (∑ n ∈ Ico 119232 119296, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 119232 119296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 119232 119296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-83883 : ℤ) ∧
    (∑ n ∈ Ico 119232 119296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1677690376941147949718900103 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_119168_119296 :
    (∑ n ∈ Ico 119168 119296, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 119168 119296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 119168 119296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-503377 : ℤ) ∧
    (∑ n ∈ Ico 119168 119296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10067627891037980445850396105 : ℤ) := by
  rcases cdemPrefixStats_119168_119232 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_119232_119296 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 119168 ≤ 119232) (by norm_num : 119232 ≤ 119296), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 119168 ≤ 119232) (by norm_num : 119232 ≤ 119296), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 119168 ≤ 119232) (by norm_num : 119232 ≤ 119296), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 119168 ≤ 119232) (by norm_num : 119232 ≤ 119296), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_119040_119296 :
    (∑ n ∈ Ico 119040 119296, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 119040 119296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 119040 119296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-251738 : ℤ) ∧
    (∑ n ∈ Ico 119040 119296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5034708815431478766809672911 : ℤ) := by
  rcases cdemPrefixStats_119040_119168 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_119168_119296 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 119040 ≤ 119168) (by norm_num : 119168 ≤ 119296), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 119040 ≤ 119168) (by norm_num : 119168 ≤ 119296), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 119040 ≤ 119168) (by norm_num : 119168 ≤ 119296), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 119040 ≤ 119168) (by norm_num : 119168 ≤ 119296), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_118784_119296 :
    (∑ n ∈ Ico 118784 119296, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 118784 119296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 118784 119296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (168750 : ℤ) ∧
    (∑ n ∈ Ico 118784 119296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3375144807733582742263544822 : ℤ) := by
  rcases cdemPrefixStats_118784_119040 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_119040_119296 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 118784 ≤ 119040) (by norm_num : 119040 ≤ 119296), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 118784 ≤ 119040) (by norm_num : 119040 ≤ 119296), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 118784 ≤ 119040) (by norm_num : 119040 ≤ 119296), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 118784 ≤ 119040) (by norm_num : 119040 ≤ 119296), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_119296_119360 :
    (∑ n ∈ Ico 119296 119360, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 119296 119360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 119296 119360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (83788 : ℤ) ∧
    (∑ n ∈ Ico 119296 119360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1675792692589172542377634235 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_119360_119424 :
    (∑ n ∈ Ico 119360 119424, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 119360 119424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 119360 119424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (83701 : ℤ) ∧
    (∑ n ∈ Ico 119360 119424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1674073706709249756526768931 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_119296_119424 :
    (∑ n ∈ Ico 119296 119424, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 119296 119424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 119296 119424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (167489 : ℤ) ∧
    (∑ n ∈ Ico 119296 119424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3349866399298422298904403166 : ℤ) := by
  rcases cdemPrefixStats_119296_119360 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_119360_119424 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 119296 ≤ 119360) (by norm_num : 119360 ≤ 119424), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 119296 ≤ 119360) (by norm_num : 119360 ≤ 119424), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 119296 ≤ 119360) (by norm_num : 119360 ≤ 119424), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 119296 ≤ 119360) (by norm_num : 119360 ≤ 119424), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_119424_119488 :
    (∑ n ∈ Ico 119424 119488, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 119424 119488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 119424 119488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (585946 : ℤ) ∧
    (∑ n ∈ Ico 119424 119488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11719039725753434676652870385 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_119488_119552 :
    (∑ n ∈ Ico 119488 119552, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 119488 119552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 119488 119552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (41802 : ℤ) ∧
    (∑ n ∈ Ico 119488 119552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (836049935397039721517481050 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_119424_119552 :
    (∑ n ∈ Ico 119424 119552, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 119424 119552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 119424 119552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (627748 : ℤ) ∧
    (∑ n ∈ Ico 119424 119552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12555089661150474398170351435 : ℤ) := by
  rcases cdemPrefixStats_119424_119488 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_119488_119552 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 119424 ≤ 119488) (by norm_num : 119488 ≤ 119552), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 119424 ≤ 119488) (by norm_num : 119488 ≤ 119552), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 119424 ≤ 119488) (by norm_num : 119488 ≤ 119552), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 119424 ≤ 119488) (by norm_num : 119488 ≤ 119552), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_119296_119552 :
    (∑ n ∈ Ico 119296 119552, mobiusTreeValue 16 mobiusTable1200001 n) = (19 : ℤ) ∧
    (∑ n ∈ Ico 119296 119552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 119296 119552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (795237 : ℤ) ∧
    (∑ n ∈ Ico 119296 119552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15904956060448896697074754601 : ℤ) := by
  rcases cdemPrefixStats_119296_119424 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_119424_119552 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 119296 ≤ 119424) (by norm_num : 119424 ≤ 119552), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 119296 ≤ 119424) (by norm_num : 119424 ≤ 119552), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 119296 ≤ 119424) (by norm_num : 119424 ≤ 119552), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 119296 ≤ 119424) (by norm_num : 119424 ≤ 119552), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_119552_119616 :
    (∑ n ∈ Ico 119552 119616, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 119552 119616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 119552 119616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-167228 : ℤ) ∧
    (∑ n ∈ Ico 119552 119616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3344614760288771040942753947 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_119616_119680 :
    (∑ n ∈ Ico 119616 119680, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 119616 119680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 119616 119680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-167174 : ℤ) ∧
    (∑ n ∈ Ico 119616 119680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3343524243069370363820342061 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_119552_119680 :
    (∑ n ∈ Ico 119552 119680, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 119552 119680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 119552 119680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-334402 : ℤ) ∧
    (∑ n ∈ Ico 119552 119680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6688139003358141404763096008 : ℤ) := by
  rcases cdemPrefixStats_119552_119616 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_119616_119680 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 119552 ≤ 119616) (by norm_num : 119616 ≤ 119680), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 119552 ≤ 119616) (by norm_num : 119616 ≤ 119680), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 119552 ≤ 119616) (by norm_num : 119616 ≤ 119680), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 119552 ≤ 119616) (by norm_num : 119616 ≤ 119680), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_119680_119744 :
    (∑ n ∈ Ico 119680 119744, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 119680 119744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 119680 119744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-41777 : ℤ) ∧
    (∑ n ∈ Ico 119680 119744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-835554425607078132929676826 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_119744_119808 :
    (∑ n ∈ Ico 119744 119808, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 119744 119808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 119744 119808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-125287 : ℤ) ∧
    (∑ n ∈ Ico 119744 119808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2505734890533332994437573728 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_119680_119808 :
    (∑ n ∈ Ico 119680 119808, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 119680 119808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 119680 119808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-167064 : ℤ) ∧
    (∑ n ∈ Ico 119680 119808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3341289316140411127367250554 : ℤ) := by
  rcases cdemPrefixStats_119680_119744 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_119744_119808 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 119680 ≤ 119744) (by norm_num : 119744 ≤ 119808), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 119680 ≤ 119744) (by norm_num : 119744 ≤ 119808), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 119680 ≤ 119744) (by norm_num : 119744 ≤ 119808), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 119680 ≤ 119744) (by norm_num : 119744 ≤ 119808), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_119552_119808 :
    (∑ n ∈ Ico 119552 119808, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 119552 119808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 119552 119808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-501466 : ℤ) ∧
    (∑ n ∈ Ico 119552 119808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10029428319498552532130346562 : ℤ) := by
  rcases cdemPrefixStats_119552_119680 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_119680_119808 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 119552 ≤ 119680) (by norm_num : 119680 ≤ 119808), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 119552 ≤ 119680) (by norm_num : 119680 ≤ 119808), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 119552 ≤ 119680) (by norm_num : 119680 ≤ 119808), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 119552 ≤ 119680) (by norm_num : 119680 ≤ 119808), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_119296_119808 :
    (∑ n ∈ Ico 119296 119808, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 119296 119808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 119296 119808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (293771 : ℤ) ∧
    (∑ n ∈ Ico 119296 119808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5875527740950344164944408039 : ℤ) := by
  rcases cdemPrefixStats_119296_119552 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_119552_119808 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 119296 ≤ 119552) (by norm_num : 119552 ≤ 119808), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 119296 ≤ 119552) (by norm_num : 119552 ≤ 119808), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 119296 ≤ 119552) (by norm_num : 119552 ≤ 119808), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 119296 ≤ 119552) (by norm_num : 119552 ≤ 119808), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_118784_119808 :
    (∑ n ∈ Ico 118784 119808, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 118784 119808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (623 : ℕ) ∧
    (∑ n ∈ Ico 118784 119808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (462521 : ℤ) ∧
    (∑ n ∈ Ico 118784 119808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9250672548683926907207952861 : ℤ) := by
  rcases cdemPrefixStats_118784_119296 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_119296_119808 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 118784 ≤ 119296) (by norm_num : 119296 ≤ 119808), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 118784 ≤ 119296) (by norm_num : 119296 ≤ 119808), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 118784 ≤ 119296) (by norm_num : 119296 ≤ 119808), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 118784 ≤ 119296) (by norm_num : 119296 ≤ 119808), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_119808_119872 :
    (∑ n ∈ Ico 119808 119872, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 119808 119872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 119808 119872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-250367 : ℤ) ∧
    (∑ n ∈ Ico 119808 119872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5007399900028217675075079236 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_119872_119936 :
    (∑ n ∈ Ico 119872 119936, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 119872 119936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 119872 119936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-375299 : ℤ) ∧
    (∑ n ∈ Ico 119872 119936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7505970209959783535794143979 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_119808_119936 :
    (∑ n ∈ Ico 119808 119936, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 119808 119936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 119808 119936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-625666 : ℤ) ∧
    (∑ n ∈ Ico 119808 119936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12513370109988001210869223215 : ℤ) := by
  rcases cdemPrefixStats_119808_119872 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_119872_119936 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 119808 ≤ 119872) (by norm_num : 119872 ≤ 119936), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 119808 ≤ 119872) (by norm_num : 119872 ≤ 119936), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 119808 ≤ 119872) (by norm_num : 119872 ≤ 119936), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 119808 ≤ 119872) (by norm_num : 119872 ≤ 119936), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_119936_120000 :
    (∑ n ∈ Ico 119936 120000, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 119936 120000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 119936 120000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (83390 : ℤ) ∧
    (∑ n ∈ Ico 119936 120000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1667827092548207162698561940 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_120000_120064 :
    (∑ n ∈ Ico 120000 120064, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 120000 120064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 120000 120064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-83244 : ℤ) ∧
    (∑ n ∈ Ico 120000 120064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1664980082703452887137796381 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_119936_120064 :
    (∑ n ∈ Ico 119936 120064, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 119936 120064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 119936 120064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (146 : ℤ) ∧
    (∑ n ∈ Ico 119936 120064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2847009844754275560765559 : ℤ) := by
  rcases cdemPrefixStats_119936_120000 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_120000_120064 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 119936 ≤ 120000) (by norm_num : 120000 ≤ 120064), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 119936 ≤ 120000) (by norm_num : 120000 ≤ 120064), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 119936 ≤ 120000) (by norm_num : 120000 ≤ 120064), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 119936 ≤ 120000) (by norm_num : 120000 ≤ 120064), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_119808_120064 :
    (∑ n ∈ Ico 119808 120064, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 119808 120064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 119808 120064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-625520 : ℤ) ∧
    (∑ n ∈ Ico 119808 120064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12510523100143246935308457656 : ℤ) := by
  rcases cdemPrefixStats_119808_119936 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_119936_120064 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 119808 ≤ 119936) (by norm_num : 119936 ≤ 120064), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 119808 ≤ 119936) (by norm_num : 119936 ≤ 120064), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 119808 ≤ 119936) (by norm_num : 119936 ≤ 120064), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 119808 ≤ 119936) (by norm_num : 119936 ≤ 120064), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_120064_120128 :
    (∑ n ∈ Ico 120064 120128, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 120064 120128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 120064 120128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (124864 : ℤ) ∧
    (∑ n ∈ Ico 120064 120128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2497273496220503665911750547 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_120128_120192 :
    (∑ n ∈ Ico 120128 120192, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 120128 120192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 120128 120192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (166391 : ℤ) ∧
    (∑ n ∈ Ico 120128 120192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3327828305534892010056382255 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_120064_120192 :
    (∑ n ∈ Ico 120064 120192, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 120064 120192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 120064 120192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (291255 : ℤ) ∧
    (∑ n ∈ Ico 120064 120192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5825101801755395675968132802 : ℤ) := by
  rcases cdemPrefixStats_120064_120128 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_120128_120192 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 120064 ≤ 120128) (by norm_num : 120128 ≤ 120192), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 120064 ≤ 120128) (by norm_num : 120128 ≤ 120192), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 120064 ≤ 120128) (by norm_num : 120128 ≤ 120192), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 120064 ≤ 120128) (by norm_num : 120128 ≤ 120192), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_120192_120256 :
    (∑ n ∈ Ico 120192 120256, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 120192 120256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 120192 120256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-291119 : ℤ) ∧
    (∑ n ∈ Ico 120192 120256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5822437340258279403044090050 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_120256_120320 :
    (∑ n ∈ Ico 120256 120320, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 120256 120320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 120256 120320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (374065 : ℤ) ∧
    (∑ n ∈ Ico 120256 120320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7481352294546000123753111542 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_120192_120320 :
    (∑ n ∈ Ico 120192 120320, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 120192 120320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 120192 120320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (82946 : ℤ) ∧
    (∑ n ∈ Ico 120192 120320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1658914954287720720709021492 : ℤ) := by
  rcases cdemPrefixStats_120192_120256 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_120256_120320 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 120192 ≤ 120256) (by norm_num : 120256 ≤ 120320), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 120192 ≤ 120256) (by norm_num : 120256 ≤ 120320), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 120192 ≤ 120256) (by norm_num : 120256 ≤ 120320), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 120192 ≤ 120256) (by norm_num : 120256 ≤ 120320), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_120064_120320 :
    (∑ n ∈ Ico 120064 120320, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 120064 120320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 120064 120320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (374201 : ℤ) ∧
    (∑ n ∈ Ico 120064 120320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7484016756043116396677154294 : ℤ) := by
  rcases cdemPrefixStats_120064_120192 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_120192_120320 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 120064 ≤ 120192) (by norm_num : 120192 ≤ 120320), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 120064 ≤ 120192) (by norm_num : 120192 ≤ 120320), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 120064 ≤ 120192) (by norm_num : 120192 ≤ 120320), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 120064 ≤ 120192) (by norm_num : 120192 ≤ 120320), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_119808_120320 :
    (∑ n ∈ Ico 119808 120320, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 119808 120320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 119808 120320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-251319 : ℤ) ∧
    (∑ n ∈ Ico 119808 120320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5026506344100130538631303362 : ℤ) := by
  rcases cdemPrefixStats_119808_120064 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_120064_120320 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 119808 ≤ 120064) (by norm_num : 120064 ≤ 120320), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 119808 ≤ 120064) (by norm_num : 120064 ≤ 120320), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 119808 ≤ 120064) (by norm_num : 120064 ≤ 120320), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 119808 ≤ 120064) (by norm_num : 120064 ≤ 120320), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_120320_120384 :
    (∑ n ∈ Ico 120320 120384, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 120320 120384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 120320 120384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (83182 : ℤ) ∧
    (∑ n ∈ Ico 120320 120384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1663676672273523537526613035 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_120384_120448 :
    (∑ n ∈ Ico 120384 120448, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 120384 120448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 120384 120448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-83071 : ℤ) ∧
    (∑ n ∈ Ico 120384 120448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1661467319421657563484961502 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_120320_120448 :
    (∑ n ∈ Ico 120320 120448, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 120320 120448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 120320 120448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (111 : ℤ) ∧
    (∑ n ∈ Ico 120320 120448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2209352851865974041651533 : ℤ) := by
  rcases cdemPrefixStats_120320_120384 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_120384_120448 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 120320 ≤ 120384) (by norm_num : 120384 ≤ 120448), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 120320 ≤ 120384) (by norm_num : 120384 ≤ 120448), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 120320 ≤ 120384) (by norm_num : 120384 ≤ 120448), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 120320 ≤ 120384) (by norm_num : 120384 ≤ 120448), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_120448_120512 :
    (∑ n ∈ Ico 120448 120512, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 120448 120512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 120448 120512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (456552 : ℤ) ∧
    (∑ n ∈ Ico 120448 120512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9131110885687175047332646318 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_120512_120576 :
    (∑ n ∈ Ico 120512 120576, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 120512 120576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 120512 120576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (248930 : ℤ) ∧
    (∑ n ∈ Ico 120512 120576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4978708967514500204899257549 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_120448_120576 :
    (∑ n ∈ Ico 120448 120576, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 120448 120576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 120448 120576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (705482 : ℤ) ∧
    (∑ n ∈ Ico 120448 120576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14109819853201675252231903867 : ℤ) := by
  rcases cdemPrefixStats_120448_120512 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_120512_120576 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 120448 ≤ 120512) (by norm_num : 120512 ≤ 120576), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 120448 ≤ 120512) (by norm_num : 120512 ≤ 120576), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 120448 ≤ 120512) (by norm_num : 120512 ≤ 120576), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 120448 ≤ 120512) (by norm_num : 120512 ≤ 120576), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_120320_120576 :
    (∑ n ∈ Ico 120320 120576, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 120320 120576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 120320 120576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (705593 : ℤ) ∧
    (∑ n ∈ Ico 120320 120576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14112029206053541226273555400 : ℤ) := by
  rcases cdemPrefixStats_120320_120448 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_120448_120576 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 120320 ≤ 120448) (by norm_num : 120448 ≤ 120576), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 120320 ≤ 120448) (by norm_num : 120448 ≤ 120576), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 120320 ≤ 120448) (by norm_num : 120448 ≤ 120576), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 120320 ≤ 120448) (by norm_num : 120448 ≤ 120576), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_120576_120640 :
    (∑ n ∈ Ico 120576 120640, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 120576 120640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 120576 120640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-207271 : ℤ) ∧
    (∑ n ∈ Ico 120576 120640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4145442000711562725224582440 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_120640_120704 :
    (∑ n ∈ Ico 120640 120704, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 120640 120704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 120640 120704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-165762 : ℤ) ∧
    (∑ n ∈ Ico 120640 120704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3315347717084368415541820686 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_120576_120704 :
    (∑ n ∈ Ico 120576 120704, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 120576 120704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 120576 120704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-373033 : ℤ) ∧
    (∑ n ∈ Ico 120576 120704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7460789717795931140766403126 : ℤ) := by
  rcases cdemPrefixStats_120576_120640 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_120640_120704 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 120576 ≤ 120640) (by norm_num : 120640 ≤ 120704), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 120576 ≤ 120640) (by norm_num : 120640 ≤ 120704), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 120576 ≤ 120640) (by norm_num : 120640 ≤ 120704), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 120576 ≤ 120640) (by norm_num : 120640 ≤ 120704), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_120704_120768 :
    (∑ n ∈ Ico 120704 120768, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 120704 120768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 120704 120768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-331315 : ℤ) ∧
    (∑ n ∈ Ico 120704 120768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6626424871086247924344115853 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_120768_120832 :
    (∑ n ∈ Ico 120768 120832, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 120768 120832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 120768 120832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (41385 : ℤ) ∧
    (∑ n ∈ Ico 120768 120832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (827602160835468808262149738 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_120704_120832 :
    (∑ n ∈ Ico 120704 120832, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 120704 120832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 120704 120832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-289930 : ℤ) ∧
    (∑ n ∈ Ico 120704 120832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5798822710250779116081966115 : ℤ) := by
  rcases cdemPrefixStats_120704_120768 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_120768_120832 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 120704 ≤ 120768) (by norm_num : 120768 ≤ 120832), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 120704 ≤ 120768) (by norm_num : 120768 ≤ 120832), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 120704 ≤ 120768) (by norm_num : 120768 ≤ 120832), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 120704 ≤ 120768) (by norm_num : 120768 ≤ 120832), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_120576_120832 :
    (∑ n ∈ Ico 120576 120832, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 120576 120832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 120576 120832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-662963 : ℤ) ∧
    (∑ n ∈ Ico 120576 120832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13259612428046710256848369241 : ℤ) := by
  rcases cdemPrefixStats_120576_120704 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_120704_120832 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 120576 ≤ 120704) (by norm_num : 120704 ≤ 120832), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 120576 ≤ 120704) (by norm_num : 120704 ≤ 120832), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 120576 ≤ 120704) (by norm_num : 120704 ≤ 120832), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 120576 ≤ 120704) (by norm_num : 120704 ≤ 120832), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_120320_120832 :
    (∑ n ∈ Ico 120320 120832, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 120320 120832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 120320 120832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (42630 : ℤ) ∧
    (∑ n ∈ Ico 120320 120832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (852416778006830969425186159 : ℤ) := by
  rcases cdemPrefixStats_120320_120576 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_120576_120832 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 120320 ≤ 120576) (by norm_num : 120576 ≤ 120832), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 120320 ≤ 120576) (by norm_num : 120576 ≤ 120832), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 120320 ≤ 120576) (by norm_num : 120576 ≤ 120832), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 120320 ≤ 120576) (by norm_num : 120576 ≤ 120832), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_119808_120832 :
    (∑ n ∈ Ico 119808 120832, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 119808 120832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (623 : ℕ) ∧
    (∑ n ∈ Ico 119808 120832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-208689 : ℤ) ∧
    (∑ n ∈ Ico 119808 120832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4174089566093299569206117203 : ℤ) := by
  rcases cdemPrefixStats_119808_120320 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_120320_120832 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 119808 ≤ 120320) (by norm_num : 120320 ≤ 120832), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 119808 ≤ 120320) (by norm_num : 120320 ≤ 120832), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 119808 ≤ 120320) (by norm_num : 120320 ≤ 120832), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 119808 ≤ 120320) (by norm_num : 120320 ≤ 120832), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_118784_120832 :
    (∑ n ∈ Ico 118784 120832, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 118784 120832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1246 : ℕ) ∧
    (∑ n ∈ Ico 118784 120832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (253832 : ℤ) ∧
    (∑ n ∈ Ico 118784 120832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5076582982590627338001835658 : ℤ) := by
  rcases cdemPrefixStats_118784_119808 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_119808_120832 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 118784 ≤ 119808) (by norm_num : 119808 ≤ 120832), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 118784 ≤ 119808) (by norm_num : 119808 ≤ 120832), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 118784 ≤ 119808) (by norm_num : 119808 ≤ 120832), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 118784 ≤ 119808) (by norm_num : 119808 ≤ 120832), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_120832_120896 :
    (∑ n ∈ Ico 120832 120896, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 120832 120896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 120832 120896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-289536 : ℤ) ∧
    (∑ n ∈ Ico 120832 120896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5790757530216100417304519145 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_120896_120960 :
    (∑ n ∈ Ico 120896 120960, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 120896 120960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 120896 120960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-620195 : ℤ) ∧
    (∑ n ∈ Ico 120896 120960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12404075464512474484792343085 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_120832_120960 :
    (∑ n ∈ Ico 120832 120960, mobiusTreeValue 16 mobiusTable1200001 n) = (-22 : ℤ) ∧
    (∑ n ∈ Ico 120832 120960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 120832 120960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-909731 : ℤ) ∧
    (∑ n ∈ Ico 120832 120960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-18194832994728574902096862230 : ℤ) := by
  rcases cdemPrefixStats_120832_120896 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_120896_120960 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 120832 ≤ 120896) (by norm_num : 120896 ≤ 120960), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 120832 ≤ 120896) (by norm_num : 120896 ≤ 120960), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 120832 ≤ 120896) (by norm_num : 120896 ≤ 120960), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 120832 ≤ 120896) (by norm_num : 120896 ≤ 120960), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_120960_121024 :
    (∑ n ∈ Ico 120960 121024, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 120960 121024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 120960 121024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-578539 : ℤ) ∧
    (∑ n ∈ Ico 120960 121024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11570985903575483976099264388 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_121024_121088 :
    (∑ n ∈ Ico 121024 121088, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 121024 121088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 121024 121088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (41332 : ℤ) ∧
    (∑ n ∈ Ico 121024 121088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (826637326166853788542167073 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_120960_121088 :
    (∑ n ∈ Ico 120960 121088, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 120960 121088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 120960 121088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-537207 : ℤ) ∧
    (∑ n ∈ Ico 120960 121088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10744348577408630187557097315 : ℤ) := by
  rcases cdemPrefixStats_120960_121024 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_121024_121088 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 120960 ≤ 121024) (by norm_num : 121024 ≤ 121088), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 120960 ≤ 121024) (by norm_num : 121024 ≤ 121088), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 120960 ≤ 121024) (by norm_num : 121024 ≤ 121088), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 120960 ≤ 121024) (by norm_num : 121024 ≤ 121088), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_120832_121088 :
    (∑ n ∈ Ico 120832 121088, mobiusTreeValue 16 mobiusTable1200001 n) = (-35 : ℤ) ∧
    (∑ n ∈ Ico 120832 121088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 120832 121088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1446938 : ℤ) ∧
    (∑ n ∈ Ico 120832 121088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-28939181572137205089653959545 : ℤ) := by
  rcases cdemPrefixStats_120832_120960 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_120960_121088 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 120832 ≤ 120960) (by norm_num : 120960 ≤ 121088), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 120832 ≤ 120960) (by norm_num : 120960 ≤ 121088), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 120832 ≤ 120960) (by norm_num : 120960 ≤ 121088), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 120832 ≤ 120960) (by norm_num : 120960 ≤ 121088), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_121088_121152 :
    (∑ n ∈ Ico 121088 121152, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 121088 121152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 121088 121152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-165155 : ℤ) ∧
    (∑ n ∈ Ico 121088 121152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3303164443129621946691815238 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_121152_121216 :
    (∑ n ∈ Ico 121152 121216, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 121152 121216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 121152 121216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-82563 : ℤ) ∧
    (∑ n ∈ Ico 121152 121216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1651268117880895736090122115 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_121088_121216 :
    (∑ n ∈ Ico 121088 121216, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 121088 121216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 121088 121216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-247718 : ℤ) ∧
    (∑ n ∈ Ico 121088 121216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4954432561010517682781937353 : ℤ) := by
  rcases cdemPrefixStats_121088_121152 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_121152_121216 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 121088 ≤ 121152) (by norm_num : 121152 ≤ 121216), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 121088 ≤ 121152) (by norm_num : 121152 ≤ 121216), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 121088 ≤ 121152) (by norm_num : 121152 ≤ 121216), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 121088 ≤ 121152) (by norm_num : 121152 ≤ 121216), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_121216_121280 :
    (∑ n ∈ Ico 121216 121280, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 121216 121280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 121216 121280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (247481 : ℤ) ∧
    (∑ n ∈ Ico 121216 121280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4949685006078488479736466726 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_121280_121344 :
    (∑ n ∈ Ico 121280 121344, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 121280 121344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 121280 121344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-41209 : ℤ) ∧
    (∑ n ∈ Ico 121280 121344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-824144103809494568135425180 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_121216_121344 :
    (∑ n ∈ Ico 121216 121344, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 121216 121344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 121216 121344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (206272 : ℤ) ∧
    (∑ n ∈ Ico 121216 121344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4125540902268993911601041546 : ℤ) := by
  rcases cdemPrefixStats_121216_121280 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_121280_121344 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 121216 ≤ 121280) (by norm_num : 121280 ≤ 121344), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 121216 ≤ 121280) (by norm_num : 121280 ≤ 121344), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 121216 ≤ 121280) (by norm_num : 121280 ≤ 121344), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 121216 ≤ 121280) (by norm_num : 121280 ≤ 121344), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_121088_121344 :
    (∑ n ∈ Ico 121088 121344, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 121088 121344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 121088 121344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-41446 : ℤ) ∧
    (∑ n ∈ Ico 121088 121344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-828891658741523771180895807 : ℤ) := by
  rcases cdemPrefixStats_121088_121216 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_121216_121344 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 121088 ≤ 121216) (by norm_num : 121216 ≤ 121344), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 121088 ≤ 121216) (by norm_num : 121216 ≤ 121344), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 121088 ≤ 121216) (by norm_num : 121216 ≤ 121344), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 121088 ≤ 121216) (by norm_num : 121216 ≤ 121344), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_120832_121344 :
    (∑ n ∈ Ico 120832 121344, mobiusTreeValue 16 mobiusTable1200001 n) = (-36 : ℤ) ∧
    (∑ n ∈ Ico 120832 121344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (314 : ℕ) ∧
    (∑ n ∈ Ico 120832 121344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1488384 : ℤ) ∧
    (∑ n ∈ Ico 120832 121344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-29768073230878728860834855352 : ℤ) := by
  rcases cdemPrefixStats_120832_121088 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_121088_121344 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 120832 ≤ 121088) (by norm_num : 121088 ≤ 121344), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 120832 ≤ 121088) (by norm_num : 121088 ≤ 121344), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 120832 ≤ 121088) (by norm_num : 121088 ≤ 121344), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 120832 ≤ 121088) (by norm_num : 121088 ≤ 121344), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_121344_121408 :
    (∑ n ∈ Ico 121344 121408, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 121344 121408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 121344 121408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-288403 : ℤ) ∧
    (∑ n ∈ Ico 121344 121408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5768132811174554340234446987 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_121408_121472 :
    (∑ n ∈ Ico 121408 121472, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 121408 121472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 121408 121472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-123528 : ℤ) ∧
    (∑ n ∈ Ico 121408 121472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2470565858986347403211160775 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_121344_121472 :
    (∑ n ∈ Ico 121344 121472, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 121344 121472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 121344 121472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-411931 : ℤ) ∧
    (∑ n ∈ Ico 121344 121472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8238698670160901743445607762 : ℤ) := by
  rcases cdemPrefixStats_121344_121408 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_121408_121472 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 121344 ≤ 121408) (by norm_num : 121408 ≤ 121472), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 121344 ≤ 121408) (by norm_num : 121408 ≤ 121472), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 121344 ≤ 121408) (by norm_num : 121408 ≤ 121472), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 121344 ≤ 121408) (by norm_num : 121408 ≤ 121472), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_121472_121536 :
    (∑ n ∈ Ico 121472 121536, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 121472 121536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 121472 121536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-164600 : ℤ) ∧
    (∑ n ∈ Ico 121472 121536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3292086234545047691280071312 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_121536_121600 :
    (∑ n ∈ Ico 121536 121600, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 121536 121600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 121536 121600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-123337 : ℤ) ∧
    (∑ n ∈ Ico 121536 121600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2466699161613681516142325921 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_121472_121600 :
    (∑ n ∈ Ico 121472 121600, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 121472 121600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 121472 121600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-287937 : ℤ) ∧
    (∑ n ∈ Ico 121472 121600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5758785396158729207422397233 : ℤ) := by
  rcases cdemPrefixStats_121472_121536 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_121536_121600 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 121472 ≤ 121536) (by norm_num : 121536 ≤ 121600), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 121472 ≤ 121536) (by norm_num : 121536 ≤ 121600), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 121472 ≤ 121536) (by norm_num : 121536 ≤ 121600), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 121472 ≤ 121536) (by norm_num : 121536 ≤ 121600), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_121344_121600 :
    (∑ n ∈ Ico 121344 121600, mobiusTreeValue 16 mobiusTable1200001 n) = (-17 : ℤ) ∧
    (∑ n ∈ Ico 121344 121600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 121344 121600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-699868 : ℤ) ∧
    (∑ n ∈ Ico 121344 121600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13997484066319630950868004995 : ℤ) := by
  rcases cdemPrefixStats_121344_121472 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_121472_121600 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 121344 ≤ 121472) (by norm_num : 121472 ≤ 121600), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 121344 ≤ 121472) (by norm_num : 121472 ≤ 121600), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 121344 ≤ 121472) (by norm_num : 121472 ≤ 121600), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 121344 ≤ 121472) (by norm_num : 121472 ≤ 121600), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_121600_121664 :
    (∑ n ∈ Ico 121600 121664, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 121600 121664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 121600 121664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-411097 : ℤ) ∧
    (∑ n ∈ Ico 121600 121664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8222075129312060528967718713 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_121664_121728 :
    (∑ n ∈ Ico 121664 121728, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 121664 121728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 121664 121728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-82142 : ℤ) ∧
    (∑ n ∈ Ico 121664 121728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1642825070664461668494542874 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_121600_121728 :
    (∑ n ∈ Ico 121600 121728, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 121600 121728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 121600 121728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-493239 : ℤ) ∧
    (∑ n ∈ Ico 121600 121728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9864900199976522197462261587 : ℤ) := by
  rcases cdemPrefixStats_121600_121664 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_121664_121728 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 121600 ≤ 121664) (by norm_num : 121664 ≤ 121728), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 121600 ≤ 121664) (by norm_num : 121664 ≤ 121728), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 121600 ≤ 121664) (by norm_num : 121664 ≤ 121728), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 121600 ≤ 121664) (by norm_num : 121664 ≤ 121728), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_121728_121792 :
    (∑ n ∈ Ico 121728 121792, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 121728 121792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 121728 121792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (164219 : ℤ) ∧
    (∑ n ∈ Ico 121728 121792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3284456436760929093080680743 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_121792_121856 :
    (∑ n ∈ Ico 121792 121856, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 121792 121856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (34 : ℕ) ∧
    (∑ n ∈ Ico 121792 121856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (492533 : ℤ) ∧
    (∑ n ∈ Ico 121792 121856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9850734183473309704412429376 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_121728_121856 :
    (∑ n ∈ Ico 121728 121856, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 121728 121856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (74 : ℕ) ∧
    (∑ n ∈ Ico 121728 121856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (656752 : ℤ) ∧
    (∑ n ∈ Ico 121728 121856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13135190620234238797493110119 : ℤ) := by
  rcases cdemPrefixStats_121728_121792 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_121792_121856 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 121728 ≤ 121792) (by norm_num : 121792 ≤ 121856), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 121728 ≤ 121792) (by norm_num : 121792 ≤ 121856), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 121728 ≤ 121792) (by norm_num : 121792 ≤ 121856), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 121728 ≤ 121792) (by norm_num : 121792 ≤ 121856), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_121600_121856 :
    (∑ n ∈ Ico 121600 121856, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 121600 121856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (150 : ℕ) ∧
    (∑ n ∈ Ico 121600 121856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (163513 : ℤ) ∧
    (∑ n ∈ Ico 121600 121856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3270290420257716600030848532 : ℤ) := by
  rcases cdemPrefixStats_121600_121728 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_121728_121856 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 121600 ≤ 121728) (by norm_num : 121728 ≤ 121856), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 121600 ≤ 121728) (by norm_num : 121728 ≤ 121856), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 121600 ≤ 121728) (by norm_num : 121728 ≤ 121856), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 121600 ≤ 121728) (by norm_num : 121728 ≤ 121856), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_121344_121856 :
    (∑ n ∈ Ico 121344 121856, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 121344 121856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (305 : ℕ) ∧
    (∑ n ∈ Ico 121344 121856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-536355 : ℤ) ∧
    (∑ n ∈ Ico 121344 121856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10727193646061914350837156463 : ℤ) := by
  rcases cdemPrefixStats_121344_121600 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_121600_121856 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 121344 ≤ 121600) (by norm_num : 121600 ≤ 121856), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 121344 ≤ 121600) (by norm_num : 121600 ≤ 121856), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 121344 ≤ 121600) (by norm_num : 121600 ≤ 121856), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 121344 ≤ 121600) (by norm_num : 121600 ≤ 121856), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_120832_121856 :
    (∑ n ∈ Ico 120832 121856, mobiusTreeValue 16 mobiusTable1200001 n) = (-49 : ℤ) ∧
    (∑ n ∈ Ico 120832 121856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (619 : ℕ) ∧
    (∑ n ∈ Ico 120832 121856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2024739 : ℤ) ∧
    (∑ n ∈ Ico 120832 121856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-40495266876940643211672011815 : ℤ) := by
  rcases cdemPrefixStats_120832_121344 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_121344_121856 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 120832 ≤ 121344) (by norm_num : 121344 ≤ 121856), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 120832 ≤ 121344) (by norm_num : 121344 ≤ 121856), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 120832 ≤ 121344) (by norm_num : 121344 ≤ 121856), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 120832 ≤ 121344) (by norm_num : 121344 ≤ 121856), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_121856_121920 :
    (∑ n ∈ Ico 121856 121920, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 121856 121920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 121856 121920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (205124 : ℤ) ∧
    (∑ n ∈ Ico 121856 121920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4102537410383783779261714369 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_121920_121984 :
    (∑ n ∈ Ico 121920 121984, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 121920 121984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 121920 121984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-163975 : ℤ) ∧
    (∑ n ∈ Ico 121920 121984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3279548830344278199211226233 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_121856_121984 :
    (∑ n ∈ Ico 121856 121984, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 121856 121984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 121856 121984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (41149 : ℤ) ∧
    (∑ n ∈ Ico 121856 121984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (822988580039505580050488136 : ℤ) := by
  rcases cdemPrefixStats_121856_121920 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_121920_121984 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 121856 ≤ 121920) (by norm_num : 121920 ≤ 121984), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 121856 ≤ 121920) (by norm_num : 121920 ≤ 121984), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 121856 ≤ 121920) (by norm_num : 121920 ≤ 121984), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 121856 ≤ 121920) (by norm_num : 121920 ≤ 121984), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_121984_122048 :
    (∑ n ∈ Ico 121984 122048, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 121984 122048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 121984 122048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-409748 : ℤ) ∧
    (∑ n ∈ Ico 121984 122048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8194995093547159886867064440 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_122048_122112 :
    (∑ n ∈ Ico 122048 122112, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 122048 122112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 122048 122112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (245700 : ℤ) ∧
    (∑ n ∈ Ico 122048 122112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4914038447777525307237354521 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_121984_122112 :
    (∑ n ∈ Ico 121984 122112, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 121984 122112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 121984 122112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-164048 : ℤ) ∧
    (∑ n ∈ Ico 121984 122112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3280956645769634579629709919 : ℤ) := by
  rcases cdemPrefixStats_121984_122048 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_122048_122112 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 121984 ≤ 122048) (by norm_num : 122048 ≤ 122112), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 121984 ≤ 122048) (by norm_num : 122048 ≤ 122112), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 121984 ≤ 122048) (by norm_num : 122048 ≤ 122112), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 121984 ≤ 122048) (by norm_num : 122048 ≤ 122112), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_121856_122112 :
    (∑ n ∈ Ico 121856 122112, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 121856 122112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 121856 122112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-122899 : ℤ) ∧
    (∑ n ∈ Ico 121856 122112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2457968065730128999579221783 : ℤ) := by
  rcases cdemPrefixStats_121856_121984 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_121984_122112 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 121856 ≤ 121984) (by norm_num : 121984 ≤ 122112), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 121856 ≤ 121984) (by norm_num : 121984 ≤ 122112), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 121856 ≤ 121984) (by norm_num : 121984 ≤ 122112), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 121856 ≤ 121984) (by norm_num : 121984 ≤ 122112), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_122112_122176 :
    (∑ n ∈ Ico 122112 122176, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 122112 122176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 122112 122176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-491170 : ℤ) ∧
    (∑ n ∈ Ico 122112 122176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9823537855147386474680169808 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_122176_122240 :
    (∑ n ∈ Ico 122176 122240, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 122176 122240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 122176 122240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-81831 : ℤ) ∧
    (∑ n ∈ Ico 122176 122240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1636607506125371208071764638 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_122112_122240 :
    (∑ n ∈ Ico 122112 122240, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 122112 122240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 122112 122240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-573001 : ℤ) ∧
    (∑ n ∈ Ico 122112 122240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11460145361272757682751934446 : ℤ) := by
  rcases cdemPrefixStats_122112_122176 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_122176_122240 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 122112 ≤ 122176) (by norm_num : 122176 ≤ 122240), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 122112 ≤ 122176) (by norm_num : 122176 ≤ 122240), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 122112 ≤ 122176) (by norm_num : 122176 ≤ 122240), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 122112 ≤ 122176) (by norm_num : 122176 ≤ 122240), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_122240_122304 :
    (∑ n ∈ Ico 122240 122304, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 122240 122304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 122240 122304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-81805 : ℤ) ∧
    (∑ n ∈ Ico 122240 122304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1636098792578690171727068998 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_122304_122368 :
    (∑ n ∈ Ico 122304 122368, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 122304 122368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 122304 122368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-245260 : ℤ) ∧
    (∑ n ∈ Ico 122304 122368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4905307120738038516451204647 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_122240_122368 :
    (∑ n ∈ Ico 122240 122368, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 122240 122368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 122240 122368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-327065 : ℤ) ∧
    (∑ n ∈ Ico 122240 122368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6541405913316728688178273645 : ℤ) := by
  rcases cdemPrefixStats_122240_122304 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_122304_122368 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 122240 ≤ 122304) (by norm_num : 122304 ≤ 122368), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 122240 ≤ 122304) (by norm_num : 122304 ≤ 122368), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 122240 ≤ 122304) (by norm_num : 122304 ≤ 122368), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 122240 ≤ 122304) (by norm_num : 122304 ≤ 122368), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_122112_122368 :
    (∑ n ∈ Ico 122112 122368, mobiusTreeValue 16 mobiusTable1200001 n) = (-22 : ℤ) ∧
    (∑ n ∈ Ico 122112 122368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 122112 122368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-900066 : ℤ) ∧
    (∑ n ∈ Ico 122112 122368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-18001551274589486370930208091 : ℤ) := by
  rcases cdemPrefixStats_122112_122240 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_122240_122368 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 122112 ≤ 122240) (by norm_num : 122240 ≤ 122368), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 122112 ≤ 122240) (by norm_num : 122240 ≤ 122368), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 122112 ≤ 122240) (by norm_num : 122240 ≤ 122368), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 122112 ≤ 122240) (by norm_num : 122240 ≤ 122368), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_121856_122368 :
    (∑ n ∈ Ico 121856 122368, mobiusTreeValue 16 mobiusTable1200001 n) = (-25 : ℤ) ∧
    (∑ n ∈ Ico 121856 122368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 121856 122368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1022965 : ℤ) ∧
    (∑ n ∈ Ico 121856 122368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-20459519340319615370509429874 : ℤ) := by
  rcases cdemPrefixStats_121856_122112 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_122112_122368 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 121856 ≤ 122112) (by norm_num : 122112 ≤ 122368), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 121856 ≤ 122112) (by norm_num : 122112 ≤ 122368), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 121856 ≤ 122112) (by norm_num : 122112 ≤ 122368), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 121856 ≤ 122112) (by norm_num : 122112 ≤ 122368), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_122368_122432 :
    (∑ n ∈ Ico 122368 122432, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 122368 122432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 122368 122432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-29 : ℤ) ∧
    (∑ n ∈ Ico 122368 122432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-527066574687740612068026 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_122432_122496 :
    (∑ n ∈ Ico 122432 122496, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 122432 122496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 122432 122496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (244918 : ℤ) ∧
    (∑ n ∈ Ico 122432 122496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4898432313353008017897927797 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_122368_122496 :
    (∑ n ∈ Ico 122368 122496, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 122368 122496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 122368 122496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (244889 : ℤ) ∧
    (∑ n ∈ Ico 122368 122496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4897905246778320277285859771 : ℤ) := by
  rcases cdemPrefixStats_122368_122432 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_122432_122496 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 122368 ≤ 122432) (by norm_num : 122432 ≤ 122496), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 122368 ≤ 122432) (by norm_num : 122432 ≤ 122496), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 122368 ≤ 122432) (by norm_num : 122432 ≤ 122496), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 122368 ≤ 122432) (by norm_num : 122432 ≤ 122496), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_122496_122560 :
    (∑ n ∈ Ico 122496 122560, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 122496 122560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 122496 122560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-244851 : ℤ) ∧
    (∑ n ∈ Ico 122496 122560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4896986730840722915869164645 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_122560_122624 :
    (∑ n ∈ Ico 122560 122624, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 122560 122624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 122560 122624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-163101 : ℤ) ∧
    (∑ n ∈ Ico 122560 122624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3262030650730328993101381508 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_122496_122624 :
    (∑ n ∈ Ico 122496 122624, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 122496 122624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 122496 122624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-407952 : ℤ) ∧
    (∑ n ∈ Ico 122496 122624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8159017381571051908970546153 : ℤ) := by
  rcases cdemPrefixStats_122496_122560 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_122560_122624 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 122496 ≤ 122560) (by norm_num : 122560 ≤ 122624), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 122496 ≤ 122560) (by norm_num : 122560 ≤ 122624), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 122496 ≤ 122560) (by norm_num : 122560 ≤ 122624), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 122496 ≤ 122560) (by norm_num : 122560 ≤ 122624), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_122368_122624 :
    (∑ n ∈ Ico 122368 122624, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 122368 122624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 122368 122624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-163063 : ℤ) ∧
    (∑ n ∈ Ico 122368 122624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3261112134792731631684686382 : ℤ) := by
  rcases cdemPrefixStats_122368_122496 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_122496_122624 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 122368 ≤ 122496) (by norm_num : 122496 ≤ 122624), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 122368 ≤ 122496) (by norm_num : 122496 ≤ 122624), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 122368 ≤ 122496) (by norm_num : 122496 ≤ 122624), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 122368 ≤ 122496) (by norm_num : 122496 ≤ 122624), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_122624_122688 :
    (∑ n ∈ Ico 122624 122688, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 122624 122688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 122624 122688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (203841 : ℤ) ∧
    (∑ n ∈ Ico 122624 122688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4076787270203793580203825658 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_122688_122752 :
    (∑ n ∈ Ico 122688 122752, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 122688 122752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 122688 122752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-122250 : ℤ) ∧
    (∑ n ∈ Ico 122688 122752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2445047609438272567689884805 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_122624_122752 :
    (∑ n ∈ Ico 122624 122752, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 122624 122752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 122624 122752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (81591 : ℤ) ∧
    (∑ n ∈ Ico 122624 122752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1631739660765521012513940853 : ℤ) := by
  rcases cdemPrefixStats_122624_122688 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_122688_122752 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 122624 ≤ 122688) (by norm_num : 122688 ≤ 122752), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 122624 ≤ 122688) (by norm_num : 122688 ≤ 122752), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 122624 ≤ 122688) (by norm_num : 122688 ≤ 122752), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 122624 ≤ 122688) (by norm_num : 122688 ≤ 122752), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_122752_122816 :
    (∑ n ∈ Ico 122752 122816, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 122752 122816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 122752 122816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (244324 : ℤ) ∧
    (∑ n ∈ Ico 122752 122816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4886590636866305626362844544 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_122816_122880 :
    (∑ n ∈ Ico 122816 122880, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 122816 122880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 122816 122880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-122043 : ℤ) ∧
    (∑ n ∈ Ico 122816 122880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2440862656226597640190151858 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_122752_122880 :
    (∑ n ∈ Ico 122752 122880, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 122752 122880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 122752 122880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (122281 : ℤ) ∧
    (∑ n ∈ Ico 122752 122880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2445727980639707986172692686 : ℤ) := by
  rcases cdemPrefixStats_122752_122816 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_122816_122880 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 122752 ≤ 122816) (by norm_num : 122816 ≤ 122880), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 122752 ≤ 122816) (by norm_num : 122816 ≤ 122880), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 122752 ≤ 122816) (by norm_num : 122816 ≤ 122880), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 122752 ≤ 122816) (by norm_num : 122816 ≤ 122880), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_122624_122880 :
    (∑ n ∈ Ico 122624 122880, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 122624 122880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 122624 122880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (203872 : ℤ) ∧
    (∑ n ∈ Ico 122624 122880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4077467641405228998686633539 : ℤ) := by
  rcases cdemPrefixStats_122624_122752 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_122752_122880 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 122624 ≤ 122752) (by norm_num : 122752 ≤ 122880), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 122624 ≤ 122752) (by norm_num : 122752 ≤ 122880), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 122624 ≤ 122752) (by norm_num : 122752 ≤ 122880), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 122624 ≤ 122752) (by norm_num : 122752 ≤ 122880), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_122368_122880 :
    (∑ n ∈ Ico 122368 122880, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 122368 122880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 122368 122880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (40809 : ℤ) ∧
    (∑ n ∈ Ico 122368 122880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (816355506612497367001947157 : ℤ) := by
  rcases cdemPrefixStats_122368_122624 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_122624_122880 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 122368 ≤ 122624) (by norm_num : 122624 ≤ 122880), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 122368 ≤ 122624) (by norm_num : 122624 ≤ 122880), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 122368 ≤ 122624) (by norm_num : 122624 ≤ 122880), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 122368 ≤ 122624) (by norm_num : 122624 ≤ 122880), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_121856_122880 :
    (∑ n ∈ Ico 121856 122880, mobiusTreeValue 16 mobiusTable1200001 n) = (-24 : ℤ) ∧
    (∑ n ∈ Ico 121856 122880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (622 : ℕ) ∧
    (∑ n ∈ Ico 121856 122880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-982156 : ℤ) ∧
    (∑ n ∈ Ico 121856 122880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-19643163833707118003507482717 : ℤ) := by
  rcases cdemPrefixStats_121856_122368 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_122368_122880 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 121856 ≤ 122368) (by norm_num : 122368 ≤ 122880), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 121856 ≤ 122368) (by norm_num : 122368 ≤ 122880), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 121856 ≤ 122368) (by norm_num : 122368 ≤ 122880), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 121856 ≤ 122368) (by norm_num : 122368 ≤ 122880), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_120832_122880 :
    (∑ n ∈ Ico 120832 122880, mobiusTreeValue 16 mobiusTable1200001 n) = (-73 : ℤ) ∧
    (∑ n ∈ Ico 120832 122880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1241 : ℕ) ∧
    (∑ n ∈ Ico 120832 122880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3006895 : ℤ) ∧
    (∑ n ∈ Ico 120832 122880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-60138430710647761215179494532 : ℤ) := by
  rcases cdemPrefixStats_120832_121856 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_121856_122880 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 120832 ≤ 121856) (by norm_num : 121856 ≤ 122880), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 120832 ≤ 121856) (by norm_num : 121856 ≤ 122880), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 120832 ≤ 121856) (by norm_num : 121856 ≤ 122880), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 120832 ≤ 121856) (by norm_num : 121856 ≤ 122880), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_118784_122880 :
    (∑ n ∈ Ico 118784 122880, mobiusTreeValue 16 mobiusTable1200001 n) = (-67 : ℤ) ∧
    (∑ n ∈ Ico 118784 122880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2487 : ℕ) ∧
    (∑ n ∈ Ico 118784 122880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2753063 : ℤ) ∧
    (∑ n ∈ Ico 118784 122880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-55061847728057133877177658874 : ℤ) := by
  rcases cdemPrefixStats_118784_120832 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_120832_122880 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 118784 ≤ 120832) (by norm_num : 120832 ≤ 122880), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 118784 ≤ 120832) (by norm_num : 120832 ≤ 122880), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 118784 ≤ 120832) (by norm_num : 120832 ≤ 122880), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 118784 ≤ 120832) (by norm_num : 120832 ≤ 122880), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup029_checked_complete :
    (∑ n ∈ Ico 118784 122880, mobiusTreeValue 16 mobiusTable1200001 n) = (-67 : ℤ) ∧
    (∑ n ∈ Ico 118784 122880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2487 : ℕ) ∧
    (∑ n ∈ Ico 118784 122880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2753063 : ℤ) ∧
    (∑ n ∈ Ico 118784 122880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-55061847728057133877177658874 : ℤ) := cdemPrefixStats_118784_122880
end Helfgott
#print axioms Helfgott.cdemPrefixGroup029_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 118784 122880, mobiusTreeValue 16 mobiusTable1200001 n) = (-67 : ℤ) ∧
    (∑ n ∈ Ico 118784 122880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2487 : ℕ) ∧
    (∑ n ∈ Ico 118784 122880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2753063 : ℤ) ∧
    (∑ n ∈ Ico 118784 122880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-55061847728057133877177658874 : ℤ) := Helfgott.cdemPrefixGroup029_checked_complete
#print axioms solution
