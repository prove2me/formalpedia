-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup009_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:31:42.16255+00:00
-- url     : https://prove2.me/submissions/3ad4fc8c-1818-4ee0-896c-d236b22abbcd

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
private theorem cdemPrefixStats_36864_36928 :
    (∑ n ∈ Ico 36864 36928, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 36864 36928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 36864 36928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1354963 : ℤ) ∧
    (∑ n ∈ Ico 36864 36928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-27099395221485797671383583315 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_36928_36992 :
    (∑ n ∈ Ico 36928 36992, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 36928 36992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 36928 36992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (404978 : ℤ) ∧
    (∑ n ∈ Ico 36928 36992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8099460814833276615567168588 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_36864_36992 :
    (∑ n ∈ Ico 36864 36992, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 36864 36992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 36864 36992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-949985 : ℤ) ∧
    (∑ n ∈ Ico 36864 36992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-18999934406652521055816414727 : ℤ) := by
  rcases cdemPrefixStats_36864_36928 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_36928_36992 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 36864 ≤ 36928) (by norm_num : 36928 ≤ 36992), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 36864 ≤ 36928) (by norm_num : 36928 ≤ 36992), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 36864 ≤ 36928) (by norm_num : 36928 ≤ 36992), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 36864 ≤ 36928) (by norm_num : 36928 ≤ 36992), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_36992_37056 :
    (∑ n ∈ Ico 36992 37056, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 36992 37056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 36992 37056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-270330 : ℤ) ∧
    (∑ n ∈ Ico 36992 37056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5406647068291259751478066931 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_37056_37120 :
    (∑ n ∈ Ico 37056 37120, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 37056 37120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 37056 37120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (135072 : ℤ) ∧
    (∑ n ∈ Ico 37056 37120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2701447102269312316265127742 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_36992_37120 :
    (∑ n ∈ Ico 36992 37120, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 36992 37120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 36992 37120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-135258 : ℤ) ∧
    (∑ n ∈ Ico 36992 37120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2705199966021947435212939189 : ℤ) := by
  rcases cdemPrefixStats_36992_37056 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_37056_37120 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 36992 ≤ 37056) (by norm_num : 37056 ≤ 37120), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 36992 ≤ 37056) (by norm_num : 37056 ≤ 37120), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 36992 ≤ 37056) (by norm_num : 37056 ≤ 37120), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 36992 ≤ 37056) (by norm_num : 37056 ≤ 37120), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_36864_37120 :
    (∑ n ∈ Ico 36864 37120, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 36864 37120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 36864 37120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1085243 : ℤ) ∧
    (∑ n ∈ Ico 36864 37120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-21705134372674468491029353916 : ℤ) := by
  rcases cdemPrefixStats_36864_36992 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_36992_37120 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 36864 ≤ 36992) (by norm_num : 36992 ≤ 37120), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 36864 ≤ 36992) (by norm_num : 36992 ≤ 37120), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 36864 ≤ 36992) (by norm_num : 36992 ≤ 37120), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 36864 ≤ 36992) (by norm_num : 36992 ≤ 37120), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_37120_37184 :
    (∑ n ∈ Ico 37120 37184, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 37120 37184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 37120 37184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (673652 : ℤ) ∧
    (∑ n ∈ Ico 37120 37184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13473077761318054048798106323 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_37184_37248 :
    (∑ n ∈ Ico 37184 37248, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 37184 37248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 37184 37248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1074778 : ℤ) ∧
    (∑ n ∈ Ico 37184 37248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-21495625734140055498268874305 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_37120_37248 :
    (∑ n ∈ Ico 37120 37248, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 37120 37248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 37120 37248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-401126 : ℤ) ∧
    (∑ n ∈ Ico 37120 37248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8022547972822001449470767982 : ℤ) := by
  rcases cdemPrefixStats_37120_37184 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_37184_37248 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 37120 ≤ 37184) (by norm_num : 37184 ≤ 37248), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 37120 ≤ 37184) (by norm_num : 37184 ≤ 37248), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 37120 ≤ 37184) (by norm_num : 37184 ≤ 37248), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 37120 ≤ 37184) (by norm_num : 37184 ≤ 37248), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_37248_37312 :
    (∑ n ∈ Ico 37248 37312, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 37248 37312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 37248 37312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1206909 : ℤ) ∧
    (∑ n ∈ Ico 37248 37312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-24138256090602428492990578903 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_37312_37376 :
    (∑ n ∈ Ico 37312 37376, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 37312 37376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 37312 37376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-669692 : ℤ) ∧
    (∑ n ∈ Ico 37312 37376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13393915136551328790887678302 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_37248_37376 :
    (∑ n ∈ Ico 37248 37376, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 37248 37376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 37248 37376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1876601 : ℤ) ∧
    (∑ n ∈ Ico 37248 37376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-37532171227153757283878257205 : ℤ) := by
  rcases cdemPrefixStats_37248_37312 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_37312_37376 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 37248 ≤ 37312) (by norm_num : 37312 ≤ 37376), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 37248 ≤ 37312) (by norm_num : 37312 ≤ 37376), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 37248 ≤ 37312) (by norm_num : 37312 ≤ 37376), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 37248 ≤ 37312) (by norm_num : 37312 ≤ 37376), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_37120_37376 :
    (∑ n ∈ Ico 37120 37376, mobiusTreeValue 16 mobiusTable1200001 n) = (-17 : ℤ) ∧
    (∑ n ∈ Ico 37120 37376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 37120 37376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2277727 : ℤ) ∧
    (∑ n ∈ Ico 37120 37376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-45554719199975758733349025187 : ℤ) := by
  rcases cdemPrefixStats_37120_37248 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_37248_37376 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 37120 ≤ 37248) (by norm_num : 37248 ≤ 37376), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 37120 ≤ 37248) (by norm_num : 37248 ≤ 37376), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 37120 ≤ 37248) (by norm_num : 37248 ≤ 37376), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 37120 ≤ 37248) (by norm_num : 37248 ≤ 37376), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_36864_37376 :
    (∑ n ∈ Ico 36864 37376, mobiusTreeValue 16 mobiusTable1200001 n) = (-25 : ℤ) ∧
    (∑ n ∈ Ico 36864 37376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 36864 37376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3362970 : ℤ) ∧
    (∑ n ∈ Ico 36864 37376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-67259853572650227224378379103 : ℤ) := by
  rcases cdemPrefixStats_36864_37120 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_37120_37376 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 36864 ≤ 37120) (by norm_num : 37120 ≤ 37376), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 36864 ≤ 37120) (by norm_num : 37120 ≤ 37376), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 36864 ≤ 37120) (by norm_num : 37120 ≤ 37376), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 36864 ≤ 37120) (by norm_num : 37120 ≤ 37376), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_37376_37440 :
    (∑ n ∈ Ico 37376 37440, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 37376 37440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 37376 37440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (667764 : ℤ) ∧
    (∑ n ∈ Ico 37376 37440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13355343038731251855277771149 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_37440_37504 :
    (∑ n ∈ Ico 37440 37504, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 37440 37504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 37440 37504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (15 : ℤ) ∧
    (∑ n ∈ Ico 37440 37504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (277859718686673423378781 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_37376_37504 :
    (∑ n ∈ Ico 37376 37504, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 37376 37504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 37376 37504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (667779 : ℤ) ∧
    (∑ n ∈ Ico 37376 37504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13355620898449938528701149930 : ℤ) := by
  rcases cdemPrefixStats_37376_37440 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_37440_37504 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 37376 ≤ 37440) (by norm_num : 37440 ≤ 37504), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 37376 ≤ 37440) (by norm_num : 37440 ≤ 37504), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 37376 ≤ 37440) (by norm_num : 37440 ≤ 37504), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 37376 ≤ 37440) (by norm_num : 37440 ≤ 37504), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_37504_37568 :
    (∑ n ∈ Ico 37504 37568, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 37504 37568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (35 : ℕ) ∧
    (∑ n ∈ Ico 37504 37568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1198674 : ℤ) ∧
    (∑ n ∈ Ico 37504 37568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-23973587003237959162346478298 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_37568_37632 :
    (∑ n ∈ Ico 37568 37632, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 37568 37632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 37568 37632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-133237 : ℤ) ∧
    (∑ n ∈ Ico 37568 37632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2664738381947945375226990295 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_37504_37632 :
    (∑ n ∈ Ico 37504 37632, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 37504 37632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (74 : ℕ) ∧
    (∑ n ∈ Ico 37504 37632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1331911 : ℤ) ∧
    (∑ n ∈ Ico 37504 37632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-26638325385185904537573468593 : ℤ) := by
  rcases cdemPrefixStats_37504_37568 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_37568_37632 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 37504 ≤ 37568) (by norm_num : 37568 ≤ 37632), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 37504 ≤ 37568) (by norm_num : 37568 ≤ 37632), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 37504 ≤ 37568) (by norm_num : 37568 ≤ 37632), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 37504 ≤ 37568) (by norm_num : 37568 ≤ 37632), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_37376_37632 :
    (∑ n ∈ Ico 37376 37632, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 37376 37632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (151 : ℕ) ∧
    (∑ n ∈ Ico 37376 37632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-664132 : ℤ) ∧
    (∑ n ∈ Ico 37376 37632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13282704486735966008872318663 : ℤ) := by
  rcases cdemPrefixStats_37376_37504 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_37504_37632 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 37376 ≤ 37504) (by norm_num : 37504 ≤ 37632), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 37376 ≤ 37504) (by norm_num : 37504 ≤ 37632), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 37376 ≤ 37504) (by norm_num : 37504 ≤ 37632), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 37376 ≤ 37504) (by norm_num : 37504 ≤ 37632), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_37632_37696 :
    (∑ n ∈ Ico 37632 37696, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 37632 37696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 37632 37696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-663620 : ℤ) ∧
    (∑ n ∈ Ico 37632 37696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13272460907073879605925962968 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_37696_37760 :
    (∑ n ∈ Ico 37696 37760, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 37696 37760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 37696 37760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (662310 : ℤ) ∧
    (∑ n ∈ Ico 37696 37760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13246224896222296950279011333 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_37632_37760 :
    (∑ n ∈ Ico 37632 37760, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 37632 37760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 37632 37760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1310 : ℤ) ∧
    (∑ n ∈ Ico 37632 37760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-26236010851582655646951635 : ℤ) := by
  rcases cdemPrefixStats_37632_37696 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_37696_37760 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 37632 ≤ 37696) (by norm_num : 37696 ≤ 37760), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 37632 ≤ 37696) (by norm_num : 37696 ≤ 37760), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 37632 ≤ 37696) (by norm_num : 37696 ≤ 37760), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 37632 ≤ 37696) (by norm_num : 37696 ≤ 37760), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_37760_37824 :
    (∑ n ∈ Ico 37760 37824, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 37760 37824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 37760 37824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (396938 : ℤ) ∧
    (∑ n ∈ Ico 37760 37824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7938823601442345911895408426 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_37824_37888 :
    (∑ n ∈ Ico 37824 37888, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 37824 37888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 37824 37888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-131860 : ℤ) ∧
    (∑ n ∈ Ico 37824 37888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2637191389527359642420790511 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_37760_37888 :
    (∑ n ∈ Ico 37760 37888, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 37760 37888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 37760 37888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (265078 : ℤ) ∧
    (∑ n ∈ Ico 37760 37888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5301632211914986269474617915 : ℤ) := by
  rcases cdemPrefixStats_37760_37824 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_37824_37888 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 37760 ≤ 37824) (by norm_num : 37824 ≤ 37888), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 37760 ≤ 37824) (by norm_num : 37824 ≤ 37888), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 37760 ≤ 37824) (by norm_num : 37824 ≤ 37888), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 37760 ≤ 37824) (by norm_num : 37824 ≤ 37888), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_37632_37888 :
    (∑ n ∈ Ico 37632 37888, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 37632 37888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 37632 37888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (263768 : ℤ) ∧
    (∑ n ∈ Ico 37632 37888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5275396201063403613827666280 : ℤ) := by
  rcases cdemPrefixStats_37632_37760 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_37760_37888 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 37632 ≤ 37760) (by norm_num : 37760 ≤ 37888), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 37632 ≤ 37760) (by norm_num : 37760 ≤ 37888), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 37632 ≤ 37760) (by norm_num : 37760 ≤ 37888), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 37632 ≤ 37760) (by norm_num : 37760 ≤ 37888), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_37376_37888 :
    (∑ n ∈ Ico 37376 37888, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 37376 37888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (307 : ℕ) ∧
    (∑ n ∈ Ico 37376 37888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-400364 : ℤ) ∧
    (∑ n ∈ Ico 37376 37888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8007308285672562395044652383 : ℤ) := by
  rcases cdemPrefixStats_37376_37632 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_37632_37888 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 37376 ≤ 37632) (by norm_num : 37632 ≤ 37888), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 37376 ≤ 37632) (by norm_num : 37632 ≤ 37888), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 37376 ≤ 37632) (by norm_num : 37632 ≤ 37888), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 37376 ≤ 37632) (by norm_num : 37632 ≤ 37888), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_36864_37888 :
    (∑ n ∈ Ico 36864 37888, mobiusTreeValue 16 mobiusTable1200001 n) = (-28 : ℤ) ∧
    (∑ n ∈ Ico 36864 37888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (616 : ℕ) ∧
    (∑ n ∈ Ico 36864 37888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3763334 : ℤ) ∧
    (∑ n ∈ Ico 36864 37888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-75267161858322789619423031486 : ℤ) := by
  rcases cdemPrefixStats_36864_37376 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_37376_37888 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 36864 ≤ 37376) (by norm_num : 37376 ≤ 37888), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 36864 ≤ 37376) (by norm_num : 37376 ≤ 37888), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 36864 ≤ 37376) (by norm_num : 37376 ≤ 37888), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 36864 ≤ 37376) (by norm_num : 37376 ≤ 37888), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_37888_37952 :
    (∑ n ∈ Ico 37888 37952, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 37888 37952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 37888 37952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1318272 : ℤ) ∧
    (∑ n ∈ Ico 37888 37952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (26365540230558218349449500393 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_37952_38016 :
    (∑ n ∈ Ico 37952 38016, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 37952 38016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 37952 38016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1316184 : ℤ) ∧
    (∑ n ∈ Ico 37952 38016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-26323759198127014452408197671 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_37888_38016 :
    (∑ n ∈ Ico 37888 38016, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 37888 38016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 37888 38016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2088 : ℤ) ∧
    (∑ n ∈ Ico 37888 38016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (41781032431203897041302722 : ℤ) := by
  rcases cdemPrefixStats_37888_37952 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_37952_38016 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 37888 ≤ 37952) (by norm_num : 37952 ≤ 38016), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 37888 ≤ 37952) (by norm_num : 37952 ≤ 38016), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 37888 ≤ 37952) (by norm_num : 37952 ≤ 38016), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 37888 ≤ 37952) (by norm_num : 37952 ≤ 38016), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_38016_38080 :
    (∑ n ∈ Ico 38016 38080, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 38016 38080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 38016 38080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (394755 : ℤ) ∧
    (∑ n ∈ Ico 38016 38080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7895144998013189113964948817 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_38080_38144 :
    (∑ n ∈ Ico 38080 38144, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 38080 38144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 38080 38144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1180989 : ℤ) ∧
    (∑ n ∈ Ico 38080 38144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (23619849824632466903235195811 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_38016_38144 :
    (∑ n ∈ Ico 38016 38144, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 38016 38144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 38016 38144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1575744 : ℤ) ∧
    (∑ n ∈ Ico 38016 38144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (31514994822645656017200144628 : ℤ) := by
  rcases cdemPrefixStats_38016_38080 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_38080_38144 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 38016 ≤ 38080) (by norm_num : 38080 ≤ 38144), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 38016 ≤ 38080) (by norm_num : 38080 ≤ 38144), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 38016 ≤ 38080) (by norm_num : 38080 ≤ 38144), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 38016 ≤ 38080) (by norm_num : 38080 ≤ 38144), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_37888_38144 :
    (∑ n ∈ Ico 37888 38144, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 37888 38144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (160 : ℕ) ∧
    (∑ n ∈ Ico 37888 38144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1577832 : ℤ) ∧
    (∑ n ∈ Ico 37888 38144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (31556775855076859914241447350 : ℤ) := by
  rcases cdemPrefixStats_37888_38016 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_38016_38144 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 37888 ≤ 38016) (by norm_num : 38016 ≤ 38144), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 37888 ≤ 38016) (by norm_num : 38016 ≤ 38144), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 37888 ≤ 38016) (by norm_num : 38016 ≤ 38144), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 37888 ≤ 38016) (by norm_num : 38016 ≤ 38144), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_38144_38208 :
    (∑ n ∈ Ico 38144 38208, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 38144 38208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 38144 38208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-654366 : ℤ) ∧
    (∑ n ∈ Ico 38144 38208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13087358256772871029999736620 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_38208_38272 :
    (∑ n ∈ Ico 38208 38272, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 38208 38272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 38208 38272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-262156 : ℤ) ∧
    (∑ n ∈ Ico 38208 38272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5243184638052618925808565593 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_38144_38272 :
    (∑ n ∈ Ico 38144 38272, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 38144 38272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 38144 38272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-916522 : ℤ) ∧
    (∑ n ∈ Ico 38144 38272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-18330542894825489955808302213 : ℤ) := by
  rcases cdemPrefixStats_38144_38208 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_38208_38272 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 38144 ≤ 38208) (by norm_num : 38208 ≤ 38272), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 38144 ≤ 38208) (by norm_num : 38208 ≤ 38272), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 38144 ≤ 38208) (by norm_num : 38208 ≤ 38272), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 38144 ≤ 38208) (by norm_num : 38208 ≤ 38272), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_38272_38336 :
    (∑ n ∈ Ico 38272 38336, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 38272 38336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 38272 38336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-913371 : ℤ) ∧
    (∑ n ∈ Ico 38272 38336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-18267498067527223248898582444 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_38336_38400 :
    (∑ n ∈ Ico 38336 38400, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 38336 38400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 38336 38400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-390670 : ℤ) ∧
    (∑ n ∈ Ico 38336 38400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7813449595373737825816417090 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_38272_38400 :
    (∑ n ∈ Ico 38272 38400, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 38272 38400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 38272 38400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1304041 : ℤ) ∧
    (∑ n ∈ Ico 38272 38400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-26080947662900961074714999534 : ℤ) := by
  rcases cdemPrefixStats_38272_38336 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_38336_38400 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 38272 ≤ 38336) (by norm_num : 38336 ≤ 38400), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 38272 ≤ 38336) (by norm_num : 38336 ≤ 38400), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 38272 ≤ 38336) (by norm_num : 38336 ≤ 38400), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 38272 ≤ 38336) (by norm_num : 38336 ≤ 38400), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_38144_38400 :
    (∑ n ∈ Ico 38144 38400, mobiusTreeValue 16 mobiusTable1200001 n) = (-17 : ℤ) ∧
    (∑ n ∈ Ico 38144 38400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 38144 38400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2220563 : ℤ) ∧
    (∑ n ∈ Ico 38144 38400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-44411490557726451030523301747 : ℤ) := by
  rcases cdemPrefixStats_38144_38272 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_38272_38400 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 38144 ≤ 38272) (by norm_num : 38272 ≤ 38400), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 38144 ≤ 38272) (by norm_num : 38272 ≤ 38400), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 38144 ≤ 38272) (by norm_num : 38272 ≤ 38400), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 38144 ≤ 38272) (by norm_num : 38272 ≤ 38400), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_37888_38400 :
    (∑ n ∈ Ico 37888 38400, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 37888 38400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (315 : ℕ) ∧
    (∑ n ∈ Ico 37888 38400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-642731 : ℤ) ∧
    (∑ n ∈ Ico 37888 38400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12854714702649591116281854397 : ℤ) := by
  rcases cdemPrefixStats_37888_38144 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_38144_38400 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 37888 ≤ 38144) (by norm_num : 38144 ≤ 38400), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 37888 ≤ 38144) (by norm_num : 38144 ≤ 38400), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 37888 ≤ 38144) (by norm_num : 38144 ≤ 38400), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 37888 ≤ 38144) (by norm_num : 38144 ≤ 38400), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_38400_38464 :
    (∑ n ∈ Ico 38400 38464, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 38400 38464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 38400 38464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2082673 : ℤ) ∧
    (∑ n ∈ Ico 38400 38464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (41653650973544270429588037613 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_38464_38528 :
    (∑ n ∈ Ico 38464 38528, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 38464 38528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 38464 38528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1168384 : ℤ) ∧
    (∑ n ∈ Ico 38464 38528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (23367788266939236682708400416 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_38400_38528 :
    (∑ n ∈ Ico 38400 38528, mobiusTreeValue 16 mobiusTable1200001 n) = (25 : ℤ) ∧
    (∑ n ∈ Ico 38400 38528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 38400 38528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3251057 : ℤ) ∧
    (∑ n ∈ Ico 38400 38528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (65021439240483507112296438029 : ℤ) := by
  rcases cdemPrefixStats_38400_38464 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_38464_38528 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 38400 ≤ 38464) (by norm_num : 38464 ≤ 38528), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 38400 ≤ 38464) (by norm_num : 38464 ≤ 38528), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 38400 ≤ 38464) (by norm_num : 38464 ≤ 38528), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 38400 ≤ 38464) (by norm_num : 38464 ≤ 38528), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_38528_38592 :
    (∑ n ∈ Ico 38528 38592, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 38528 38592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 38528 38592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-129933 : ℤ) ∧
    (∑ n ∈ Ico 38528 38592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2598736812984764415727045909 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_38592_38656 :
    (∑ n ∈ Ico 38592 38656, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 38592 38656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 38592 38656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-258978 : ℤ) ∧
    (∑ n ∈ Ico 38592 38656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5179606021304556935086508769 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_38528_38656 :
    (∑ n ∈ Ico 38528 38656, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 38528 38656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 38528 38656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-388911 : ℤ) ∧
    (∑ n ∈ Ico 38528 38656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7778342834289321350813554678 : ℤ) := by
  rcases cdemPrefixStats_38528_38592 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_38592_38656 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 38528 ≤ 38592) (by norm_num : 38592 ≤ 38656), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 38528 ≤ 38592) (by norm_num : 38592 ≤ 38656), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 38528 ≤ 38592) (by norm_num : 38592 ≤ 38656), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 38528 ≤ 38592) (by norm_num : 38592 ≤ 38656), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_38400_38656 :
    (∑ n ∈ Ico 38400 38656, mobiusTreeValue 16 mobiusTable1200001 n) = (22 : ℤ) ∧
    (∑ n ∈ Ico 38400 38656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 38400 38656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2862146 : ℤ) ∧
    (∑ n ∈ Ico 38400 38656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (57243096406194185761482883351 : ℤ) := by
  rcases cdemPrefixStats_38400_38528 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_38528_38656 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 38400 ≤ 38528) (by norm_num : 38528 ≤ 38656), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 38400 ≤ 38528) (by norm_num : 38528 ≤ 38656), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 38400 ≤ 38528) (by norm_num : 38528 ≤ 38656), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 38400 ≤ 38528) (by norm_num : 38528 ≤ 38656), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_38656_38720 :
    (∑ n ∈ Ico 38656 38720, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 38656 38720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 38656 38720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-129015 : ℤ) ∧
    (∑ n ∈ Ico 38656 38720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2580302663744353886732078468 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_38720_38784 :
    (∑ n ∈ Ico 38720 38784, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 38720 38784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 38720 38784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-258548 : ℤ) ∧
    (∑ n ∈ Ico 38720 38784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5170947821223193080076162428 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_38656_38784 :
    (∑ n ∈ Ico 38656 38784, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 38656 38784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 38656 38784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-387563 : ℤ) ∧
    (∑ n ∈ Ico 38656 38784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7751250484967546966808240896 : ℤ) := by
  rcases cdemPrefixStats_38656_38720 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_38720_38784 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 38656 ≤ 38720) (by norm_num : 38720 ≤ 38784), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 38656 ≤ 38720) (by norm_num : 38720 ≤ 38784), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 38656 ≤ 38720) (by norm_num : 38720 ≤ 38784), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 38656 ≤ 38720) (by norm_num : 38720 ≤ 38784), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_38784_38848 :
    (∑ n ∈ Ico 38784 38848, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 38784 38848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 38784 38848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (129125 : ℤ) ∧
    (∑ n ∈ Ico 38784 38848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2582562923433234135036341766 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_38848_38912 :
    (∑ n ∈ Ico 38848 38912, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 38848 38912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 38848 38912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (128737 : ℤ) ∧
    (∑ n ∈ Ico 38848 38912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2574664195548590128886311405 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_38784_38912 :
    (∑ n ∈ Ico 38784 38912, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 38784 38912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 38784 38912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (257862 : ℤ) ∧
    (∑ n ∈ Ico 38784 38912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5157227118981824263922653171 : ℤ) := by
  rcases cdemPrefixStats_38784_38848 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_38848_38912 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 38784 ≤ 38848) (by norm_num : 38848 ≤ 38912), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 38784 ≤ 38848) (by norm_num : 38848 ≤ 38912), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 38784 ≤ 38848) (by norm_num : 38848 ≤ 38912), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 38784 ≤ 38848) (by norm_num : 38848 ≤ 38912), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_38656_38912 :
    (∑ n ∈ Ico 38656 38912, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 38656 38912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (151 : ℕ) ∧
    (∑ n ∈ Ico 38656 38912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-129701 : ℤ) ∧
    (∑ n ∈ Ico 38656 38912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2594023365985722702885587725 : ℤ) := by
  rcases cdemPrefixStats_38656_38784 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_38784_38912 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 38656 ≤ 38784) (by norm_num : 38784 ≤ 38912), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 38656 ≤ 38784) (by norm_num : 38784 ≤ 38912), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 38656 ≤ 38784) (by norm_num : 38784 ≤ 38912), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 38656 ≤ 38784) (by norm_num : 38784 ≤ 38912), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_38400_38912 :
    (∑ n ∈ Ico 38400 38912, mobiusTreeValue 16 mobiusTable1200001 n) = (21 : ℤ) ∧
    (∑ n ∈ Ico 38400 38912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (305 : ℕ) ∧
    (∑ n ∈ Ico 38400 38912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2732445 : ℤ) ∧
    (∑ n ∈ Ico 38400 38912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (54649073040208463058597295626 : ℤ) := by
  rcases cdemPrefixStats_38400_38656 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_38656_38912 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 38400 ≤ 38656) (by norm_num : 38656 ≤ 38912), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 38400 ≤ 38656) (by norm_num : 38656 ≤ 38912), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 38400 ≤ 38656) (by norm_num : 38656 ≤ 38912), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 38400 ≤ 38656) (by norm_num : 38656 ≤ 38912), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_37888_38912 :
    (∑ n ∈ Ico 37888 38912, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 37888 38912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (620 : ℕ) ∧
    (∑ n ∈ Ico 37888 38912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2089714 : ℤ) ∧
    (∑ n ∈ Ico 37888 38912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (41794358337558871942315441229 : ℤ) := by
  rcases cdemPrefixStats_37888_38400 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_38400_38912 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 37888 ≤ 38400) (by norm_num : 38400 ≤ 38912), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 37888 ≤ 38400) (by norm_num : 38400 ≤ 38912), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 37888 ≤ 38400) (by norm_num : 38400 ≤ 38912), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 37888 ≤ 38400) (by norm_num : 38400 ≤ 38912), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_36864_38912 :
    (∑ n ∈ Ico 36864 38912, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 36864 38912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1236 : ℕ) ∧
    (∑ n ∈ Ico 36864 38912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1673620 : ℤ) ∧
    (∑ n ∈ Ico 36864 38912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-33472803520763917677107590257 : ℤ) := by
  rcases cdemPrefixStats_36864_37888 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_37888_38912 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 36864 ≤ 37888) (by norm_num : 37888 ≤ 38912), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 36864 ≤ 37888) (by norm_num : 37888 ≤ 38912), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 36864 ≤ 37888) (by norm_num : 37888 ≤ 38912), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 36864 ≤ 37888) (by norm_num : 37888 ≤ 38912), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_38912_38976 :
    (∑ n ∈ Ico 38912 38976, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 38912 38976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 38912 38976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (642291 : ℤ) ∧
    (∑ n ∈ Ico 38912 38976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12845870099382270282407754240 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_38976_39040 :
    (∑ n ∈ Ico 38976 39040, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 38976 39040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 38976 39040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2179302 : ℤ) ∧
    (∑ n ∈ Ico 38976 39040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (43586198806006209874784316441 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_38912_39040 :
    (∑ n ∈ Ico 38912 39040, mobiusTreeValue 16 mobiusTable1200001 n) = (22 : ℤ) ∧
    (∑ n ∈ Ico 38912 39040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 38912 39040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2821593 : ℤ) ∧
    (∑ n ∈ Ico 38912 39040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (56432068905388480157192070681 : ℤ) := by
  rcases cdemPrefixStats_38912_38976 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_38976_39040 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 38912 ≤ 38976) (by norm_num : 38976 ≤ 39040), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 38912 ≤ 38976) (by norm_num : 38976 ≤ 39040), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 38912 ≤ 38976) (by norm_num : 38976 ≤ 39040), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 38912 ≤ 38976) (by norm_num : 38976 ≤ 39040), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_39040_39104 :
    (∑ n ∈ Ico 39040 39104, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 39040 39104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 39040 39104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-767803 : ℤ) ∧
    (∑ n ∈ Ico 39040 39104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-15356141506974251384258999669 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_39104_39168 :
    (∑ n ∈ Ico 39104 39168, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 39104 39168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 39104 39168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (127471 : ℤ) ∧
    (∑ n ∈ Ico 39104 39168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2549447282323971171767778304 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_39040_39168 :
    (∑ n ∈ Ico 39040 39168, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 39040 39168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 39040 39168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-640332 : ℤ) ∧
    (∑ n ∈ Ico 39040 39168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12806694224650280212491221365 : ℤ) := by
  rcases cdemPrefixStats_39040_39104 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_39104_39168 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 39040 ≤ 39104) (by norm_num : 39104 ≤ 39168), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 39040 ≤ 39104) (by norm_num : 39104 ≤ 39168), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 39040 ≤ 39104) (by norm_num : 39104 ≤ 39168), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 39040 ≤ 39104) (by norm_num : 39104 ≤ 39168), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_38912_39168 :
    (∑ n ∈ Ico 38912 39168, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 38912 39168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 38912 39168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2181261 : ℤ) ∧
    (∑ n ∈ Ico 38912 39168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (43625374680738199944700849316 : ℤ) := by
  rcases cdemPrefixStats_38912_39040 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_39040_39168 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 38912 ≤ 39040) (by norm_num : 39040 ≤ 39168), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 38912 ≤ 39040) (by norm_num : 39040 ≤ 39168), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 38912 ≤ 39040) (by norm_num : 39040 ≤ 39168), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 38912 ≤ 39040) (by norm_num : 39040 ≤ 39168), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_39168_39232 :
    (∑ n ∈ Ico 39168 39232, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 39168 39232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 39168 39232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1275654 : ℤ) ∧
    (∑ n ∈ Ico 39168 39232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-25513209606211519611543272052 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_39232_39296 :
    (∑ n ∈ Ico 39232 39296, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 39232 39296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 39232 39296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-891417 : ℤ) ∧
    (∑ n ∈ Ico 39232 39296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-17828430790725963000387464930 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_39168_39296 :
    (∑ n ∈ Ico 39168 39296, mobiusTreeValue 16 mobiusTable1200001 n) = (-17 : ℤ) ∧
    (∑ n ∈ Ico 39168 39296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 39168 39296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2167071 : ℤ) ∧
    (∑ n ∈ Ico 39168 39296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-43341640396937482611930736982 : ℤ) := by
  rcases cdemPrefixStats_39168_39232 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_39232_39296 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 39168 ≤ 39232) (by norm_num : 39232 ≤ 39296), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 39168 ≤ 39232) (by norm_num : 39232 ≤ 39296), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 39168 ≤ 39232) (by norm_num : 39232 ≤ 39296), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 39168 ≤ 39232) (by norm_num : 39232 ≤ 39296), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_39296_39360 :
    (∑ n ∈ Ico 39296 39360, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 39296 39360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 39296 39360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-889829 : ℤ) ∧
    (∑ n ∈ Ico 39296 39360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-17796637720894068561304522124 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_39360_39424 :
    (∑ n ∈ Ico 39360 39424, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 39360 39424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 39360 39424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (381036 : ℤ) ∧
    (∑ n ∈ Ico 39360 39424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7620724435402779270504892530 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_39296_39424 :
    (∑ n ∈ Ico 39296 39424, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 39296 39424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 39296 39424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-508793 : ℤ) ∧
    (∑ n ∈ Ico 39296 39424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10175913285491289290799629594 : ℤ) := by
  rcases cdemPrefixStats_39296_39360 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_39360_39424 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 39296 ≤ 39360) (by norm_num : 39360 ≤ 39424), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 39296 ≤ 39360) (by norm_num : 39360 ≤ 39424), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 39296 ≤ 39360) (by norm_num : 39360 ≤ 39424), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 39296 ≤ 39360) (by norm_num : 39360 ≤ 39424), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_39168_39424 :
    (∑ n ∈ Ico 39168 39424, mobiusTreeValue 16 mobiusTable1200001 n) = (-21 : ℤ) ∧
    (∑ n ∈ Ico 39168 39424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (159 : ℕ) ∧
    (∑ n ∈ Ico 39168 39424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2675864 : ℤ) ∧
    (∑ n ∈ Ico 39168 39424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-53517553682428771902730366576 : ℤ) := by
  rcases cdemPrefixStats_39168_39296 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_39296_39424 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 39168 ≤ 39296) (by norm_num : 39296 ≤ 39424), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 39168 ≤ 39296) (by norm_num : 39296 ≤ 39424), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 39168 ≤ 39296) (by norm_num : 39296 ≤ 39424), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 39168 ≤ 39296) (by norm_num : 39296 ≤ 39424), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_38912_39424 :
    (∑ n ∈ Ico 38912 39424, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 38912 39424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (316 : ℕ) ∧
    (∑ n ∈ Ico 38912 39424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-494603 : ℤ) ∧
    (∑ n ∈ Ico 38912 39424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9892179001690571958029517260 : ℤ) := by
  rcases cdemPrefixStats_38912_39168 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_39168_39424 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 38912 ≤ 39168) (by norm_num : 39168 ≤ 39424), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 38912 ≤ 39168) (by norm_num : 39168 ≤ 39424), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 38912 ≤ 39168) (by norm_num : 39168 ≤ 39424), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 38912 ≤ 39168) (by norm_num : 39168 ≤ 39424), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_39424_39488 :
    (∑ n ∈ Ico 39424 39488, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 39424 39488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 39424 39488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-379948 : ℤ) ∧
    (∑ n ∈ Ico 39424 39488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7598974164764586497916636677 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_39488_39552 :
    (∑ n ∈ Ico 39488 39552, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 39488 39552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 39488 39552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1012191 : ℤ) ∧
    (∑ n ∈ Ico 39488 39552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (20243942366685742939849495150 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_39424_39552 :
    (∑ n ∈ Ico 39424 39552, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 39424 39552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 39424 39552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (632243 : ℤ) ∧
    (∑ n ∈ Ico 39424 39552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12644968201921156441932858473 : ℤ) := by
  rcases cdemPrefixStats_39424_39488 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_39488_39552 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 39424 ≤ 39488) (by norm_num : 39488 ≤ 39552), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 39424 ≤ 39488) (by norm_num : 39488 ≤ 39552), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 39424 ≤ 39488) (by norm_num : 39488 ≤ 39552), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 39424 ≤ 39488) (by norm_num : 39488 ≤ 39552), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_39552_39616 :
    (∑ n ∈ Ico 39552 39616, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 39552 39616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 39552 39616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (200 : ℤ) ∧
    (∑ n ∈ Ico 39552 39616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4022882630756959855258923 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_39616_39680 :
    (∑ n ∈ Ico 39616 39680, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 39616 39680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 39616 39680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (378353 : ℤ) ∧
    (∑ n ∈ Ico 39616 39680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7567092755392093975930754689 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_39552_39680 :
    (∑ n ∈ Ico 39552 39680, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 39552 39680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 39552 39680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (378553 : ℤ) ∧
    (∑ n ∈ Ico 39552 39680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7571115638022850935786013612 : ℤ) := by
  rcases cdemPrefixStats_39552_39616 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_39616_39680 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 39552 ≤ 39616) (by norm_num : 39616 ≤ 39680), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 39552 ≤ 39616) (by norm_num : 39616 ≤ 39680), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 39552 ≤ 39616) (by norm_num : 39616 ≤ 39680), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 39552 ≤ 39616) (by norm_num : 39616 ≤ 39680), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_39424_39680 :
    (∑ n ∈ Ico 39424 39680, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 39424 39680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 39424 39680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1010796 : ℤ) ∧
    (∑ n ∈ Ico 39424 39680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (20216083839944007377718872085 : ℤ) := by
  rcases cdemPrefixStats_39424_39552 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_39552_39680 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 39424 ≤ 39552) (by norm_num : 39552 ≤ 39680), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 39424 ≤ 39552) (by norm_num : 39552 ≤ 39680), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 39424 ≤ 39552) (by norm_num : 39552 ≤ 39680), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 39424 ≤ 39552) (by norm_num : 39552 ≤ 39680), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_39680_39744 :
    (∑ n ∈ Ico 39680 39744, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 39680 39744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 39680 39744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (377701 : ℤ) ∧
    (∑ n ∈ Ico 39680 39744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7554017032398443464945397295 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_39744_39808 :
    (∑ n ∈ Ico 39744 39808, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 39744 39808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 39744 39808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1257440 : ℤ) ∧
    (∑ n ∈ Ico 39744 39808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (25148946133249118263800729967 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_39680_39808 :
    (∑ n ∈ Ico 39680 39808, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 39680 39808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 39680 39808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1635141 : ℤ) ∧
    (∑ n ∈ Ico 39680 39808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (32702963165647561728746127262 : ℤ) := by
  rcases cdemPrefixStats_39680_39744 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_39744_39808 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 39680 ≤ 39744) (by norm_num : 39744 ≤ 39808), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 39680 ≤ 39744) (by norm_num : 39744 ≤ 39808), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 39680 ≤ 39744) (by norm_num : 39744 ≤ 39808), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 39680 ≤ 39744) (by norm_num : 39744 ≤ 39808), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_39808_39872 :
    (∑ n ∈ Ico 39808 39872, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 39808 39872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 39808 39872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-752738 : ℤ) ∧
    (∑ n ∈ Ico 39808 39872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-15054888085257438704279984059 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_39872_39936 :
    (∑ n ∈ Ico 39872 39936, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 39872 39936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 39872 39936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-375932 : ℤ) ∧
    (∑ n ∈ Ico 39872 39936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7518608945587534618273843273 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_39808_39936 :
    (∑ n ∈ Ico 39808 39936, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 39808 39936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 39808 39936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1128670 : ℤ) ∧
    (∑ n ∈ Ico 39808 39936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-22573497030844973322553827332 : ℤ) := by
  rcases cdemPrefixStats_39808_39872 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_39872_39936 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 39808 ≤ 39872) (by norm_num : 39872 ≤ 39936), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 39808 ≤ 39872) (by norm_num : 39872 ≤ 39936), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 39808 ≤ 39872) (by norm_num : 39872 ≤ 39936), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 39808 ≤ 39872) (by norm_num : 39872 ≤ 39936), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_39680_39936 :
    (∑ n ∈ Ico 39680 39936, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 39680 39936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 39680 39936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (506471 : ℤ) ∧
    (∑ n ∈ Ico 39680 39936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10129466134802588406192299930 : ℤ) := by
  rcases cdemPrefixStats_39680_39808 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_39808_39936 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 39680 ≤ 39808) (by norm_num : 39808 ≤ 39936), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 39680 ≤ 39808) (by norm_num : 39808 ≤ 39936), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 39680 ≤ 39808) (by norm_num : 39808 ≤ 39936), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 39680 ≤ 39808) (by norm_num : 39808 ≤ 39936), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_39424_39936 :
    (∑ n ∈ Ico 39424 39936, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 39424 39936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (306 : ℕ) ∧
    (∑ n ∈ Ico 39424 39936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1517267 : ℤ) ∧
    (∑ n ∈ Ico 39424 39936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (30345549974746595783911172015 : ℤ) := by
  rcases cdemPrefixStats_39424_39680 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_39680_39936 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 39424 ≤ 39680) (by norm_num : 39680 ≤ 39936), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 39424 ≤ 39680) (by norm_num : 39680 ≤ 39936), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 39424 ≤ 39680) (by norm_num : 39680 ≤ 39936), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 39424 ≤ 39680) (by norm_num : 39680 ≤ 39936), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_38912_39936 :
    (∑ n ∈ Ico 38912 39936, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 38912 39936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (622 : ℕ) ∧
    (∑ n ∈ Ico 38912 39936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1022664 : ℤ) ∧
    (∑ n ∈ Ico 38912 39936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (20453370973056023825881654755 : ℤ) := by
  rcases cdemPrefixStats_38912_39424 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_39424_39936 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 38912 ≤ 39424) (by norm_num : 39424 ≤ 39936), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 38912 ≤ 39424) (by norm_num : 39424 ≤ 39936), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 38912 ≤ 39424) (by norm_num : 39424 ≤ 39936), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 38912 ≤ 39424) (by norm_num : 39424 ≤ 39936), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_39936_40000 :
    (∑ n ∈ Ico 39936 40000, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 39936 40000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 39936 40000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (125464 : ℤ) ∧
    (∑ n ∈ Ico 39936 40000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2509383034352930979299400153 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_40000_40064 :
    (∑ n ∈ Ico 40000 40064, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 40000 40064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 40000 40064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (499535 : ℤ) ∧
    (∑ n ∈ Ico 40000 40064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9990760502637165234579143656 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_39936_40064 :
    (∑ n ∈ Ico 39936 40064, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 39936 40064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 39936 40064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (624999 : ℤ) ∧
    (∑ n ∈ Ico 39936 40064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12500143536990096213878543809 : ℤ) := by
  rcases cdemPrefixStats_39936_40000 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_40000_40064 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 39936 ≤ 40000) (by norm_num : 40000 ≤ 40064), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 39936 ≤ 40000) (by norm_num : 40000 ≤ 40064), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 39936 ≤ 40000) (by norm_num : 40000 ≤ 40064), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 39936 ≤ 40000) (by norm_num : 40000 ≤ 40064), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_40064_40128 :
    (∑ n ∈ Ico 40064 40128, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 40064 40128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 40064 40128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-373485 : ℤ) ∧
    (∑ n ∈ Ico 40064 40128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7469730081762789613299158509 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_40128_40192 :
    (∑ n ∈ Ico 40128 40192, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 40128 40192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 40128 40192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1244973 : ℤ) ∧
    (∑ n ∈ Ico 40128 40192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-24899535204630057699854647001 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_40064_40192 :
    (∑ n ∈ Ico 40064 40192, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 40064 40192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 40064 40192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1618458 : ℤ) ∧
    (∑ n ∈ Ico 40064 40192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-32369265286392847313153805510 : ℤ) := by
  rcases cdemPrefixStats_40064_40128 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_40128_40192 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 40064 ≤ 40128) (by norm_num : 40128 ≤ 40192), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 40064 ≤ 40128) (by norm_num : 40128 ≤ 40192), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 40064 ≤ 40128) (by norm_num : 40128 ≤ 40192), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 40064 ≤ 40128) (by norm_num : 40128 ≤ 40192), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_39936_40192 :
    (∑ n ∈ Ico 39936 40192, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 39936 40192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 39936 40192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-993459 : ℤ) ∧
    (∑ n ∈ Ico 39936 40192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-19869121749402751099275261701 : ℤ) := by
  rcases cdemPrefixStats_39936_40064 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_40064_40192 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 39936 ≤ 40064) (by norm_num : 40064 ≤ 40192), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 39936 ≤ 40064) (by norm_num : 40064 ≤ 40192), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 39936 ≤ 40064) (by norm_num : 40064 ≤ 40192), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 39936 ≤ 40064) (by norm_num : 40064 ≤ 40192), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_40192_40256 :
    (∑ n ∈ Ico 40192 40256, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 40192 40256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 40192 40256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (870343 : ℤ) ∧
    (∑ n ∈ Ico 40192 40256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17406936131709123125015990762 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_40256_40320 :
    (∑ n ∈ Ico 40256 40320, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 40256 40320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 40256 40320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-372387 : ℤ) ∧
    (∑ n ∈ Ico 40256 40320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7447742916006886589059669108 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_40192_40320 :
    (∑ n ∈ Ico 40192 40320, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 40192 40320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 40192 40320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (497956 : ℤ) ∧
    (∑ n ∈ Ico 40192 40320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9959193215702236535956321654 : ℤ) := by
  rcases cdemPrefixStats_40192_40256 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_40256_40320 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 40192 ≤ 40256) (by norm_num : 40256 ≤ 40320), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 40192 ≤ 40256) (by norm_num : 40256 ≤ 40320), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 40192 ≤ 40256) (by norm_num : 40256 ≤ 40320), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 40192 ≤ 40256) (by norm_num : 40256 ≤ 40320), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_40320_40384 :
    (∑ n ∈ Ico 40320 40384, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 40320 40384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 40320 40384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (619782 : ℤ) ∧
    (∑ n ∈ Ico 40320 40384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12395693850189477465119751866 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_40384_40448 :
    (∑ n ∈ Ico 40384 40448, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 40384 40448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 40384 40448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (494569 : ℤ) ∧
    (∑ n ∈ Ico 40384 40448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9891381837458046162626204327 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_40320_40448 :
    (∑ n ∈ Ico 40320 40448, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 40320 40448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 40320 40448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1114351 : ℤ) ∧
    (∑ n ∈ Ico 40320 40448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (22287075687647523627745956193 : ℤ) := by
  rcases cdemPrefixStats_40320_40384 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_40384_40448 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 40320 ≤ 40384) (by norm_num : 40384 ≤ 40448), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 40320 ≤ 40384) (by norm_num : 40384 ≤ 40448), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 40320 ≤ 40384) (by norm_num : 40384 ≤ 40448), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 40320 ≤ 40384) (by norm_num : 40384 ≤ 40448), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_40192_40448 :
    (∑ n ∈ Ico 40192 40448, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 40192 40448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 40192 40448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1612307 : ℤ) ∧
    (∑ n ∈ Ico 40192 40448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (32246268903349760163702277847 : ℤ) := by
  rcases cdemPrefixStats_40192_40320 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_40320_40448 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 40192 ≤ 40320) (by norm_num : 40320 ≤ 40448), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 40192 ≤ 40320) (by norm_num : 40320 ≤ 40448), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 40192 ≤ 40320) (by norm_num : 40320 ≤ 40448), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 40192 ≤ 40320) (by norm_num : 40320 ≤ 40448), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_39936_40448 :
    (∑ n ∈ Ico 39936 40448, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 39936 40448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (315 : ℕ) ∧
    (∑ n ∈ Ico 39936 40448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (618848 : ℤ) ∧
    (∑ n ∈ Ico 39936 40448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12377147153947009064427016146 : ℤ) := by
  rcases cdemPrefixStats_39936_40192 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_40192_40448 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 39936 ≤ 40192) (by norm_num : 40192 ≤ 40448), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 39936 ≤ 40192) (by norm_num : 40192 ≤ 40448), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 39936 ≤ 40192) (by norm_num : 40192 ≤ 40448), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 39936 ≤ 40192) (by norm_num : 40192 ≤ 40448), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_40448_40512 :
    (∑ n ∈ Ico 40448 40512, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 40448 40512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 40448 40512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (494169 : ℤ) ∧
    (∑ n ∈ Ico 40448 40512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9883441576426494935557607605 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_40512_40576 :
    (∑ n ∈ Ico 40512 40576, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 40512 40576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 40512 40576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-510 : ℤ) ∧
    (∑ n ∈ Ico 40512 40576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10158621960252020957588032 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_40448_40576 :
    (∑ n ∈ Ico 40448 40576, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 40448 40576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 40448 40576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (493659 : ℤ) ∧
    (∑ n ∈ Ico 40448 40576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9873282954466242914600019573 : ℤ) := by
  rcases cdemPrefixStats_40448_40512 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_40512_40576 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 40448 ≤ 40512) (by norm_num : 40512 ≤ 40576), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 40448 ≤ 40512) (by norm_num : 40512 ≤ 40576), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 40448 ≤ 40512) (by norm_num : 40512 ≤ 40576), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 40448 ≤ 40512) (by norm_num : 40512 ≤ 40576), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_40576_40640 :
    (∑ n ∈ Ico 40576 40640, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 40576 40640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 40576 40640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-246394 : ℤ) ∧
    (∑ n ∈ Ico 40576 40640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4927931964915626085685742050 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_40640_40704 :
    (∑ n ∈ Ico 40640 40704, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 40640 40704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 40640 40704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (123301 : ℤ) ∧
    (∑ n ∈ Ico 40640 40704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2466066045397774833513510911 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_40576_40704 :
    (∑ n ∈ Ico 40576 40704, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 40576 40704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 40576 40704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-123093 : ℤ) ∧
    (∑ n ∈ Ico 40576 40704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2461865919517851252172231139 : ℤ) := by
  rcases cdemPrefixStats_40576_40640 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_40640_40704 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 40576 ≤ 40640) (by norm_num : 40640 ≤ 40704), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 40576 ≤ 40640) (by norm_num : 40640 ≤ 40704), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 40576 ≤ 40640) (by norm_num : 40640 ≤ 40704), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 40576 ≤ 40640) (by norm_num : 40640 ≤ 40704), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_40448_40704 :
    (∑ n ∈ Ico 40448 40704, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 40448 40704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 40448 40704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (370566 : ℤ) ∧
    (∑ n ∈ Ico 40448 40704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7411417034948391662427788434 : ℤ) := by
  rcases cdemPrefixStats_40448_40576 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_40576_40704 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 40448 ≤ 40576) (by norm_num : 40576 ≤ 40704), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 40448 ≤ 40576) (by norm_num : 40576 ≤ 40704), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 40448 ≤ 40576) (by norm_num : 40576 ≤ 40704), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 40448 ≤ 40576) (by norm_num : 40576 ≤ 40704), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_40704_40768 :
    (∑ n ∈ Ico 40704 40768, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 40704 40768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 40704 40768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-245050 : ℤ) ∧
    (∑ n ∈ Ico 40704 40768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4900988943815237113967995206 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_40768_40832 :
    (∑ n ∈ Ico 40768 40832, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 40768 40832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 40768 40832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (854 : ℤ) ∧
    (∑ n ∈ Ico 40768 40832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (16939680788249808536562110 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_40704_40832 :
    (∑ n ∈ Ico 40704 40832, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 40704 40832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 40704 40832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-244196 : ℤ) ∧
    (∑ n ∈ Ico 40704 40832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4884049263026987305431433096 : ℤ) := by
  rcases cdemPrefixStats_40704_40768 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_40768_40832 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 40704 ≤ 40768) (by norm_num : 40768 ≤ 40832), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 40704 ≤ 40768) (by norm_num : 40768 ≤ 40832), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 40704 ≤ 40768) (by norm_num : 40768 ≤ 40832), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 40704 ≤ 40768) (by norm_num : 40768 ≤ 40832), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_40832_40896 :
    (∑ n ∈ Ico 40832 40896, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 40832 40896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 40832 40896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (366577 : ℤ) ∧
    (∑ n ∈ Ico 40832 40896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7331547270573774257523276353 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_40896_40960 :
    (∑ n ∈ Ico 40896 40960, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 40896 40960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 40896 40960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-488851 : ℤ) ∧
    (∑ n ∈ Ico 40896 40960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9777135481715921710883796617 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_40832_40960 :
    (∑ n ∈ Ico 40832 40960, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 40832 40960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 40832 40960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-122274 : ℤ) ∧
    (∑ n ∈ Ico 40832 40960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2445588211142147453360520264 : ℤ) := by
  rcases cdemPrefixStats_40832_40896 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_40896_40960 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 40832 ≤ 40896) (by norm_num : 40896 ≤ 40960), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 40832 ≤ 40896) (by norm_num : 40896 ≤ 40960), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 40832 ≤ 40896) (by norm_num : 40896 ≤ 40960), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 40832 ≤ 40896) (by norm_num : 40896 ≤ 40960), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_40704_40960 :
    (∑ n ∈ Ico 40704 40960, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 40704 40960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 40704 40960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-366470 : ℤ) ∧
    (∑ n ∈ Ico 40704 40960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7329637474169134758791953360 : ℤ) := by
  rcases cdemPrefixStats_40704_40832 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_40832_40960 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 40704 ≤ 40832) (by norm_num : 40832 ≤ 40960), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 40704 ≤ 40832) (by norm_num : 40832 ≤ 40960), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 40704 ≤ 40832) (by norm_num : 40832 ≤ 40960), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 40704 ≤ 40832) (by norm_num : 40832 ≤ 40960), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_40448_40960 :
    (∑ n ∈ Ico 40448 40960, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 40448 40960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 40448 40960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (4096 : ℤ) ∧
    (∑ n ∈ Ico 40448 40960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (81779560779256903635835074 : ℤ) := by
  rcases cdemPrefixStats_40448_40704 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_40704_40960 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 40448 ≤ 40704) (by norm_num : 40704 ≤ 40960), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 40448 ≤ 40704) (by norm_num : 40704 ≤ 40960), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 40448 ≤ 40704) (by norm_num : 40704 ≤ 40960), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 40448 ≤ 40704) (by norm_num : 40704 ≤ 40960), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_39936_40960 :
    (∑ n ∈ Ico 39936 40960, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 39936 40960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (625 : ℕ) ∧
    (∑ n ∈ Ico 39936 40960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (622944 : ℤ) ∧
    (∑ n ∈ Ico 39936 40960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12458926714726265968062851220 : ℤ) := by
  rcases cdemPrefixStats_39936_40448 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_40448_40960 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 39936 ≤ 40448) (by norm_num : 40448 ≤ 40960), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 39936 ≤ 40448) (by norm_num : 40448 ≤ 40960), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 39936 ≤ 40448) (by norm_num : 40448 ≤ 40960), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 39936 ≤ 40448) (by norm_num : 40448 ≤ 40960), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_38912_40960 :
    (∑ n ∈ Ico 38912 40960, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 38912 40960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1247 : ℕ) ∧
    (∑ n ∈ Ico 38912 40960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1645608 : ℤ) ∧
    (∑ n ∈ Ico 38912 40960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (32912297687782289793944505975 : ℤ) := by
  rcases cdemPrefixStats_38912_39936 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_39936_40960 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 38912 ≤ 39936) (by norm_num : 39936 ≤ 40960), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 38912 ≤ 39936) (by norm_num : 39936 ≤ 40960), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 38912 ≤ 39936) (by norm_num : 39936 ≤ 40960), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 38912 ≤ 39936) (by norm_num : 39936 ≤ 40960), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_36864_40960 :
    (∑ n ∈ Ico 36864 40960, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 36864 40960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2483 : ℕ) ∧
    (∑ n ∈ Ico 36864 40960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-28012 : ℤ) ∧
    (∑ n ∈ Ico 36864 40960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-560505832981627883163084282 : ℤ) := by
  rcases cdemPrefixStats_36864_38912 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_38912_40960 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 36864 ≤ 38912) (by norm_num : 38912 ≤ 40960), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 36864 ≤ 38912) (by norm_num : 38912 ≤ 40960), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 36864 ≤ 38912) (by norm_num : 38912 ≤ 40960), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 36864 ≤ 38912) (by norm_num : 38912 ≤ 40960), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup009_checked_complete :
    (∑ n ∈ Ico 36864 40960, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 36864 40960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2483 : ℕ) ∧
    (∑ n ∈ Ico 36864 40960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-28012 : ℤ) ∧
    (∑ n ∈ Ico 36864 40960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-560505832981627883163084282 : ℤ) := cdemPrefixStats_36864_40960
end Helfgott
#print axioms Helfgott.cdemPrefixGroup009_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 36864 40960, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 36864 40960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2483 : ℕ) ∧
    (∑ n ∈ Ico 36864 40960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-28012 : ℤ) ∧
    (∑ n ∈ Ico 36864 40960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-560505832981627883163084282 : ℤ) := Helfgott.cdemPrefixGroup009_checked_complete
#print axioms solution
