-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup040_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T02:41:59.318889+00:00
-- url     : https://prove2.me/submissions/f05af912-1cf7-493b-a792-fcd5f269e3ec

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
private theorem cdemPrefixStats_163840_163904 :
    (∑ n ∈ Ico 163840 163904, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 163840 163904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 163840 163904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-30525 : ℤ) ∧
    (∑ n ∈ Ico 163840 163904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-610511662143166506167799581 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_163904_163968 :
    (∑ n ∈ Ico 163904 163968, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 163904 163968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 163904 163968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (518461 : ℤ) ∧
    (∑ n ∈ Ico 163904 163968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10369446639658272549890872833 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_163840_163968 :
    (∑ n ∈ Ico 163840 163968, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 163840 163968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 163840 163968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (487936 : ℤ) ∧
    (∑ n ∈ Ico 163840 163968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9758934977515106043723073252 : ℤ) := by
  rcases cdemPrefixStats_163840_163904 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_163904_163968 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 163840 ≤ 163904) (by norm_num : 163904 ≤ 163968), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 163840 ≤ 163904) (by norm_num : 163904 ≤ 163968), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 163840 ≤ 163904) (by norm_num : 163904 ≤ 163968), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 163840 ≤ 163904) (by norm_num : 163904 ≤ 163968), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_163968_164032 :
    (∑ n ∈ Ico 163968 164032, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 163968 164032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 163968 164032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-30537 : ℤ) ∧
    (∑ n ∈ Ico 163968 164032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-610778519874727109160790596 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_164032_164096 :
    (∑ n ∈ Ico 164032 164096, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 164032 164096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 164032 164096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-30448 : ℤ) ∧
    (∑ n ∈ Ico 164032 164096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-608998161688115105941660741 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_163968_164096 :
    (∑ n ∈ Ico 163968 164096, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 163968 164096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 163968 164096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-60985 : ℤ) ∧
    (∑ n ∈ Ico 163968 164096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1219776681562842215102451337 : ℤ) := by
  rcases cdemPrefixStats_163968_164032 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_164032_164096 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 163968 ≤ 164032) (by norm_num : 164032 ≤ 164096), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 163968 ≤ 164032) (by norm_num : 164032 ≤ 164096), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 163968 ≤ 164032) (by norm_num : 164032 ≤ 164096), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 163968 ≤ 164032) (by norm_num : 164032 ≤ 164096), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_163840_164096 :
    (∑ n ∈ Ico 163840 164096, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 163840 164096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 163840 164096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (426951 : ℤ) ∧
    (∑ n ∈ Ico 163840 164096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8539158295952263828620621915 : ℤ) := by
  rcases cdemPrefixStats_163840_163968 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_163968_164096 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 163840 ≤ 163968) (by norm_num : 163968 ≤ 164096), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 163840 ≤ 163968) (by norm_num : 163968 ≤ 164096), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 163840 ≤ 163968) (by norm_num : 163968 ≤ 164096), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 163840 ≤ 163968) (by norm_num : 163968 ≤ 164096), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_164096_164160 :
    (∑ n ∈ Ico 164096 164160, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 164096 164160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 164096 164160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (60904 : ℤ) ∧
    (∑ n ∈ Ico 164096 164160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1218134200215070185717920047 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_164160_164224 :
    (∑ n ∈ Ico 164160 164224, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 164160 164224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 164160 164224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-91358 : ℤ) ∧
    (∑ n ∈ Ico 164160 164224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1827199663312650011600851898 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_164096_164224 :
    (∑ n ∈ Ico 164096 164224, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 164096 164224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 164096 164224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-30454 : ℤ) ∧
    (∑ n ∈ Ico 164096 164224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-609065463097579825882931851 : ℤ) := by
  rcases cdemPrefixStats_164096_164160 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_164160_164224 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 164096 ≤ 164160) (by norm_num : 164160 ≤ 164224), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 164096 ≤ 164160) (by norm_num : 164160 ≤ 164224), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 164096 ≤ 164160) (by norm_num : 164160 ≤ 164224), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 164096 ≤ 164160) (by norm_num : 164160 ≤ 164224), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_164224_164288 :
    (∑ n ∈ Ico 164224 164288, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 164224 164288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 164224 164288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-243550 : ℤ) ∧
    (∑ n ∈ Ico 164224 164288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4871091073017002542824380101 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_164288_164352 :
    (∑ n ∈ Ico 164288 164352, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 164288 164352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 164288 164352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (182576 : ℤ) ∧
    (∑ n ∈ Ico 164288 164352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3651597073976767797431089052 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_164224_164352 :
    (∑ n ∈ Ico 164224 164352, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 164224 164352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 164224 164352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-60974 : ℤ) ∧
    (∑ n ∈ Ico 164224 164352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1219493999040234745393291049 : ℤ) := by
  rcases cdemPrefixStats_164224_164288 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_164288_164352 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 164224 ≤ 164288) (by norm_num : 164288 ≤ 164352), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 164224 ≤ 164288) (by norm_num : 164288 ≤ 164352), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 164224 ≤ 164288) (by norm_num : 164288 ≤ 164352), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 164224 ≤ 164288) (by norm_num : 164288 ≤ 164352), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_164096_164352 :
    (∑ n ∈ Ico 164096 164352, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 164096 164352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 164096 164352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-91428 : ℤ) ∧
    (∑ n ∈ Ico 164096 164352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1828559462137814571276222900 : ℤ) := by
  rcases cdemPrefixStats_164096_164224 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_164224_164352 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 164096 ≤ 164224) (by norm_num : 164224 ≤ 164352), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 164096 ≤ 164224) (by norm_num : 164224 ≤ 164352), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 164096 ≤ 164224) (by norm_num : 164224 ≤ 164352), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 164096 ≤ 164224) (by norm_num : 164224 ≤ 164352), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_163840_164352 :
    (∑ n ∈ Ico 163840 164352, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 163840 164352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 163840 164352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (335523 : ℤ) ∧
    (∑ n ∈ Ico 163840 164352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6710598833814449257344399015 : ℤ) := by
  rcases cdemPrefixStats_163840_164096 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_164096_164352 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 163840 ≤ 164096) (by norm_num : 164096 ≤ 164352), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 163840 ≤ 164096) (by norm_num : 164096 ≤ 164352), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 163840 ≤ 164096) (by norm_num : 164096 ≤ 164352), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 163840 ≤ 164096) (by norm_num : 164096 ≤ 164352), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_164352_164416 :
    (∑ n ∈ Ico 164352 164416, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 164352 164416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 164352 164416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-91276 : ℤ) ∧
    (∑ n ∈ Ico 164352 164416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1825516994931805744992215044 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_164416_164480 :
    (∑ n ∈ Ico 164416 164480, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 164416 164480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 164416 164480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-60830 : ℤ) ∧
    (∑ n ∈ Ico 164416 164480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1216711311117273308246386608 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_164352_164480 :
    (∑ n ∈ Ico 164352 164480, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 164352 164480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 164352 164480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-152106 : ℤ) ∧
    (∑ n ∈ Ico 164352 164480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3042228306049079053238601652 : ℤ) := by
  rcases cdemPrefixStats_164352_164416 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_164416_164480 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 164352 ≤ 164416) (by norm_num : 164416 ≤ 164480), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 164352 ≤ 164416) (by norm_num : 164416 ≤ 164480), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 164352 ≤ 164416) (by norm_num : 164416 ≤ 164480), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 164352 ≤ 164416) (by norm_num : 164416 ≤ 164480), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_164480_164544 :
    (∑ n ∈ Ico 164480 164544, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 164480 164544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 164480 164544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (121558 : ℤ) ∧
    (∑ n ∈ Ico 164480 164544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2431208257038961512613462988 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_164544_164608 :
    (∑ n ∈ Ico 164544 164608, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 164544 164608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 164544 164608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (121521 : ℤ) ∧
    (∑ n ∈ Ico 164544 164608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2430469631101450904356815237 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_164480_164608 :
    (∑ n ∈ Ico 164480 164608, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 164480 164608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 164480 164608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (243079 : ℤ) ∧
    (∑ n ∈ Ico 164480 164608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4861677888140412416970278225 : ℤ) := by
  rcases cdemPrefixStats_164480_164544 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_164544_164608 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 164480 ≤ 164544) (by norm_num : 164544 ≤ 164608), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 164480 ≤ 164544) (by norm_num : 164544 ≤ 164608), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 164480 ≤ 164544) (by norm_num : 164544 ≤ 164608), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 164480 ≤ 164544) (by norm_num : 164544 ≤ 164608), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_164352_164608 :
    (∑ n ∈ Ico 164352 164608, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 164352 164608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 164352 164608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (90973 : ℤ) ∧
    (∑ n ∈ Ico 164352 164608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1819449582091333363731676573 : ℤ) := by
  rcases cdemPrefixStats_164352_164480 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_164480_164608 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 164352 ≤ 164480) (by norm_num : 164480 ≤ 164608), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 164352 ≤ 164480) (by norm_num : 164480 ≤ 164608), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 164352 ≤ 164480) (by norm_num : 164480 ≤ 164608), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 164352 ≤ 164480) (by norm_num : 164480 ≤ 164608), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_164608_164672 :
    (∑ n ∈ Ico 164608 164672, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 164608 164672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 164608 164672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-91110 : ℤ) ∧
    (∑ n ∈ Ico 164608 164672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1822238647163682893778259194 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_164672_164736 :
    (∑ n ∈ Ico 164672 164736, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 164672 164736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 164672 164736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (30361 : ℤ) ∧
    (∑ n ∈ Ico 164672 164736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (607201290763010132454598402 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_164608_164736 :
    (∑ n ∈ Ico 164608 164736, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 164608 164736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 164608 164736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-60749 : ℤ) ∧
    (∑ n ∈ Ico 164608 164736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1215037356400672761323660792 : ℤ) := by
  rcases cdemPrefixStats_164608_164672 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_164672_164736 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 164608 ≤ 164672) (by norm_num : 164672 ≤ 164736), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 164608 ≤ 164672) (by norm_num : 164672 ≤ 164736), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 164608 ≤ 164672) (by norm_num : 164672 ≤ 164736), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 164608 ≤ 164672) (by norm_num : 164672 ≤ 164736), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_164736_164800 :
    (∑ n ∈ Ico 164736 164800, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 164736 164800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 164736 164800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (60680 : ℤ) ∧
    (∑ n ∈ Ico 164736 164800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1213651153480270651097345749 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_164800_164864 :
    (∑ n ∈ Ico 164800 164864, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 164800 164864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 164800 164864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (121318 : ℤ) ∧
    (∑ n ∈ Ico 164800 164864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2426337835247816029376783945 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_164736_164864 :
    (∑ n ∈ Ico 164736 164864, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 164736 164864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 164736 164864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (181998 : ℤ) ∧
    (∑ n ∈ Ico 164736 164864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3639988988728086680474129694 : ℤ) := by
  rcases cdemPrefixStats_164736_164800 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_164800_164864 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 164736 ≤ 164800) (by norm_num : 164800 ≤ 164864), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 164736 ≤ 164800) (by norm_num : 164800 ≤ 164864), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 164736 ≤ 164800) (by norm_num : 164800 ≤ 164864), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 164736 ≤ 164800) (by norm_num : 164800 ≤ 164864), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_164608_164864 :
    (∑ n ∈ Ico 164608 164864, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 164608 164864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 164608 164864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (121249 : ℤ) ∧
    (∑ n ∈ Ico 164608 164864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2424951632327413919150468902 : ℤ) := by
  rcases cdemPrefixStats_164608_164736 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_164736_164864 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 164608 ≤ 164736) (by norm_num : 164736 ≤ 164864), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 164608 ≤ 164736) (by norm_num : 164736 ≤ 164864), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 164608 ≤ 164736) (by norm_num : 164736 ≤ 164864), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 164608 ≤ 164736) (by norm_num : 164736 ≤ 164864), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_164352_164864 :
    (∑ n ∈ Ico 164352 164864, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 164352 164864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 164352 164864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (212222 : ℤ) ∧
    (∑ n ∈ Ico 164352 164864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4244401214418747282882145475 : ℤ) := by
  rcases cdemPrefixStats_164352_164608 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_164608_164864 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 164352 ≤ 164608) (by norm_num : 164608 ≤ 164864), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 164352 ≤ 164608) (by norm_num : 164608 ≤ 164864), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 164352 ≤ 164608) (by norm_num : 164608 ≤ 164864), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 164352 ≤ 164608) (by norm_num : 164608 ≤ 164864), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_163840_164864 :
    (∑ n ∈ Ico 163840 164864, mobiusTreeValue 16 mobiusTable1200001 n) = (18 : ℤ) ∧
    (∑ n ∈ Ico 163840 164864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (624 : ℕ) ∧
    (∑ n ∈ Ico 163840 164864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (547745 : ℤ) ∧
    (∑ n ∈ Ico 163840 164864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10955000048233196540226544490 : ℤ) := by
  rcases cdemPrefixStats_163840_164352 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_164352_164864 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 163840 ≤ 164352) (by norm_num : 164352 ≤ 164864), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 163840 ≤ 164352) (by norm_num : 164352 ≤ 164864), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 163840 ≤ 164352) (by norm_num : 164352 ≤ 164864), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 163840 ≤ 164352) (by norm_num : 164352 ≤ 164864), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_164864_164928 :
    (∑ n ∈ Ico 164864 164928, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 164864 164928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 164864 164928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (60640 : ℤ) ∧
    (∑ n ∈ Ico 164864 164928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1212860037165333153491297781 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_164928_164992 :
    (∑ n ∈ Ico 164928 164992, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 164928 164992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 164928 164992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (272794 : ℤ) ∧
    (∑ n ∈ Ico 164928 164992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5456037175597577889978715812 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_164864_164992 :
    (∑ n ∈ Ico 164864 164992, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 164864 164992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 164864 164992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (333434 : ℤ) ∧
    (∑ n ∈ Ico 164864 164992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6668897212762911043470013593 : ℤ) := by
  rcases cdemPrefixStats_164864_164928 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_164928_164992 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 164864 ≤ 164928) (by norm_num : 164928 ≤ 164992), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 164864 ≤ 164928) (by norm_num : 164928 ≤ 164992), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 164864 ≤ 164928) (by norm_num : 164928 ≤ 164992), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 164864 ≤ 164928) (by norm_num : 164928 ≤ 164992), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_164992_165056 :
    (∑ n ∈ Ico 164992 165056, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 164992 165056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 164992 165056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (151532 : ℤ) ∧
    (∑ n ∈ Ico 164992 165056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3030758299893890902028638136 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_165056_165120 :
    (∑ n ∈ Ico 165056 165120, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 165056 165120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 165056 165120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (121161 : ℤ) ∧
    (∑ n ∈ Ico 165056 165120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2423214431233062027090565653 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_164992_165120 :
    (∑ n ∈ Ico 164992 165120, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 164992 165120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 164992 165120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (272693 : ℤ) ∧
    (∑ n ∈ Ico 164992 165120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5453972731126952929119203789 : ℤ) := by
  rcases cdemPrefixStats_164992_165056 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_165056_165120 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 164992 ≤ 165056) (by norm_num : 165056 ≤ 165120), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 164992 ≤ 165056) (by norm_num : 165056 ≤ 165120), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 164992 ≤ 165056) (by norm_num : 165056 ≤ 165120), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 164992 ≤ 165056) (by norm_num : 165056 ≤ 165120), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_164864_165120 :
    (∑ n ∈ Ico 164864 165120, mobiusTreeValue 16 mobiusTable1200001 n) = (20 : ℤ) ∧
    (∑ n ∈ Ico 164864 165120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 164864 165120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (606127 : ℤ) ∧
    (∑ n ∈ Ico 164864 165120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12122869943889863972589217382 : ℤ) := by
  rcases cdemPrefixStats_164864_164992 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_164992_165120 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 164864 ≤ 164992) (by norm_num : 164992 ≤ 165120), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 164864 ≤ 164992) (by norm_num : 164992 ≤ 165120), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 164864 ≤ 164992) (by norm_num : 164992 ≤ 165120), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 164864 ≤ 164992) (by norm_num : 164992 ≤ 165120), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_165120_165184 :
    (∑ n ∈ Ico 165120 165184, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 165120 165184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 165120 165184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (242206 : ℤ) ∧
    (∑ n ∈ Ico 165120 165184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4844213139259543662210702302 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_165184_165248 :
    (∑ n ∈ Ico 165184 165248, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 165184 165248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 165184 165248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (90798 : ℤ) ∧
    (∑ n ∈ Ico 165184 165248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1815976992014906820628714776 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_165120_165248 :
    (∑ n ∈ Ico 165120 165248, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 165120 165248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 165120 165248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (333004 : ℤ) ∧
    (∑ n ∈ Ico 165120 165248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6660190131274450482839417078 : ℤ) := by
  rcases cdemPrefixStats_165120_165184 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_165184_165248 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 165120 ≤ 165184) (by norm_num : 165184 ≤ 165248), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 165120 ≤ 165184) (by norm_num : 165184 ≤ 165248), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 165120 ≤ 165184) (by norm_num : 165184 ≤ 165248), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 165120 ≤ 165184) (by norm_num : 165184 ≤ 165248), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_165248_165312 :
    (∑ n ∈ Ico 165248 165312, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 165248 165312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 165248 165312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-30246 : ℤ) ∧
    (∑ n ∈ Ico 165248 165312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-604960636449603273672312745 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_165312_165376 :
    (∑ n ∈ Ico 165312 165376, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 165312 165376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 165312 165376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (14 : ℤ) ∧
    (∑ n ∈ Ico 165312 165376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (288994835297088657904017 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_165248_165376 :
    (∑ n ∈ Ico 165248 165376, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 165248 165376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 165248 165376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-30232 : ℤ) ∧
    (∑ n ∈ Ico 165248 165376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-604671641614306185014408728 : ℤ) := by
  rcases cdemPrefixStats_165248_165312 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_165312_165376 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 165248 ≤ 165312) (by norm_num : 165312 ≤ 165376), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 165248 ≤ 165312) (by norm_num : 165312 ≤ 165376), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 165248 ≤ 165312) (by norm_num : 165312 ≤ 165376), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 165248 ≤ 165312) (by norm_num : 165312 ≤ 165376), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_165120_165376 :
    (∑ n ∈ Ico 165120 165376, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 165120 165376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 165120 165376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (302772 : ℤ) ∧
    (∑ n ∈ Ico 165120 165376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6055518489660144297825008350 : ℤ) := by
  rcases cdemPrefixStats_165120_165248 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_165248_165376 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 165120 ≤ 165248) (by norm_num : 165248 ≤ 165376), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 165120 ≤ 165248) (by norm_num : 165248 ≤ 165376), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 165120 ≤ 165248) (by norm_num : 165248 ≤ 165376), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 165120 ≤ 165248) (by norm_num : 165248 ≤ 165376), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_164864_165376 :
    (∑ n ∈ Ico 164864 165376, mobiusTreeValue 16 mobiusTable1200001 n) = (30 : ℤ) ∧
    (∑ n ∈ Ico 164864 165376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 164864 165376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (908899 : ℤ) ∧
    (∑ n ∈ Ico 164864 165376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18178388433550008270414225732 : ℤ) := by
  rcases cdemPrefixStats_164864_165120 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_165120_165376 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 164864 ≤ 165120) (by norm_num : 165120 ≤ 165376), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 164864 ≤ 165120) (by norm_num : 165120 ≤ 165376), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 164864 ≤ 165120) (by norm_num : 165120 ≤ 165376), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 164864 ≤ 165120) (by norm_num : 165120 ≤ 165376), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_165376_165440 :
    (∑ n ∈ Ico 165376 165440, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 165376 165440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 165376 165440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (30205 : ℤ) ∧
    (∑ n ∈ Ico 165376 165440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (604043041192687340127428598 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_165440_165504 :
    (∑ n ∈ Ico 165440 165504, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 165440 165504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 165440 165504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-151052 : ℤ) ∧
    (∑ n ∈ Ico 165440 165504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3021107778933472283262889414 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_165376_165504 :
    (∑ n ∈ Ico 165376 165504, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 165376 165504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 165376 165504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-120847 : ℤ) ∧
    (∑ n ∈ Ico 165376 165504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2417064737740784943135460816 : ℤ) := by
  rcases cdemPrefixStats_165376_165440 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_165440_165504 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 165376 ≤ 165440) (by norm_num : 165440 ≤ 165504), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 165376 ≤ 165440) (by norm_num : 165440 ≤ 165504), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 165376 ≤ 165440) (by norm_num : 165440 ≤ 165504), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 165376 ≤ 165440) (by norm_num : 165440 ≤ 165504), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_165504_165568 :
    (∑ n ∈ Ico 165504 165568, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 165504 165568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 165504 165568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-302062 : ℤ) ∧
    (∑ n ∈ Ico 165504 165568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6041332433818454854188989338 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_165568_165632 :
    (∑ n ∈ Ico 165568 165632, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 165568 165632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 165568 165632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (30165 : ℤ) ∧
    (∑ n ∈ Ico 165568 165632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (603350639911831254680119315 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_165504_165632 :
    (∑ n ∈ Ico 165504 165632, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 165504 165632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 165504 165632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-271897 : ℤ) ∧
    (∑ n ∈ Ico 165504 165632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5437981793906623599508870023 : ℤ) := by
  rcases cdemPrefixStats_165504_165568 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_165568_165632 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 165504 ≤ 165568) (by norm_num : 165568 ≤ 165632), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 165504 ≤ 165568) (by norm_num : 165568 ≤ 165632), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 165504 ≤ 165568) (by norm_num : 165568 ≤ 165632), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 165504 ≤ 165568) (by norm_num : 165568 ≤ 165632), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_165376_165632 :
    (∑ n ∈ Ico 165376 165632, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 165376 165632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 165376 165632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-392744 : ℤ) ∧
    (∑ n ∈ Ico 165376 165632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7855046531647408542644330839 : ℤ) := by
  rcases cdemPrefixStats_165376_165504 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_165504_165632 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 165376 ≤ 165504) (by norm_num : 165504 ≤ 165632), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 165376 ≤ 165504) (by norm_num : 165504 ≤ 165632), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 165376 ≤ 165504) (by norm_num : 165504 ≤ 165632), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 165376 ≤ 165504) (by norm_num : 165504 ≤ 165632), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_165632_165696 :
    (∑ n ∈ Ico 165632 165696, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 165632 165696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 165632 165696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (181094 : ℤ) ∧
    (∑ n ∈ Ico 165632 165696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3621916279921864833762884870 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_165696_165760 :
    (∑ n ∈ Ico 165696 165760, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 165696 165760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 165696 165760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-90530 : ℤ) ∧
    (∑ n ∈ Ico 165696 165760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1810682976434251071508049361 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_165632_165760 :
    (∑ n ∈ Ico 165632 165760, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 165632 165760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 165632 165760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (90564 : ℤ) ∧
    (∑ n ∈ Ico 165632 165760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1811233303487613762254835509 : ℤ) := by
  rcases cdemPrefixStats_165632_165696 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_165696_165760 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 165632 ≤ 165696) (by norm_num : 165696 ≤ 165760), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 165632 ≤ 165696) (by norm_num : 165696 ≤ 165760), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 165632 ≤ 165696) (by norm_num : 165696 ≤ 165760), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 165632 ≤ 165696) (by norm_num : 165696 ≤ 165760), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_165760_165824 :
    (∑ n ∈ Ico 165760 165824, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 165760 165824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 165760 165824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (241283 : ℤ) ∧
    (∑ n ∈ Ico 165760 165824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4825741737705552542984472727 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_165824_165888 :
    (∑ n ∈ Ico 165824 165888, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 165824 165888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 165824 165888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-241153 : ℤ) ∧
    (∑ n ∈ Ico 165824 165888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4823214195528669633548904533 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_165760_165888 :
    (∑ n ∈ Ico 165760 165888, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 165760 165888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 165760 165888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (130 : ℤ) ∧
    (∑ n ∈ Ico 165760 165888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2527542176882909435568194 : ℤ) := by
  rcases cdemPrefixStats_165760_165824 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_165824_165888 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 165760 ≤ 165824) (by norm_num : 165824 ≤ 165888), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 165760 ≤ 165824) (by norm_num : 165824 ≤ 165888), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 165760 ≤ 165824) (by norm_num : 165824 ≤ 165888), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 165760 ≤ 165824) (by norm_num : 165824 ≤ 165888), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_165632_165888 :
    (∑ n ∈ Ico 165632 165888, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 165632 165888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 165632 165888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (90694 : ℤ) ∧
    (∑ n ∈ Ico 165632 165888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1813760845664496671690403703 : ℤ) := by
  rcases cdemPrefixStats_165632_165760 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_165760_165888 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 165632 ≤ 165760) (by norm_num : 165760 ≤ 165888), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 165632 ≤ 165760) (by norm_num : 165760 ≤ 165888), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 165632 ≤ 165760) (by norm_num : 165760 ≤ 165888), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 165632 ≤ 165760) (by norm_num : 165760 ≤ 165888), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_165376_165888 :
    (∑ n ∈ Ico 165376 165888, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 165376 165888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 165376 165888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-302050 : ℤ) ∧
    (∑ n ∈ Ico 165376 165888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6041285685982911870953927136 : ℤ) := by
  rcases cdemPrefixStats_165376_165632 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_165632_165888 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 165376 ≤ 165632) (by norm_num : 165632 ≤ 165888), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 165376 ≤ 165632) (by norm_num : 165632 ≤ 165888), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 165376 ≤ 165632) (by norm_num : 165632 ≤ 165888), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 165376 ≤ 165632) (by norm_num : 165632 ≤ 165888), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_164864_165888 :
    (∑ n ∈ Ico 164864 165888, mobiusTreeValue 16 mobiusTable1200001 n) = (20 : ℤ) ∧
    (∑ n ∈ Ico 164864 165888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (624 : ℕ) ∧
    (∑ n ∈ Ico 164864 165888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (606849 : ℤ) ∧
    (∑ n ∈ Ico 164864 165888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12137102747567096399460298596 : ℤ) := by
  rcases cdemPrefixStats_164864_165376 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_165376_165888 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 164864 ≤ 165376) (by norm_num : 165376 ≤ 165888), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 164864 ≤ 165376) (by norm_num : 165376 ≤ 165888), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 164864 ≤ 165376) (by norm_num : 165376 ≤ 165888), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 164864 ≤ 165376) (by norm_num : 165376 ≤ 165888), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_163840_165888 :
    (∑ n ∈ Ico 163840 165888, mobiusTreeValue 16 mobiusTable1200001 n) = (38 : ℤ) ∧
    (∑ n ∈ Ico 163840 165888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1248 : ℕ) ∧
    (∑ n ∈ Ico 163840 165888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1154594 : ℤ) ∧
    (∑ n ∈ Ico 163840 165888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (23092102795800292939686843086 : ℤ) := by
  rcases cdemPrefixStats_163840_164864 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_164864_165888 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 163840 ≤ 164864) (by norm_num : 164864 ≤ 165888), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 163840 ≤ 164864) (by norm_num : 164864 ≤ 165888), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 163840 ≤ 164864) (by norm_num : 164864 ≤ 165888), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 163840 ≤ 164864) (by norm_num : 164864 ≤ 165888), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_165888_165952 :
    (∑ n ∈ Ico 165888 165952, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 165888 165952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 165888 165952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (24 : ℤ) ∧
    (∑ n ∈ Ico 165888 165952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (515789965078388589648589 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_165952_166016 :
    (∑ n ∈ Ico 165952 166016, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 165952 166016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 165952 166016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (271082 : ℤ) ∧
    (∑ n ∈ Ico 165952 166016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5421773993334052436300285155 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_165888_166016 :
    (∑ n ∈ Ico 165888 166016, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 165888 166016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 165888 166016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (271106 : ℤ) ∧
    (∑ n ∈ Ico 165888 166016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5422289783299130824889933744 : ℤ) := by
  rcases cdemPrefixStats_165888_165952 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_165952_166016 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 165888 ≤ 165952) (by norm_num : 165952 ≤ 166016), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 165888 ≤ 165952) (by norm_num : 165952 ≤ 166016), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 165888 ≤ 165952) (by norm_num : 165952 ≤ 166016), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 165888 ≤ 165952) (by norm_num : 165952 ≤ 166016), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_166016_166080 :
    (∑ n ∈ Ico 166016 166080, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 166016 166080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 166016 166080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-120449 : ℤ) ∧
    (∑ n ∈ Ico 166016 166080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2409068942705386146476410278 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_166080_166144 :
    (∑ n ∈ Ico 166080 166144, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 166080 166144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 166080 166144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (30097 : ℤ) ∧
    (∑ n ∈ Ico 166080 166144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (601978100734142698598601608 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_166016_166144 :
    (∑ n ∈ Ico 166016 166144, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 166016 166144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 166016 166144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-90352 : ℤ) ∧
    (∑ n ∈ Ico 166016 166144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1807090841971243447877808670 : ℤ) := by
  rcases cdemPrefixStats_166016_166080 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_166080_166144 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 166016 ≤ 166080) (by norm_num : 166080 ≤ 166144), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 166016 ≤ 166080) (by norm_num : 166080 ≤ 166144), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 166016 ≤ 166080) (by norm_num : 166080 ≤ 166144), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 166016 ≤ 166080) (by norm_num : 166080 ≤ 166144), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_165888_166144 :
    (∑ n ∈ Ico 165888 166144, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 165888 166144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 165888 166144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (180754 : ℤ) ∧
    (∑ n ∈ Ico 165888 166144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3615198941327887377012125074 : ℤ) := by
  rcases cdemPrefixStats_165888_166016 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_166016_166144 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 165888 ≤ 166016) (by norm_num : 166016 ≤ 166144), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 165888 ≤ 166016) (by norm_num : 166016 ≤ 166144), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 165888 ≤ 166016) (by norm_num : 166016 ≤ 166144), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 165888 ≤ 166016) (by norm_num : 166016 ≤ 166144), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_166144_166208 :
    (∑ n ∈ Ico 166144 166208, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 166144 166208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 166144 166208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-270795 : ℤ) ∧
    (∑ n ∈ Ico 166144 166208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5415937389668046719961469490 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_166208_166272 :
    (∑ n ∈ Ico 166208 166272, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 166208 166272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 166208 166272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (30106 : ℤ) ∧
    (∑ n ∈ Ico 166208 166272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (602108089047528659456486141 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_166144_166272 :
    (∑ n ∈ Ico 166144 166272, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 166144 166272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 166144 166272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-240689 : ℤ) ∧
    (∑ n ∈ Ico 166144 166272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4813829300620518060504983349 : ℤ) := by
  rcases cdemPrefixStats_166144_166208 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_166208_166272 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 166144 ≤ 166208) (by norm_num : 166208 ≤ 166272), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 166144 ≤ 166208) (by norm_num : 166208 ≤ 166272), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 166144 ≤ 166208) (by norm_num : 166208 ≤ 166272), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 166144 ≤ 166208) (by norm_num : 166208 ≤ 166272), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_166272_166336 :
    (∑ n ∈ Ico 166272 166336, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 166272 166336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 166272 166336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-120290 : ℤ) ∧
    (∑ n ∈ Ico 166272 166336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2405830330215294462324195353 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_166336_166400 :
    (∑ n ∈ Ico 166336 166400, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 166336 166400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 166336 166400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-240408 : ℤ) ∧
    (∑ n ∈ Ico 166336 166400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4808223294263327822023633611 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_166272_166400 :
    (∑ n ∈ Ico 166272 166400, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 166272 166400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 166272 166400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-360698 : ℤ) ∧
    (∑ n ∈ Ico 166272 166400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7214053624478622284347828964 : ℤ) := by
  rcases cdemPrefixStats_166272_166336 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_166336_166400 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 166272 ≤ 166336) (by norm_num : 166336 ≤ 166400), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 166272 ≤ 166336) (by norm_num : 166336 ≤ 166400), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 166272 ≤ 166336) (by norm_num : 166336 ≤ 166400), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 166272 ≤ 166336) (by norm_num : 166336 ≤ 166400), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_166144_166400 :
    (∑ n ∈ Ico 166144 166400, mobiusTreeValue 16 mobiusTable1200001 n) = (-20 : ℤ) ∧
    (∑ n ∈ Ico 166144 166400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 166144 166400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-601387 : ℤ) ∧
    (∑ n ∈ Ico 166144 166400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12027882925099140344852812313 : ℤ) := by
  rcases cdemPrefixStats_166144_166272 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_166272_166400 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 166144 ≤ 166272) (by norm_num : 166272 ≤ 166400), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 166144 ≤ 166272) (by norm_num : 166272 ≤ 166400), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 166144 ≤ 166272) (by norm_num : 166272 ≤ 166400), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 166144 ≤ 166272) (by norm_num : 166272 ≤ 166400), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_165888_166400 :
    (∑ n ∈ Ico 165888 166400, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 165888 166400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 165888 166400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-420633 : ℤ) ∧
    (∑ n ∈ Ico 165888 166400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8412683983771252967840687239 : ℤ) := by
  rcases cdemPrefixStats_165888_166144 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_166144_166400 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 165888 ≤ 166144) (by norm_num : 166144 ≤ 166400), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 165888 ≤ 166144) (by norm_num : 166144 ≤ 166400), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 165888 ≤ 166144) (by norm_num : 166144 ≤ 166400), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 165888 ≤ 166144) (by norm_num : 166144 ≤ 166400), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_166400_166464 :
    (∑ n ∈ Ico 166400 166464, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 166400 166464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 166400 166464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (180239 : ℤ) ∧
    (∑ n ∈ Ico 166400 166464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3604855767467300333291550991 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_166464_166528 :
    (∑ n ∈ Ico 166464 166528, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 166464 166528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 166464 166528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (240229 : ℤ) ∧
    (∑ n ∈ Ico 166464 166528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4804649687610065662873344823 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_166400_166528 :
    (∑ n ∈ Ico 166400 166528, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 166400 166528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 166400 166528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (420468 : ℤ) ∧
    (∑ n ∈ Ico 166400 166528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8409505455077365996164895814 : ℤ) := by
  rcases cdemPrefixStats_166400_166464 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_166464_166528 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 166400 ≤ 166464) (by norm_num : 166464 ≤ 166528), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 166400 ≤ 166464) (by norm_num : 166464 ≤ 166528), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 166400 ≤ 166464) (by norm_num : 166464 ≤ 166528), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 166400 ≤ 166464) (by norm_num : 166464 ≤ 166528), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_166528_166592 :
    (∑ n ∈ Ico 166528 166592, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 166528 166592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 166528 166592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (11 : ℤ) ∧
    (∑ n ∈ Ico 166528 166592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (212793174410682914766813 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_166592_166656 :
    (∑ n ∈ Ico 166592 166656, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 166592 166656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 166592 166656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-210072 : ℤ) ∧
    (∑ n ∈ Ico 166592 166656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4201493344692337727626127363 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_166528_166656 :
    (∑ n ∈ Ico 166528 166656, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 166528 166656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 166528 166656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-210061 : ℤ) ∧
    (∑ n ∈ Ico 166528 166656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4201280551517927044711360550 : ℤ) := by
  rcases cdemPrefixStats_166528_166592 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_166592_166656 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 166528 ≤ 166592) (by norm_num : 166592 ≤ 166656), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 166528 ≤ 166592) (by norm_num : 166592 ≤ 166656), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 166528 ≤ 166592) (by norm_num : 166592 ≤ 166656), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 166528 ≤ 166592) (by norm_num : 166592 ≤ 166656), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_166400_166656 :
    (∑ n ∈ Ico 166400 166656, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 166400 166656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 166400 166656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (210407 : ℤ) ∧
    (∑ n ∈ Ico 166400 166656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4208224903559438951453535264 : ℤ) := by
  rcases cdemPrefixStats_166400_166528 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_166528_166656 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 166400 ≤ 166528) (by norm_num : 166528 ≤ 166656), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 166400 ≤ 166528) (by norm_num : 166528 ≤ 166656), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 166400 ≤ 166528) (by norm_num : 166528 ≤ 166656), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 166400 ≤ 166528) (by norm_num : 166528 ≤ 166656), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_166656_166720 :
    (∑ n ∈ Ico 166656 166720, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 166656 166720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 166656 166720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-51 : ℤ) ∧
    (∑ n ∈ Ico 166656 166720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1022164814474456946354866 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_166720_166784 :
    (∑ n ∈ Ico 166720 166784, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 166720 166784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 166720 166784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 166720 166784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-104304927134650816783327 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_166656_166784 :
    (∑ n ∈ Ico 166656 166784, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 166656 166784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 166656 166784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-54 : ℤ) ∧
    (∑ n ∈ Ico 166656 166784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1126469741609107763138193 : ℤ) := by
  rcases cdemPrefixStats_166656_166720 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_166720_166784 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 166656 ≤ 166720) (by norm_num : 166720 ≤ 166784), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 166656 ≤ 166720) (by norm_num : 166720 ≤ 166784), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 166656 ≤ 166720) (by norm_num : 166720 ≤ 166784), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 166656 ≤ 166720) (by norm_num : 166720 ≤ 166784), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_166784_166848 :
    (∑ n ∈ Ico 166784 166848, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 166784 166848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 166784 166848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-59928 : ℤ) ∧
    (∑ n ∈ Ico 166784 166848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1198537714229958454304594917 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_166848_166912 :
    (∑ n ∈ Ico 166848 166912, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 166848 166912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 166848 166912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-29971 : ℤ) ∧
    (∑ n ∈ Ico 166848 166912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-599448517888766187608895627 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_166784_166912 :
    (∑ n ∈ Ico 166784 166912, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 166784 166912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 166784 166912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-89899 : ℤ) ∧
    (∑ n ∈ Ico 166784 166912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1797986232118724641913490544 : ℤ) := by
  rcases cdemPrefixStats_166784_166848 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_166848_166912 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 166784 ≤ 166848) (by norm_num : 166848 ≤ 166912), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 166784 ≤ 166848) (by norm_num : 166848 ≤ 166912), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 166784 ≤ 166848) (by norm_num : 166848 ≤ 166912), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 166784 ≤ 166848) (by norm_num : 166848 ≤ 166912), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_166656_166912 :
    (∑ n ∈ Ico 166656 166912, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 166656 166912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 166656 166912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-89953 : ℤ) ∧
    (∑ n ∈ Ico 166656 166912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1799112701860333749676628737 : ℤ) := by
  rcases cdemPrefixStats_166656_166784 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_166784_166912 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 166656 ≤ 166784) (by norm_num : 166784 ≤ 166912), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 166656 ≤ 166784) (by norm_num : 166784 ≤ 166912), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 166656 ≤ 166784) (by norm_num : 166784 ≤ 166912), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 166656 ≤ 166784) (by norm_num : 166784 ≤ 166912), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_166400_166912 :
    (∑ n ∈ Ico 166400 166912, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 166400 166912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 166400 166912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (120454 : ℤ) ∧
    (∑ n ∈ Ico 166400 166912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2409112201699105201776906527 : ℤ) := by
  rcases cdemPrefixStats_166400_166656 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_166656_166912 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 166400 ≤ 166656) (by norm_num : 166656 ≤ 166912), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 166400 ≤ 166656) (by norm_num : 166656 ≤ 166912), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 166400 ≤ 166656) (by norm_num : 166656 ≤ 166912), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 166400 ≤ 166656) (by norm_num : 166656 ≤ 166912), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_165888_166912 :
    (∑ n ∈ Ico 165888 166912, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 165888 166912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (622 : ℕ) ∧
    (∑ n ∈ Ico 165888 166912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-300179 : ℤ) ∧
    (∑ n ∈ Ico 165888 166912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6003571782072147766063780712 : ℤ) := by
  rcases cdemPrefixStats_165888_166400 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_166400_166912 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 165888 ≤ 166400) (by norm_num : 166400 ≤ 166912), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 165888 ≤ 166400) (by norm_num : 166400 ≤ 166912), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 165888 ≤ 166400) (by norm_num : 166400 ≤ 166912), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 165888 ≤ 166400) (by norm_num : 166400 ≤ 166912), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_166912_166976 :
    (∑ n ∈ Ico 166912 166976, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 166912 166976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 166912 166976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (119830 : ℤ) ∧
    (∑ n ∈ Ico 166912 166976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2396615859491487006510652696 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_166976_167040 :
    (∑ n ∈ Ico 166976 167040, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 166976 167040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 166976 167040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-359201 : ℤ) ∧
    (∑ n ∈ Ico 166976 167040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7184140969251050496627797049 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_166912_167040 :
    (∑ n ∈ Ico 166912 167040, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 166912 167040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 166912 167040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-239371 : ℤ) ∧
    (∑ n ∈ Ico 166912 167040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4787525109759563490117144353 : ℤ) := by
  rcases cdemPrefixStats_166912_166976 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_166976_167040 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 166912 ≤ 166976) (by norm_num : 166976 ≤ 167040), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 166912 ≤ 166976) (by norm_num : 166976 ≤ 167040), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 166912 ≤ 166976) (by norm_num : 166976 ≤ 167040), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 166912 ≤ 166976) (by norm_num : 166976 ≤ 167040), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_167040_167104 :
    (∑ n ∈ Ico 167040 167104, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 167040 167104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 167040 167104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-119708 : ℤ) ∧
    (∑ n ∈ Ico 167040 167104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2394173768772407654654326406 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_167104_167168 :
    (∑ n ∈ Ico 167104 167168, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 167104 167168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 167104 167168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (329044 : ℤ) ∧
    (∑ n ∈ Ico 167104 167168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6580936788319558834381775119 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_167040_167168 :
    (∑ n ∈ Ico 167040 167168, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 167040 167168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 167040 167168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (209336 : ℤ) ∧
    (∑ n ∈ Ico 167040 167168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4186763019547151179727448713 : ℤ) := by
  rcases cdemPrefixStats_167040_167104 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_167104_167168 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 167040 ≤ 167104) (by norm_num : 167104 ≤ 167168), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 167040 ≤ 167104) (by norm_num : 167104 ≤ 167168), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 167040 ≤ 167104) (by norm_num : 167104 ≤ 167168), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 167040 ≤ 167104) (by norm_num : 167104 ≤ 167168), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_166912_167168 :
    (∑ n ∈ Ico 166912 167168, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 166912 167168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 166912 167168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-30035 : ℤ) ∧
    (∑ n ∈ Ico 166912 167168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-600762090212412310389695640 : ℤ) := by
  rcases cdemPrefixStats_166912_167040 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_167040_167168 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 166912 ≤ 167040) (by norm_num : 167040 ≤ 167168), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 166912 ≤ 167040) (by norm_num : 167040 ≤ 167168), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 166912 ≤ 167040) (by norm_num : 167040 ≤ 167168), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 166912 ≤ 167040) (by norm_num : 167040 ≤ 167168), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_167168_167232 :
    (∑ n ∈ Ico 167168 167232, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 167168 167232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 167168 167232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (179412 : ℤ) ∧
    (∑ n ∈ Ico 167168 167232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3588219876387551573946590771 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_167232_167296 :
    (∑ n ∈ Ico 167232 167296, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 167232 167296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 167232 167296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (59755 : ℤ) ∧
    (∑ n ∈ Ico 167232 167296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1195078370767056865199418971 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_167168_167296 :
    (∑ n ∈ Ico 167168 167296, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 167168 167296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 167168 167296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (239167 : ℤ) ∧
    (∑ n ∈ Ico 167168 167296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4783298247154608439146009742 : ℤ) := by
  rcases cdemPrefixStats_167168_167232 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_167232_167296 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 167168 ≤ 167232) (by norm_num : 167232 ≤ 167296), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 167168 ≤ 167232) (by norm_num : 167232 ≤ 167296), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 167168 ≤ 167232) (by norm_num : 167232 ≤ 167296), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 167168 ≤ 167232) (by norm_num : 167232 ≤ 167296), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_167296_167360 :
    (∑ n ∈ Ico 167296 167360, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 167296 167360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (35 : ℕ) ∧
    (∑ n ∈ Ico 167296 167360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-89669 : ℤ) ∧
    (∑ n ∈ Ico 167296 167360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1793418034579734372362465313 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_167360_167424 :
    (∑ n ∈ Ico 167360 167424, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 167360 167424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 167360 167424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (30 : ℤ) ∧
    (∑ n ∈ Ico 167360 167424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (571016490683849916497812 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_167296_167424 :
    (∑ n ∈ Ico 167296 167424, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 167296 167424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 167296 167424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-89639 : ℤ) ∧
    (∑ n ∈ Ico 167296 167424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1792847018089050522445967501 : ℤ) := by
  rcases cdemPrefixStats_167296_167360 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_167360_167424 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 167296 ≤ 167360) (by norm_num : 167360 ≤ 167424), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 167296 ≤ 167360) (by norm_num : 167360 ≤ 167424), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 167296 ≤ 167360) (by norm_num : 167360 ≤ 167424), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 167296 ≤ 167360) (by norm_num : 167360 ≤ 167424), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_167168_167424 :
    (∑ n ∈ Ico 167168 167424, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 167168 167424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 167168 167424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (149528 : ℤ) ∧
    (∑ n ∈ Ico 167168 167424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2990451229065557916700042241 : ℤ) := by
  rcases cdemPrefixStats_167168_167296 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_167296_167424 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 167168 ≤ 167296) (by norm_num : 167296 ≤ 167424), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 167168 ≤ 167296) (by norm_num : 167296 ≤ 167424), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 167168 ≤ 167296) (by norm_num : 167296 ≤ 167424), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 167168 ≤ 167296) (by norm_num : 167296 ≤ 167424), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_166912_167424 :
    (∑ n ∈ Ico 166912 167424, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 166912 167424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 166912 167424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (119493 : ℤ) ∧
    (∑ n ∈ Ico 166912 167424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2389689138853145606310346601 : ℤ) := by
  rcases cdemPrefixStats_166912_167168 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_167168_167424 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 166912 ≤ 167168) (by norm_num : 167168 ≤ 167424), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 166912 ≤ 167168) (by norm_num : 167168 ≤ 167424), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 166912 ≤ 167168) (by norm_num : 167168 ≤ 167424), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 166912 ≤ 167168) (by norm_num : 167168 ≤ 167424), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_167424_167488 :
    (∑ n ∈ Ico 167424 167488, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 167424 167488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 167424 167488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (29823 : ℤ) ∧
    (∑ n ∈ Ico 167424 167488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (596451480034310870201940679 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_167488_167552 :
    (∑ n ∈ Ico 167488 167552, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 167488 167552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 167488 167552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-27 : ℤ) ∧
    (∑ n ∈ Ico 167488 167552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-516743565598978806293437 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_167424_167552 :
    (∑ n ∈ Ico 167424 167552, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 167424 167552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 167424 167552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (29796 : ℤ) ∧
    (∑ n ∈ Ico 167424 167552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (595934736468711891395647242 : ℤ) := by
  rcases cdemPrefixStats_167424_167488 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_167488_167552 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 167424 ≤ 167488) (by norm_num : 167488 ≤ 167552), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 167424 ≤ 167488) (by norm_num : 167488 ≤ 167552), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 167424 ≤ 167488) (by norm_num : 167488 ≤ 167552), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 167424 ≤ 167488) (by norm_num : 167488 ≤ 167552), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_167552_167616 :
    (∑ n ∈ Ico 167552 167616, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 167552 167616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 167552 167616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-59638 : ℤ) ∧
    (∑ n ∈ Ico 167552 167616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1192811771377484076274749343 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_167616_167680 :
    (∑ n ∈ Ico 167616 167680, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 167616 167680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 167616 167680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-298247 : ℤ) ∧
    (∑ n ∈ Ico 167616 167680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5965028308106594187566119389 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_167552_167680 :
    (∑ n ∈ Ico 167552 167680, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 167552 167680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 167552 167680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-357885 : ℤ) ∧
    (∑ n ∈ Ico 167552 167680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7157840079484078263840868732 : ℤ) := by
  rcases cdemPrefixStats_167552_167616 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_167616_167680 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 167552 ≤ 167616) (by norm_num : 167616 ≤ 167680), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 167552 ≤ 167616) (by norm_num : 167616 ≤ 167680), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 167552 ≤ 167616) (by norm_num : 167616 ≤ 167680), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 167552 ≤ 167616) (by norm_num : 167616 ≤ 167680), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_167424_167680 :
    (∑ n ∈ Ico 167424 167680, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 167424 167680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 167424 167680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-328089 : ℤ) ∧
    (∑ n ∈ Ico 167424 167680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6561905343015366372445221490 : ℤ) := by
  rcases cdemPrefixStats_167424_167552 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_167552_167680 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 167424 ≤ 167552) (by norm_num : 167552 ≤ 167680), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 167424 ≤ 167552) (by norm_num : 167552 ≤ 167680), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 167424 ≤ 167552) (by norm_num : 167552 ≤ 167680), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 167424 ≤ 167552) (by norm_num : 167552 ≤ 167680), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_167680_167744 :
    (∑ n ∈ Ico 167680 167744, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 167680 167744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 167680 167744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (178901 : ℤ) ∧
    (∑ n ∈ Ico 167680 167744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3578151744814046439422524273 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_167744_167808 :
    (∑ n ∈ Ico 167744 167808, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 167744 167808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 167744 167808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (89392 : ℤ) ∧
    (∑ n ∈ Ico 167744 167808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1787917322058212936416947912 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_167680_167808 :
    (∑ n ∈ Ico 167680 167808, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 167680 167808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 167680 167808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (268293 : ℤ) ∧
    (∑ n ∈ Ico 167680 167808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5366069066872259375839472185 : ℤ) := by
  rcases cdemPrefixStats_167680_167744 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_167744_167808 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 167680 ≤ 167744) (by norm_num : 167744 ≤ 167808), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 167680 ≤ 167744) (by norm_num : 167744 ≤ 167808), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 167680 ≤ 167744) (by norm_num : 167744 ≤ 167808), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 167680 ≤ 167744) (by norm_num : 167744 ≤ 167808), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_167808_167872 :
    (∑ n ∈ Ico 167808 167872, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 167808 167872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 167808 167872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (446879 : ℤ) ∧
    (∑ n ∈ Ico 167808 167872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8937725487061400990230542450 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_167872_167936 :
    (∑ n ∈ Ico 167872 167936, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 167872 167936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 167872 167936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (29742 : ℤ) ∧
    (∑ n ∈ Ico 167872 167936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (594847781938807774155348239 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_167808_167936 :
    (∑ n ∈ Ico 167808 167936, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 167808 167936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 167808 167936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (476621 : ℤ) ∧
    (∑ n ∈ Ico 167808 167936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9532573269000208764385890689 : ℤ) := by
  rcases cdemPrefixStats_167808_167872 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_167872_167936 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 167808 ≤ 167872) (by norm_num : 167872 ≤ 167936), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 167808 ≤ 167872) (by norm_num : 167872 ≤ 167936), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 167808 ≤ 167872) (by norm_num : 167872 ≤ 167936), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 167808 ≤ 167872) (by norm_num : 167872 ≤ 167936), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_167680_167936 :
    (∑ n ∈ Ico 167680 167936, mobiusTreeValue 16 mobiusTable1200001 n) = (25 : ℤ) ∧
    (∑ n ∈ Ico 167680 167936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 167680 167936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (744914 : ℤ) ∧
    (∑ n ∈ Ico 167680 167936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14898642335872468140225362874 : ℤ) := by
  rcases cdemPrefixStats_167680_167808 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_167808_167936 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 167680 ≤ 167808) (by norm_num : 167808 ≤ 167936), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 167680 ≤ 167808) (by norm_num : 167808 ≤ 167936), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 167680 ≤ 167808) (by norm_num : 167808 ≤ 167936), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 167680 ≤ 167808) (by norm_num : 167808 ≤ 167936), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_167424_167936 :
    (∑ n ∈ Ico 167424 167936, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 167424 167936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 167424 167936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (416825 : ℤ) ∧
    (∑ n ∈ Ico 167424 167936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8336736992857101767780141384 : ℤ) := by
  rcases cdemPrefixStats_167424_167680 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_167680_167936 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 167424 ≤ 167680) (by norm_num : 167680 ≤ 167936), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 167424 ≤ 167680) (by norm_num : 167680 ≤ 167936), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 167424 ≤ 167680) (by norm_num : 167680 ≤ 167936), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 167424 ≤ 167680) (by norm_num : 167680 ≤ 167936), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_166912_167936 :
    (∑ n ∈ Ico 166912 167936, mobiusTreeValue 16 mobiusTable1200001 n) = (18 : ℤ) ∧
    (∑ n ∈ Ico 166912 167936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (622 : ℕ) ∧
    (∑ n ∈ Ico 166912 167936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (536318 : ℤ) ∧
    (∑ n ∈ Ico 166912 167936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10726426131710247374090487985 : ℤ) := by
  rcases cdemPrefixStats_166912_167424 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_167424_167936 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 166912 ≤ 167424) (by norm_num : 167424 ≤ 167936), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 166912 ≤ 167424) (by norm_num : 167424 ≤ 167936), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 166912 ≤ 167424) (by norm_num : 167424 ≤ 167936), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 166912 ≤ 167424) (by norm_num : 167424 ≤ 167936), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_165888_167936 :
    (∑ n ∈ Ico 165888 167936, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 165888 167936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1244 : ℕ) ∧
    (∑ n ∈ Ico 165888 167936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (236139 : ℤ) ∧
    (∑ n ∈ Ico 165888 167936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4722854349638099608026707273 : ℤ) := by
  rcases cdemPrefixStats_165888_166912 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_166912_167936 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 165888 ≤ 166912) (by norm_num : 166912 ≤ 167936), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 165888 ≤ 166912) (by norm_num : 166912 ≤ 167936), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 165888 ≤ 166912) (by norm_num : 166912 ≤ 167936), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 165888 ≤ 166912) (by norm_num : 166912 ≤ 167936), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_163840_167936 :
    (∑ n ∈ Ico 163840 167936, mobiusTreeValue 16 mobiusTable1200001 n) = (46 : ℤ) ∧
    (∑ n ∈ Ico 163840 167936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2492 : ℕ) ∧
    (∑ n ∈ Ico 163840 167936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1390733 : ℤ) ∧
    (∑ n ∈ Ico 163840 167936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (27814957145438392547713550359 : ℤ) := by
  rcases cdemPrefixStats_163840_165888 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_165888_167936 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 163840 ≤ 165888) (by norm_num : 165888 ≤ 167936), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 163840 ≤ 165888) (by norm_num : 165888 ≤ 167936), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 163840 ≤ 165888) (by norm_num : 165888 ≤ 167936), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 163840 ≤ 165888) (by norm_num : 165888 ≤ 167936), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup040_checked_complete :
    (∑ n ∈ Ico 163840 167936, mobiusTreeValue 16 mobiusTable1200001 n) = (46 : ℤ) ∧
    (∑ n ∈ Ico 163840 167936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2492 : ℕ) ∧
    (∑ n ∈ Ico 163840 167936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1390733 : ℤ) ∧
    (∑ n ∈ Ico 163840 167936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (27814957145438392547713550359 : ℤ) := cdemPrefixStats_163840_167936
end Helfgott
#print axioms Helfgott.cdemPrefixGroup040_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 163840 167936, mobiusTreeValue 16 mobiusTable1200001 n) = (46 : ℤ) ∧
    (∑ n ∈ Ico 163840 167936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2492 : ℕ) ∧
    (∑ n ∈ Ico 163840 167936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1390733 : ℤ) ∧
    (∑ n ∈ Ico 163840 167936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (27814957145438392547713550359 : ℤ) := Helfgott.cdemPrefixGroup040_checked_complete
#print axioms solution
