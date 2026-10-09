-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup000_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:10:53.018497+00:00
-- url     : https://prove2.me/submissions/09ffcfe3-b75d-4752-a90d-6b53750009e3

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
private theorem cdemPrefixStats_0_64 :
    (∑ n ∈ Ico 0 64, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 0 64, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 0 64, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (79916222 : ℤ) ∧
    (∑ n ∈ Ico 0 64, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1598324411119615954313326897870 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_64_128 :
    (∑ n ∈ Ico 64 128, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 64 128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 64 128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-82761623 : ℤ) ∧
    (∑ n ∈ Ico 64 128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1655232446730665195299972330239 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_0_128 :
    (∑ n ∈ Ico 0 128, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 0 128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 0 128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2845401 : ℤ) ∧
    (∑ n ∈ Ico 0 128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-56908035611049240986645432369 : ℤ) := by
  rcases cdemPrefixStats_0_64 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_64_128 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 0 ≤ 64) (by norm_num : 64 ≤ 128), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 0 ≤ 64) (by norm_num : 64 ≤ 128), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 0 ≤ 64) (by norm_num : 64 ≤ 128), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 0 ≤ 64) (by norm_num : 64 ≤ 128), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_128_192 :
    (∑ n ∈ Ico 128 192, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 128 192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 128 192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-74699509 : ℤ) ∧
    (∑ n ∈ Ico 128 192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1493990147775162777752748611757 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_192_256 :
    (∑ n ∈ Ico 192 256, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 192 256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 192 256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (100294900 : ℤ) ∧
    (∑ n ∈ Ico 192 256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2005898126609386525945047793055 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_128_256 :
    (∑ n ∈ Ico 128 256, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 128 256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 128 256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (25595391 : ℤ) ∧
    (∑ n ∈ Ico 128 256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (511907978834223748192299181298 : ℤ) := by
  rcases cdemPrefixStats_128_192 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_192_256 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 128 ≤ 192) (by norm_num : 192 ≤ 256), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 128 ≤ 192) (by norm_num : 192 ≤ 256), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 128 ≤ 192) (by norm_num : 192 ≤ 256), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 128 ≤ 192) (by norm_num : 192 ≤ 256), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_0_256 :
    (∑ n ∈ Ico 0 256, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 0 256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 0 256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (22749990 : ℤ) ∧
    (∑ n ∈ Ico 0 256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (454999943223174507205653748929 : ℤ) := by
  rcases cdemPrefixStats_0_128 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_128_256 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 0 ≤ 128) (by norm_num : 128 ≤ 256), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 0 ≤ 128) (by norm_num : 128 ≤ 256), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 0 ≤ 128) (by norm_num : 128 ≤ 256), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 0 ≤ 128) (by norm_num : 128 ≤ 256), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_256_320 :
    (∑ n ∈ Ico 256 320, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 256 320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 256 320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-57422000 : ℤ) ∧
    (∑ n ∈ Ico 256 320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1148440060236831137889968831798 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_320_384 :
    (∑ n ∈ Ico 320 384, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 320 384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 320 384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (35564538 : ℤ) ∧
    (∑ n ∈ Ico 320 384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (711290764143063255722132848021 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_256_384 :
    (∑ n ∈ Ico 256 384, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 256 384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 256 384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-21857462 : ℤ) ∧
    (∑ n ∈ Ico 256 384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-437149296093767882167835983777 : ℤ) := by
  rcases cdemPrefixStats_256_320 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_320_384 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 256 ≤ 320) (by norm_num : 320 ≤ 384), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 256 ≤ 320) (by norm_num : 320 ≤ 384), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 256 ≤ 320) (by norm_num : 320 ≤ 384), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 256 ≤ 320) (by norm_num : 320 ≤ 384), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_384_448 :
    (∑ n ∈ Ico 384 448, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 384 448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 384 448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-44136648 : ℤ) ∧
    (∑ n ∈ Ico 384 448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-882733024947354625643867091622 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_448_512 :
    (∑ n ∈ Ico 448 512, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 448 512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 448 512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (20424717 : ℤ) ∧
    (∑ n ∈ Ico 448 512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (408494387909175463945769909052 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_384_512 :
    (∑ n ∈ Ico 384 512, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 384 512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (82 : ℕ) ∧
    (∑ n ∈ Ico 384 512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-23711931 : ℤ) ∧
    (∑ n ∈ Ico 384 512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-474238637038179161698097182570 : ℤ) := by
  rcases cdemPrefixStats_384_448 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_448_512 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 384 ≤ 448) (by norm_num : 448 ≤ 512), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 384 ≤ 448) (by norm_num : 448 ≤ 512), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 384 ≤ 448) (by norm_num : 448 ≤ 512), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 384 ≤ 448) (by norm_num : 448 ≤ 512), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_256_512 :
    (∑ n ∈ Ico 256 512, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 256 512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 256 512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-45569393 : ℤ) ∧
    (∑ n ∈ Ico 256 512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-911387933131947043865933166347 : ℤ) := by
  rcases cdemPrefixStats_256_384 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_384_512 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 256 ≤ 384) (by norm_num : 384 ≤ 512), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 256 ≤ 384) (by norm_num : 384 ≤ 512), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 256 ≤ 384) (by norm_num : 384 ≤ 512), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 256 ≤ 384) (by norm_num : 384 ≤ 512), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_0_512 :
    (∑ n ∈ Ico 0 512, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 0 512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (314 : ℕ) ∧
    (∑ n ∈ Ico 0 512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-22819403 : ℤ) ∧
    (∑ n ∈ Ico 0 512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-456387989908772536660279417418 : ℤ) := by
  rcases cdemPrefixStats_0_256 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_256_512 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 0 ≤ 256) (by norm_num : 256 ≤ 512), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 0 ≤ 256) (by norm_num : 256 ≤ 512), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 0 ≤ 256) (by norm_num : 256 ≤ 512), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 0 ≤ 256) (by norm_num : 256 ≤ 512), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_512_576 :
    (∑ n ∈ Ico 512 576, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 512 576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 512 576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (83971316 : ℤ) ∧
    (∑ n ∈ Ico 512 576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1679426378213447825794902860923 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_576_640 :
    (∑ n ∈ Ico 576 640, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 576 640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 576 640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-49945423 : ℤ) ∧
    (∑ n ∈ Ico 576 640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-998908517071203200644863210595 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_512_640 :
    (∑ n ∈ Ico 512 640, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 512 640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 512 640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (34025893 : ℤ) ∧
    (∑ n ∈ Ico 512 640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (680517861142244625150039650328 : ℤ) := by
  rcases cdemPrefixStats_512_576 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_576_640 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 512 ≤ 576) (by norm_num : 576 ≤ 640), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 512 ≤ 576) (by norm_num : 576 ≤ 640), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 512 ≤ 576) (by norm_num : 576 ≤ 640), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 512 ≤ 576) (by norm_num : 576 ≤ 640), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_640_704 :
    (∑ n ∈ Ico 640 704, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 640 704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 640 704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-26532165 : ℤ) ∧
    (∑ n ∈ Ico 640 704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-530643304699253879783926698582 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_704_768 :
    (∑ n ∈ Ico 704 768, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 704 768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 704 768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (13664167 : ℤ) ∧
    (∑ n ∈ Ico 704 768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (273283361089828659885920682307 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_640_768 :
    (∑ n ∈ Ico 640 768, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 640 768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 640 768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-12867998 : ℤ) ∧
    (∑ n ∈ Ico 640 768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-257359943609425219898006016275 : ℤ) := by
  rcases cdemPrefixStats_640_704 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_704_768 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 640 ≤ 704) (by norm_num : 704 ≤ 768), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 640 ≤ 704) (by norm_num : 704 ≤ 768), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 640 ≤ 704) (by norm_num : 704 ≤ 768), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 640 ≤ 704) (by norm_num : 704 ≤ 768), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_512_768 :
    (∑ n ∈ Ico 512 768, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 512 768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 512 768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (21157895 : ℤ) ∧
    (∑ n ∈ Ico 512 768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (423157917532819405252033634053 : ℤ) := by
  rcases cdemPrefixStats_512_640 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_640_768 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 512 ≤ 640) (by norm_num : 640 ≤ 768), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 512 ≤ 640) (by norm_num : 640 ≤ 768), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 512 ≤ 640) (by norm_num : 640 ≤ 768), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 512 ≤ 640) (by norm_num : 640 ≤ 768), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_768_832 :
    (∑ n ∈ Ico 768 832, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 768 832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 768 832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-5140793 : ℤ) ∧
    (∑ n ∈ Ico 768 832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-102815879376708239990682155673 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_832_896 :
    (∑ n ∈ Ico 832 896, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 832 896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (35 : ℕ) ∧
    (∑ n ∈ Ico 832 896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (17663943 : ℤ) ∧
    (∑ n ∈ Ico 832 896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (353278836190433281695867497165 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_768_896 :
    (∑ n ∈ Ico 768 896, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 768 896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 768 896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (12523150 : ℤ) ∧
    (∑ n ∈ Ico 768 896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (250462956813725041705185341492 : ℤ) := by
  rcases cdemPrefixStats_768_832 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_832_896 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 768 ≤ 832) (by norm_num : 832 ≤ 896), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 768 ≤ 832) (by norm_num : 832 ≤ 896), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 768 ≤ 832) (by norm_num : 832 ≤ 896), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 768 ≤ 832) (by norm_num : 832 ≤ 896), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_896_960 :
    (∑ n ∈ Ico 896 960, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 896 960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 896 960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (21543307 : ℤ) ∧
    (∑ n ∈ Ico 896 960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (430866211305364189390966278666 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_960_1024 :
    (∑ n ∈ Ico 960 1024, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 960 1024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 960 1024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-39879817 : ℤ) ∧
    (∑ n ∈ Ico 960 1024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-797596435953302361274698485738 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_896_1024 :
    (∑ n ∈ Ico 896 1024, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 896 1024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 896 1024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-18336510 : ℤ) ∧
    (∑ n ∈ Ico 896 1024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-366730224647938171883732207072 : ℤ) := by
  rcases cdemPrefixStats_896_960 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_960_1024 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 896 ≤ 960) (by norm_num : 960 ≤ 1024), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 896 ≤ 960) (by norm_num : 960 ≤ 1024), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 896 ≤ 960) (by norm_num : 960 ≤ 1024), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 896 ≤ 960) (by norm_num : 960 ≤ 1024), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_768_1024 :
    (∑ n ∈ Ico 768 1024, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 768 1024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 768 1024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-5813360 : ℤ) ∧
    (∑ n ∈ Ico 768 1024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-116267267834213130178546865580 : ℤ) := by
  rcases cdemPrefixStats_768_896 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_896_1024 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 768 ≤ 896) (by norm_num : 896 ≤ 1024), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 768 ≤ 896) (by norm_num : 896 ≤ 1024), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 768 ≤ 896) (by norm_num : 896 ≤ 1024), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 768 ≤ 896) (by norm_num : 896 ≤ 1024), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_512_1024 :
    (∑ n ∈ Ico 512 1024, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 512 1024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 512 1024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (15344535 : ℤ) ∧
    (∑ n ∈ Ico 512 1024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (306890649698606275073486768473 : ℤ) := by
  rcases cdemPrefixStats_512_768 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_768_1024 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 512 ≤ 768) (by norm_num : 768 ≤ 1024), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 512 ≤ 768) (by norm_num : 768 ≤ 1024), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 512 ≤ 768) (by norm_num : 768 ≤ 1024), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 512 ≤ 768) (by norm_num : 768 ≤ 1024), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_0_1024 :
    (∑ n ∈ Ico 0 1024, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 0 1024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (624 : ℕ) ∧
    (∑ n ∈ Ico 0 1024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-7474868 : ℤ) ∧
    (∑ n ∈ Ico 0 1024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-149497340210166261586792648945 : ℤ) := by
  rcases cdemPrefixStats_0_512 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_512_1024 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 0 ≤ 512) (by norm_num : 512 ≤ 1024), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 0 ≤ 512) (by norm_num : 512 ≤ 1024), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 0 ≤ 512) (by norm_num : 512 ≤ 1024), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 0 ≤ 512) (by norm_num : 512 ≤ 1024), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_1024_1088 :
    (∑ n ∈ Ico 1024 1088, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 1024 1088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 1024 1088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-18979707 : ℤ) ∧
    (∑ n ∈ Ico 1024 1088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-379594185744735791130729688695 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_1088_1152 :
    (∑ n ∈ Ico 1088 1152, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 1088 1152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 1088 1152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (7933718 : ℤ) ∧
    (∑ n ∈ Ico 1088 1152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (158674335482421807286975881275 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_1024_1152 :
    (∑ n ∈ Ico 1024 1152, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 1024 1152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 1024 1152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-11045989 : ℤ) ∧
    (∑ n ∈ Ico 1024 1152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-220919850262313983843753807420 : ℤ) := by
  rcases cdemPrefixStats_1024_1088 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_1088_1152 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 1024 ≤ 1088) (by norm_num : 1088 ≤ 1152), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 1024 ≤ 1088) (by norm_num : 1088 ≤ 1152), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 1024 ≤ 1088) (by norm_num : 1088 ≤ 1152), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 1024 ≤ 1088) (by norm_num : 1088 ≤ 1152), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_1152_1216 :
    (∑ n ∈ Ico 1152 1216, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 1152 1216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 1152 1216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (20845322 : ℤ) ∧
    (∑ n ∈ Ico 1152 1216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (416906503897427865071911239142 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_1216_1280 :
    (∑ n ∈ Ico 1216 1280, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 1216 1280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 1216 1280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3928772 : ℤ) ∧
    (∑ n ∈ Ico 1216 1280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (78575491733101390034672737932 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_1152_1280 :
    (∑ n ∈ Ico 1152 1280, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 1152 1280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 1152 1280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (24774094 : ℤ) ∧
    (∑ n ∈ Ico 1152 1280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (495481995630529255106583977074 : ℤ) := by
  rcases cdemPrefixStats_1152_1216 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_1216_1280 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 1152 ≤ 1216) (by norm_num : 1216 ≤ 1280), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 1152 ≤ 1216) (by norm_num : 1216 ≤ 1280), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 1152 ≤ 1216) (by norm_num : 1216 ≤ 1280), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 1152 ≤ 1216) (by norm_num : 1216 ≤ 1280), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_1024_1280 :
    (∑ n ∈ Ico 1024 1280, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 1024 1280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 1024 1280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (13728105 : ℤ) ∧
    (∑ n ∈ Ico 1024 1280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (274562145368215271262830169654 : ℤ) := by
  rcases cdemPrefixStats_1024_1152 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_1152_1280 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 1024 ≤ 1152) (by norm_num : 1152 ≤ 1280), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 1024 ≤ 1152) (by norm_num : 1152 ≤ 1280), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 1024 ≤ 1152) (by norm_num : 1152 ≤ 1280), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 1024 ≤ 1152) (by norm_num : 1152 ≤ 1280), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_1280_1344 :
    (∑ n ∈ Ico 1280 1344, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 1280 1344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 1280 1344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3650165 : ℤ) ∧
    (∑ n ∈ Ico 1280 1344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (73003286193456653463154858461 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_1344_1408 :
    (∑ n ∈ Ico 1344 1408, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 1344 1408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 1344 1408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (32948694 : ℤ) ∧
    (∑ n ∈ Ico 1344 1408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (658973949199966506560792386431 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_1280_1408 :
    (∑ n ∈ Ico 1280 1408, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 1280 1408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (82 : ℕ) ∧
    (∑ n ∈ Ico 1280 1408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (36598859 : ℤ) ∧
    (∑ n ∈ Ico 1280 1408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (731977235393423160023947244892 : ℤ) := by
  rcases cdemPrefixStats_1280_1344 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_1344_1408 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 1280 ≤ 1344) (by norm_num : 1344 ≤ 1408), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 1280 ≤ 1344) (by norm_num : 1344 ≤ 1408), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 1280 ≤ 1344) (by norm_num : 1344 ≤ 1408), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 1280 ≤ 1344) (by norm_num : 1344 ≤ 1408), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_1408_1472 :
    (∑ n ∈ Ico 1408 1472, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 1408 1472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 1408 1472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-24277925 : ℤ) ∧
    (∑ n ∈ Ico 1408 1472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-485558538593554886600506336192 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_1472_1536 :
    (∑ n ∈ Ico 1472 1536, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 1472 1536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 1472 1536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-13409704 : ℤ) ∧
    (∑ n ∈ Ico 1472 1536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-268194079410453217675992379581 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_1408_1536 :
    (∑ n ∈ Ico 1408 1536, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 1408 1536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 1408 1536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-37687629 : ℤ) ∧
    (∑ n ∈ Ico 1408 1536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-753752618004008104276498715773 : ℤ) := by
  rcases cdemPrefixStats_1408_1472 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_1472_1536 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 1408 ≤ 1472) (by norm_num : 1472 ≤ 1536), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 1408 ≤ 1472) (by norm_num : 1472 ≤ 1536), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 1408 ≤ 1472) (by norm_num : 1472 ≤ 1536), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 1408 ≤ 1472) (by norm_num : 1472 ≤ 1536), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_1280_1536 :
    (∑ n ∈ Ico 1280 1536, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 1280 1536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (159 : ℕ) ∧
    (∑ n ∈ Ico 1280 1536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1088770 : ℤ) ∧
    (∑ n ∈ Ico 1280 1536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-21775382610584944252551470881 : ℤ) := by
  rcases cdemPrefixStats_1280_1408 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_1408_1536 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 1280 ≤ 1408) (by norm_num : 1408 ≤ 1536), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 1280 ≤ 1408) (by norm_num : 1408 ≤ 1536), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 1280 ≤ 1408) (by norm_num : 1408 ≤ 1536), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 1280 ≤ 1408) (by norm_num : 1408 ≤ 1536), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_1024_1536 :
    (∑ n ∈ Ico 1024 1536, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 1024 1536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 1024 1536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (12639335 : ℤ) ∧
    (∑ n ∈ Ico 1024 1536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (252786762757630327010278698773 : ℤ) := by
  rcases cdemPrefixStats_1024_1280 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_1280_1536 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 1024 ≤ 1280) (by norm_num : 1280 ≤ 1536), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 1024 ≤ 1280) (by norm_num : 1280 ≤ 1536), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 1024 ≤ 1280) (by norm_num : 1280 ≤ 1536), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 1024 ≤ 1280) (by norm_num : 1280 ≤ 1536), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_1536_1600 :
    (∑ n ∈ Ico 1536 1600, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 1536 1600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 1536 1600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-19017073 : ℤ) ∧
    (∑ n ∈ Ico 1536 1600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-380341529878699962991401903795 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_1600_1664 :
    (∑ n ∈ Ico 1600 1664, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 1600 1664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 1600 1664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-12575976 : ℤ) ∧
    (∑ n ∈ Ico 1600 1664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-251519548790201631556769340687 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_1536_1664 :
    (∑ n ∈ Ico 1536 1664, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 1536 1664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 1536 1664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-31593049 : ℤ) ∧
    (∑ n ∈ Ico 1536 1664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-631861078668901594548171244482 : ℤ) := by
  rcases cdemPrefixStats_1536_1600 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_1600_1664 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 1536 ≤ 1600) (by norm_num : 1600 ≤ 1664), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 1536 ≤ 1600) (by norm_num : 1600 ≤ 1664), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 1536 ≤ 1600) (by norm_num : 1600 ≤ 1664), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 1536 ≤ 1600) (by norm_num : 1600 ≤ 1664), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_1664_1728 :
    (∑ n ∈ Ico 1664 1728, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 1664 1728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (34 : ℕ) ∧
    (∑ n ∈ Ico 1664 1728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (11582619 : ℤ) ∧
    (∑ n ∈ Ico 1664 1728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (231652410209382628359376192858 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_1728_1792 :
    (∑ n ∈ Ico 1728 1792, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 1728 1792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 1728 1792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-8554481 : ℤ) ∧
    (∑ n ∈ Ico 1728 1792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-171089602676503807494341326038 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_1664_1792 :
    (∑ n ∈ Ico 1664 1792, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 1664 1792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (73 : ℕ) ∧
    (∑ n ∈ Ico 1664 1792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3028138 : ℤ) ∧
    (∑ n ∈ Ico 1664 1792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (60562807532878820865034866820 : ℤ) := by
  rcases cdemPrefixStats_1664_1728 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_1728_1792 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 1664 ≤ 1728) (by norm_num : 1728 ≤ 1792), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 1664 ≤ 1728) (by norm_num : 1728 ≤ 1792), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 1664 ≤ 1728) (by norm_num : 1728 ≤ 1792), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 1664 ≤ 1728) (by norm_num : 1728 ≤ 1792), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_1536_1792 :
    (∑ n ∈ Ico 1536 1792, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 1536 1792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 1536 1792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-28564911 : ℤ) ∧
    (∑ n ∈ Ico 1536 1792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-571298271136022773683136377662 : ℤ) := by
  rcases cdemPrefixStats_1536_1664 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_1664_1792 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 1536 ≤ 1664) (by norm_num : 1664 ≤ 1792), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 1536 ≤ 1664) (by norm_num : 1664 ≤ 1792), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 1536 ≤ 1664) (by norm_num : 1664 ≤ 1792), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 1536 ≤ 1664) (by norm_num : 1664 ≤ 1792), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_1792_1856 :
    (∑ n ∈ Ico 1792 1856, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 1792 1856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 1792 1856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (24812406 : ℤ) ∧
    (∑ n ∈ Ico 1792 1856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (496248134053717965485407066734 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_1856_1920 :
    (∑ n ∈ Ico 1856 1920, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 1856 1920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 1856 1920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-8010424 : ℤ) ∧
    (∑ n ∈ Ico 1856 1920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-160208532158066660954526754835 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_1792_1920 :
    (∑ n ∈ Ico 1792 1920, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 1792 1920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 1792 1920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (16801982 : ℤ) ∧
    (∑ n ∈ Ico 1792 1920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (336039601895651304530880311899 : ℤ) := by
  rcases cdemPrefixStats_1792_1856 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_1856_1920 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 1792 ≤ 1856) (by norm_num : 1856 ≤ 1920), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 1792 ≤ 1856) (by norm_num : 1856 ≤ 1920), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 1792 ≤ 1856) (by norm_num : 1856 ≤ 1920), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 1792 ≤ 1856) (by norm_num : 1856 ≤ 1920), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_1920_1984 :
    (∑ n ∈ Ico 1920 1984, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 1920 1984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 1920 1984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (28212585 : ℤ) ∧
    (∑ n ∈ Ico 1920 1984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (564251765111761363270366142598 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_1984_2048 :
    (∑ n ∈ Ico 1984 2048, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 1984 2048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 1984 2048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-242158 : ℤ) ∧
    (∑ n ∈ Ico 1984 2048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4843114356729509214579981457 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_1920_2048 :
    (∑ n ∈ Ico 1920 2048, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 1920 2048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 1920 2048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (27970427 : ℤ) ∧
    (∑ n ∈ Ico 1920 2048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (559408650755031854055786161141 : ℤ) := by
  rcases cdemPrefixStats_1920_1984 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_1984_2048 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 1920 ≤ 1984) (by norm_num : 1984 ≤ 2048), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 1920 ≤ 1984) (by norm_num : 1984 ≤ 2048), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 1920 ≤ 1984) (by norm_num : 1984 ≤ 2048), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 1920 ≤ 1984) (by norm_num : 1984 ≤ 2048), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_1792_2048 :
    (∑ n ∈ Ico 1792 2048, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 1792 2048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 1792 2048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (44772409 : ℤ) ∧
    (∑ n ∈ Ico 1792 2048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (895448252650683158586666473040 : ℤ) := by
  rcases cdemPrefixStats_1792_1920 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_1920_2048 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 1792 ≤ 1920) (by norm_num : 1920 ≤ 2048), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 1792 ≤ 1920) (by norm_num : 1920 ≤ 2048), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 1792 ≤ 1920) (by norm_num : 1920 ≤ 2048), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 1792 ≤ 1920) (by norm_num : 1920 ≤ 2048), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_1536_2048 :
    (∑ n ∈ Ico 1536 2048, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 1536 2048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (308 : ℕ) ∧
    (∑ n ∈ Ico 1536 2048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (16207498 : ℤ) ∧
    (∑ n ∈ Ico 1536 2048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (324149981514660384903530095378 : ℤ) := by
  rcases cdemPrefixStats_1536_1792 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_1792_2048 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 1536 ≤ 1792) (by norm_num : 1792 ≤ 2048), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 1536 ≤ 1792) (by norm_num : 1792 ≤ 2048), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 1536 ≤ 1792) (by norm_num : 1792 ≤ 2048), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 1536 ≤ 1792) (by norm_num : 1792 ≤ 2048), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_1024_2048 :
    (∑ n ∈ Ico 1024 2048, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 1024 2048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (621 : ℕ) ∧
    (∑ n ∈ Ico 1024 2048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (28846833 : ℤ) ∧
    (∑ n ∈ Ico 1024 2048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (576936744272290711913808794151 : ℤ) := by
  rcases cdemPrefixStats_1024_1536 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_1536_2048 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 1024 ≤ 1536) (by norm_num : 1536 ≤ 2048), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 1024 ≤ 1536) (by norm_num : 1536 ≤ 2048), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 1024 ≤ 1536) (by norm_num : 1536 ≤ 2048), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 1024 ≤ 1536) (by norm_num : 1536 ≤ 2048), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_0_2048 :
    (∑ n ∈ Ico 0 2048, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 0 2048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1245 : ℕ) ∧
    (∑ n ∈ Ico 0 2048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (21371965 : ℤ) ∧
    (∑ n ∈ Ico 0 2048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (427439404062124450327016145206 : ℤ) := by
  rcases cdemPrefixStats_0_1024 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_1024_2048 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 0 ≤ 1024) (by norm_num : 1024 ≤ 2048), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 0 ≤ 1024) (by norm_num : 1024 ≤ 2048), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 0 ≤ 1024) (by norm_num : 1024 ≤ 2048), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 0 ≤ 1024) (by norm_num : 1024 ≤ 2048), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_2048_2112 :
    (∑ n ∈ Ico 2048 2112, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 2048 2112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 2048 2112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-14377384 : ℤ) ∧
    (∑ n ∈ Ico 2048 2112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-287547739935154366706156889906 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_2112_2176 :
    (∑ n ∈ Ico 2112 2176, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 2112 2176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 2112 2176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2183329 : ℤ) ∧
    (∑ n ∈ Ico 2112 2176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (43666592037374264620491404016 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_2048_2176 :
    (∑ n ∈ Ico 2048 2176, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 2048 2176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 2048 2176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-12194055 : ℤ) ∧
    (∑ n ∈ Ico 2048 2176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-243881147897780102085665485890 : ℤ) := by
  rcases cdemPrefixStats_2048_2112 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_2112_2176 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 2048 ≤ 2112) (by norm_num : 2112 ≤ 2176), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 2048 ≤ 2112) (by norm_num : 2112 ≤ 2176), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 2048 ≤ 2112) (by norm_num : 2112 ≤ 2176), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 2048 ≤ 2112) (by norm_num : 2112 ≤ 2176), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_2176_2240 :
    (∑ n ∈ Ico 2176 2240, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 2176 2240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 2176 2240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (13786383 : ℤ) ∧
    (∑ n ∈ Ico 2176 2240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (275727757746966903125289781572 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_2240_2304 :
    (∑ n ∈ Ico 2240 2304, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 2240 2304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 2240 2304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-21902718 : ℤ) ∧
    (∑ n ∈ Ico 2240 2304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-438054434642358052782164983300 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_2176_2304 :
    (∑ n ∈ Ico 2176 2304, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 2176 2304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 2176 2304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-8116335 : ℤ) ∧
    (∑ n ∈ Ico 2176 2304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-162326676895391149656875201728 : ℤ) := by
  rcases cdemPrefixStats_2176_2240 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_2240_2304 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 2176 ≤ 2240) (by norm_num : 2240 ≤ 2304), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 2176 ≤ 2240) (by norm_num : 2240 ≤ 2304), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 2176 ≤ 2240) (by norm_num : 2240 ≤ 2304), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 2176 ≤ 2240) (by norm_num : 2240 ≤ 2304), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_2048_2304 :
    (∑ n ∈ Ico 2048 2304, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 2048 2304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 2048 2304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-20310390 : ℤ) ∧
    (∑ n ∈ Ico 2048 2304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-406207824793171251742540687618 : ℤ) := by
  rcases cdemPrefixStats_2048_2176 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_2176_2304 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 2048 ≤ 2176) (by norm_num : 2176 ≤ 2304), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 2048 ≤ 2176) (by norm_num : 2176 ≤ 2304), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 2048 ≤ 2176) (by norm_num : 2176 ≤ 2304), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 2048 ≤ 2176) (by norm_num : 2176 ≤ 2304), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_2304_2368 :
    (∑ n ∈ Ico 2304 2368, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 2304 2368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 2304 2368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2067224 : ℤ) ∧
    (∑ n ∈ Ico 2304 2368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-41344487012807437770630985693 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_2368_2432 :
    (∑ n ∈ Ico 2368 2432, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 2368 2432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 2368 2432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-20934411 : ℤ) ∧
    (∑ n ∈ Ico 2368 2432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-418688306426401502854018153193 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_2304_2432 :
    (∑ n ∈ Ico 2304 2432, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 2304 2432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 2304 2432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-23001635 : ℤ) ∧
    (∑ n ∈ Ico 2304 2432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-460032793439208940624649138886 : ℤ) := by
  rcases cdemPrefixStats_2304_2368 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_2368_2432 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 2304 ≤ 2368) (by norm_num : 2368 ≤ 2432), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 2304 ≤ 2368) (by norm_num : 2368 ≤ 2432), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 2304 ≤ 2368) (by norm_num : 2368 ≤ 2432), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 2304 ≤ 2368) (by norm_num : 2368 ≤ 2432), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_2432_2496 :
    (∑ n ∈ Ico 2432 2496, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 2432 2496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 2432 2496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (20252346 : ℤ) ∧
    (∑ n ∈ Ico 2432 2496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (405046933802570809296087932119 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_2496_2560 :
    (∑ n ∈ Ico 2496 2560, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 2496 2560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 2496 2560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3845155 : ℤ) ∧
    (∑ n ∈ Ico 2496 2560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-76903114557481012154159993560 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_2432_2560 :
    (∑ n ∈ Ico 2432 2560, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 2432 2560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 2432 2560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (16407191 : ℤ) ∧
    (∑ n ∈ Ico 2432 2560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (328143819245089797141927938559 : ℤ) := by
  rcases cdemPrefixStats_2432_2496 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_2496_2560 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 2432 ≤ 2496) (by norm_num : 2496 ≤ 2560), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 2432 ≤ 2496) (by norm_num : 2496 ≤ 2560), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 2432 ≤ 2496) (by norm_num : 2496 ≤ 2560), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 2432 ≤ 2496) (by norm_num : 2496 ≤ 2560), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_2304_2560 :
    (∑ n ∈ Ico 2304 2560, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 2304 2560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 2304 2560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-6594444 : ℤ) ∧
    (∑ n ∈ Ico 2304 2560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-131888974194119143482721200327 : ℤ) := by
  rcases cdemPrefixStats_2304_2432 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_2432_2560 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 2304 ≤ 2432) (by norm_num : 2432 ≤ 2560), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 2304 ≤ 2432) (by norm_num : 2432 ≤ 2560), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 2304 ≤ 2432) (by norm_num : 2432 ≤ 2560), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 2304 ≤ 2432) (by norm_num : 2432 ≤ 2560), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_2048_2560 :
    (∑ n ∈ Ico 2048 2560, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 2048 2560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 2048 2560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-26904834 : ℤ) ∧
    (∑ n ∈ Ico 2048 2560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-538096798987290395225261887945 : ℤ) := by
  rcases cdemPrefixStats_2048_2304 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_2304_2560 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 2048 ≤ 2304) (by norm_num : 2304 ≤ 2560), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 2048 ≤ 2304) (by norm_num : 2304 ≤ 2560), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 2048 ≤ 2304) (by norm_num : 2304 ≤ 2560), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 2048 ≤ 2304) (by norm_num : 2304 ≤ 2560), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_2560_2624 :
    (∑ n ∈ Ico 2560 2624, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 2560 2624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 2560 2624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (27100569 : ℤ) ∧
    (∑ n ∈ Ico 2560 2624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (542011560115554600261462105604 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_2624_2688 :
    (∑ n ∈ Ico 2624 2688, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 2624 2688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 2624 2688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-14911296 : ℤ) ∧
    (∑ n ∈ Ico 2624 2688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-298225965213676061144494074860 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_2560_2688 :
    (∑ n ∈ Ico 2560 2688, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 2560 2688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 2560 2688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (12189273 : ℤ) ∧
    (∑ n ∈ Ico 2560 2688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (243785594901878539116968030744 : ℤ) := by
  rcases cdemPrefixStats_2560_2624 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_2624_2688 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 2560 ≤ 2624) (by norm_num : 2624 ≤ 2688), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 2560 ≤ 2624) (by norm_num : 2624 ≤ 2688), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 2560 ≤ 2624) (by norm_num : 2624 ≤ 2688), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 2560 ≤ 2624) (by norm_num : 2624 ≤ 2688), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_2688_2752 :
    (∑ n ∈ Ico 2688 2752, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 2688 2752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 2688 2752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-27689960 : ℤ) ∧
    (∑ n ∈ Ico 2688 2752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-553799362416416983652388355592 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_2752_2816 :
    (∑ n ∈ Ico 2752 2816, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 2752 2816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 2752 2816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-12634277 : ℤ) ∧
    (∑ n ∈ Ico 2752 2816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-252685573559556121619876020773 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_2688_2816 :
    (∑ n ∈ Ico 2688 2816, mobiusTreeValue 16 mobiusTable1200001 n) = (-22 : ℤ) ∧
    (∑ n ∈ Ico 2688 2816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 2688 2816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-40324237 : ℤ) ∧
    (∑ n ∈ Ico 2688 2816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-806484935975973105272264376365 : ℤ) := by
  rcases cdemPrefixStats_2688_2752 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_2752_2816 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 2688 ≤ 2752) (by norm_num : 2752 ≤ 2816), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 2688 ≤ 2752) (by norm_num : 2752 ≤ 2816), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 2688 ≤ 2752) (by norm_num : 2752 ≤ 2816), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 2688 ≤ 2752) (by norm_num : 2752 ≤ 2816), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_2560_2816 :
    (∑ n ∈ Ico 2560 2816, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 2560 2816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 2560 2816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-28134964 : ℤ) ∧
    (∑ n ∈ Ico 2560 2816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-562699341074094566155296345621 : ℤ) := by
  rcases cdemPrefixStats_2560_2688 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_2688_2816 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 2560 ≤ 2688) (by norm_num : 2688 ≤ 2816), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 2560 ≤ 2688) (by norm_num : 2688 ≤ 2816), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 2560 ≤ 2688) (by norm_num : 2688 ≤ 2816), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 2560 ≤ 2688) (by norm_num : 2688 ≤ 2816), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_2816_2880 :
    (∑ n ∈ Ico 2816 2880, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 2816 2880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 2816 2880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1711638 : ℤ) ∧
    (∑ n ∈ Ico 2816 2880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (34232728973466948279063906585 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_2880_2944 :
    (∑ n ∈ Ico 2880 2944, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 2880 2944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 2880 2944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (8595073 : ℤ) ∧
    (∑ n ∈ Ico 2880 2944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (171901443456261186572562004914 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_2816_2944 :
    (∑ n ∈ Ico 2816 2944, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 2816 2944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 2816 2944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (10306711 : ℤ) ∧
    (∑ n ∈ Ico 2816 2944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (206134172429728134851625911499 : ℤ) := by
  rcases cdemPrefixStats_2816_2880 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_2880_2944 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 2816 ≤ 2880) (by norm_num : 2880 ≤ 2944), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 2816 ≤ 2880) (by norm_num : 2880 ≤ 2944), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 2816 ≤ 2880) (by norm_num : 2880 ≤ 2944), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 2816 ≤ 2880) (by norm_num : 2880 ≤ 2944), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_2944_3008 :
    (∑ n ∈ Ico 2944 3008, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 2944 3008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 2944 3008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (16722863 : ℤ) ∧
    (∑ n ∈ Ico 2944 3008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (334457358658453944068966008480 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_3008_3072 :
    (∑ n ∈ Ico 3008 3072, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 3008 3072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 3008 3072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3254175 : ℤ) ∧
    (∑ n ∈ Ico 3008 3072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (65083501935931563644206347685 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_2944_3072 :
    (∑ n ∈ Ico 2944 3072, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 2944 3072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 2944 3072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (19977038 : ℤ) ∧
    (∑ n ∈ Ico 2944 3072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (399540860594385507713172356165 : ℤ) := by
  rcases cdemPrefixStats_2944_3008 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_3008_3072 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 2944 ≤ 3008) (by norm_num : 3008 ≤ 3072), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 2944 ≤ 3008) (by norm_num : 3008 ≤ 3072), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 2944 ≤ 3008) (by norm_num : 3008 ≤ 3072), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 2944 ≤ 3008) (by norm_num : 3008 ≤ 3072), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_2816_3072 :
    (∑ n ∈ Ico 2816 3072, mobiusTreeValue 16 mobiusTable1200001 n) = (18 : ℤ) ∧
    (∑ n ∈ Ico 2816 3072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 2816 3072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (30283749 : ℤ) ∧
    (∑ n ∈ Ico 2816 3072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (605675033024113642564798267664 : ℤ) := by
  rcases cdemPrefixStats_2816_2944 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_2944_3072 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 2816 ≤ 2944) (by norm_num : 2944 ≤ 3072), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 2816 ≤ 2944) (by norm_num : 2944 ≤ 3072), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 2816 ≤ 2944) (by norm_num : 2944 ≤ 3072), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 2816 ≤ 2944) (by norm_num : 2944 ≤ 3072), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_2560_3072 :
    (∑ n ∈ Ico 2560 3072, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 2560 3072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 2560 3072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2148785 : ℤ) ∧
    (∑ n ∈ Ico 2560 3072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (42975691950019076409501922043 : ℤ) := by
  rcases cdemPrefixStats_2560_2816 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_2816_3072 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 2560 ≤ 2816) (by norm_num : 2816 ≤ 3072), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 2560 ≤ 2816) (by norm_num : 2816 ≤ 3072), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 2560 ≤ 2816) (by norm_num : 2816 ≤ 3072), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 2560 ≤ 2816) (by norm_num : 2816 ≤ 3072), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_2048_3072 :
    (∑ n ∈ Ico 2048 3072, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 2048 3072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (624 : ℕ) ∧
    (∑ n ∈ Ico 2048 3072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-24756049 : ℤ) ∧
    (∑ n ∈ Ico 2048 3072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-495121107037271318815759965902 : ℤ) := by
  rcases cdemPrefixStats_2048_2560 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_2560_3072 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 2048 ≤ 2560) (by norm_num : 2560 ≤ 3072), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 2048 ≤ 2560) (by norm_num : 2560 ≤ 3072), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 2048 ≤ 2560) (by norm_num : 2560 ≤ 3072), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 2048 ≤ 2560) (by norm_num : 2560 ≤ 3072), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_3072_3136 :
    (∑ n ∈ Ico 3072 3136, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 3072 3136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 3072 3136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (14503378 : ℤ) ∧
    (∑ n ∈ Ico 3072 3136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (290067658395919568986939481227 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_3136_3200 :
    (∑ n ∈ Ico 3136 3200, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 3136 3200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 3136 3200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (7868760 : ℤ) ∧
    (∑ n ∈ Ico 3136 3200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (157375238614712236924971592394 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_3072_3200 :
    (∑ n ∈ Ico 3072 3200, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 3072 3200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 3072 3200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (22372138 : ℤ) ∧
    (∑ n ∈ Ico 3072 3200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (447442897010631805911911073621 : ℤ) := by
  rcases cdemPrefixStats_3072_3136 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_3136_3200 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 3072 ≤ 3136) (by norm_num : 3136 ≤ 3200), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 3072 ≤ 3136) (by norm_num : 3136 ≤ 3200), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 3072 ≤ 3136) (by norm_num : 3136 ≤ 3200), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 3072 ≤ 3136) (by norm_num : 3136 ≤ 3200), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_3200_3264 :
    (∑ n ∈ Ico 3200 3264, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 3200 3264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 3200 3264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (7750930 : ℤ) ∧
    (∑ n ∈ Ico 3200 3264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (155018621252640851415723683949 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_3264_3328 :
    (∑ n ∈ Ico 3264 3328, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 3264 3328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 3264 3328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (6103844 : ℤ) ∧
    (∑ n ∈ Ico 3264 3328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (122076948212749831755157394363 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_3200_3328 :
    (∑ n ∈ Ico 3200 3328, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 3200 3328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 3200 3328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (13854774 : ℤ) ∧
    (∑ n ∈ Ico 3200 3328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (277095569465390683170881078312 : ℤ) := by
  rcases cdemPrefixStats_3200_3264 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_3264_3328 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 3200 ≤ 3264) (by norm_num : 3264 ≤ 3328), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 3200 ≤ 3264) (by norm_num : 3264 ≤ 3328), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 3200 ≤ 3264) (by norm_num : 3264 ≤ 3328), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 3200 ≤ 3264) (by norm_num : 3264 ≤ 3328), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_3072_3328 :
    (∑ n ∈ Ico 3072 3328, mobiusTreeValue 16 mobiusTable1200001 n) = (23 : ℤ) ∧
    (∑ n ∈ Ico 3072 3328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 3072 3328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (36226912 : ℤ) ∧
    (∑ n ∈ Ico 3072 3328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (724538466476022489082792151933 : ℤ) := by
  rcases cdemPrefixStats_3072_3200 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_3200_3328 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 3072 ≤ 3200) (by norm_num : 3200 ≤ 3328), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 3072 ≤ 3200) (by norm_num : 3200 ≤ 3328), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 3072 ≤ 3200) (by norm_num : 3200 ≤ 3328), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 3072 ≤ 3200) (by norm_num : 3200 ≤ 3328), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_3328_3392 :
    (∑ n ∈ Ico 3328 3392, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 3328 3392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 3328 3392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-8971235 : ℤ) ∧
    (∑ n ∈ Ico 3328 3392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-179424714564014566571894220797 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_3392_3456 :
    (∑ n ∈ Ico 3392 3456, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 3392 3456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 3392 3456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1475367 : ℤ) ∧
    (∑ n ∈ Ico 3392 3456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (29507318503209204310316862963 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_3328_3456 :
    (∑ n ∈ Ico 3328 3456, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 3328 3456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 3328 3456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-7495868 : ℤ) ∧
    (∑ n ∈ Ico 3328 3456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-149917396060805362261577357834 : ℤ) := by
  rcases cdemPrefixStats_3328_3392 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_3392_3456 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 3328 ≤ 3392) (by norm_num : 3392 ≤ 3456), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 3328 ≤ 3392) (by norm_num : 3392 ≤ 3456), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 3328 ≤ 3392) (by norm_num : 3392 ≤ 3456), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 3328 ≤ 3392) (by norm_num : 3392 ≤ 3456), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_3456_3520 :
    (∑ n ∈ Ico 3456 3520, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 3456 3520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 3456 3520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-5766360 : ℤ) ∧
    (∑ n ∈ Ico 3456 3520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-115327233133551046565937452763 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_3520_3584 :
    (∑ n ∈ Ico 3520 3584, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 3520 3584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 3520 3584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-11299238 : ℤ) ∧
    (∑ n ∈ Ico 3520 3584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-225984845085258665132513489743 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_3456_3584 :
    (∑ n ∈ Ico 3456 3584, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 3456 3584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 3456 3584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-17065598 : ℤ) ∧
    (∑ n ∈ Ico 3456 3584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-341312078218809711698450942506 : ℤ) := by
  rcases cdemPrefixStats_3456_3520 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_3520_3584 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 3456 ≤ 3520) (by norm_num : 3520 ≤ 3584), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 3456 ≤ 3520) (by norm_num : 3520 ≤ 3584), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 3456 ≤ 3520) (by norm_num : 3520 ≤ 3584), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 3456 ≤ 3520) (by norm_num : 3520 ≤ 3584), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_3328_3584 :
    (∑ n ∈ Ico 3328 3584, mobiusTreeValue 16 mobiusTable1200001 n) = (-17 : ℤ) ∧
    (∑ n ∈ Ico 3328 3584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 3328 3584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-24561466 : ℤ) ∧
    (∑ n ∈ Ico 3328 3584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-491229474279615073960028300340 : ℤ) := by
  rcases cdemPrefixStats_3328_3456 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_3456_3584 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 3328 ≤ 3456) (by norm_num : 3456 ≤ 3584), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 3328 ≤ 3456) (by norm_num : 3456 ≤ 3584), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 3328 ≤ 3456) (by norm_num : 3456 ≤ 3584), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 3328 ≤ 3456) (by norm_num : 3456 ≤ 3584), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_3072_3584 :
    (∑ n ∈ Ico 3072 3584, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 3072 3584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 3072 3584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (11665446 : ℤ) ∧
    (∑ n ∈ Ico 3072 3584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (233308992196407415122763851593 : ℤ) := by
  rcases cdemPrefixStats_3072_3328 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_3328_3584 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 3072 ≤ 3328) (by norm_num : 3328 ≤ 3584), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 3072 ≤ 3328) (by norm_num : 3328 ≤ 3584), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 3072 ≤ 3328) (by norm_num : 3328 ≤ 3584), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 3072 ≤ 3328) (by norm_num : 3328 ≤ 3584), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_3584_3648 :
    (∑ n ∈ Ico 3584 3648, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 3584 3648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 3584 3648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-12463567 : ℤ) ∧
    (∑ n ∈ Ico 3584 3648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-249271357620256647468058841738 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_3648_3712 :
    (∑ n ∈ Ico 3648 3712, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 3648 3712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 3648 3712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1346267 : ℤ) ∧
    (∑ n ∈ Ico 3648 3712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-26925339585265696368421068115 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_3584_3712 :
    (∑ n ∈ Ico 3584 3712, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 3584 3712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 3584 3712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-13809834 : ℤ) ∧
    (∑ n ∈ Ico 3584 3712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-276196697205522343836479909853 : ℤ) := by
  rcases cdemPrefixStats_3584_3648 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_3648_3712 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 3584 ≤ 3648) (by norm_num : 3648 ≤ 3712), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 3584 ≤ 3648) (by norm_num : 3648 ≤ 3712), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 3584 ≤ 3648) (by norm_num : 3648 ≤ 3712), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 3584 ≤ 3648) (by norm_num : 3648 ≤ 3712), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_3712_3776 :
    (∑ n ∈ Ico 3712 3776, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 3712 3776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (34 : ℕ) ∧
    (∑ n ∈ Ico 3712 3776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-15053 : ℤ) ∧
    (∑ n ∈ Ico 3712 3776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-301008420737668877957020549 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_3776_3840 :
    (∑ n ∈ Ico 3776 3840, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 3776 3840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 3776 3840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3168 : ℤ) ∧
    (∑ n ∈ Ico 3776 3840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (63404091841504778281242747 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_3712_3840 :
    (∑ n ∈ Ico 3712 3840, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 3712 3840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 3712 3840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-11885 : ℤ) ∧
    (∑ n ∈ Ico 3712 3840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-237604328896164099675777802 : ℤ) := by
  rcases cdemPrefixStats_3712_3776 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_3776_3840 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 3712 ≤ 3776) (by norm_num : 3776 ≤ 3840), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 3712 ≤ 3776) (by norm_num : 3776 ≤ 3840), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 3712 ≤ 3776) (by norm_num : 3776 ≤ 3840), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 3712 ≤ 3776) (by norm_num : 3776 ≤ 3840), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_3584_3840 :
    (∑ n ∈ Ico 3584 3840, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 3584 3840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 3584 3840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-13821719 : ℤ) ∧
    (∑ n ∈ Ico 3584 3840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-276434301534418507936155687655 : ℤ) := by
  rcases cdemPrefixStats_3584_3712 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_3712_3840 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 3584 ≤ 3712) (by norm_num : 3712 ≤ 3840), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 3584 ≤ 3712) (by norm_num : 3712 ≤ 3840), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 3584 ≤ 3712) (by norm_num : 3712 ≤ 3840), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 3584 ≤ 3712) (by norm_num : 3712 ≤ 3840), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_3840_3904 :
    (∑ n ∈ Ico 3840 3904, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 3840 3904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 3840 3904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1226507 : ℤ) ∧
    (∑ n ∈ Ico 3840 3904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (24530179692141001222754452319 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_3904_3968 :
    (∑ n ∈ Ico 3904 3968, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 3904 3968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 3904 3968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-11475219 : ℤ) ∧
    (∑ n ∈ Ico 3904 3968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-229504485865928185711584308259 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_3840_3968 :
    (∑ n ∈ Ico 3840 3968, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 3840 3968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 3840 3968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-10248712 : ℤ) ∧
    (∑ n ∈ Ico 3840 3968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-204974306173787184488829855940 : ℤ) := by
  rcases cdemPrefixStats_3840_3904 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_3904_3968 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 3840 ≤ 3904) (by norm_num : 3904 ≤ 3968), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 3840 ≤ 3904) (by norm_num : 3904 ≤ 3968), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 3840 ≤ 3904) (by norm_num : 3904 ≤ 3968), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 3840 ≤ 3904) (by norm_num : 3904 ≤ 3968), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_3968_4032 :
    (∑ n ∈ Ico 3968 4032, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 3968 4032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 3968 4032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1298277 : ℤ) ∧
    (∑ n ∈ Ico 3968 4032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (25965499241222497886752557122 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_4032_4096 :
    (∑ n ∈ Ico 4032 4096, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 4032 4096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 4032 4096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-6094239 : ℤ) ∧
    (∑ n ∈ Ico 4032 4096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-121884849962466414218631730829 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_3968_4096 :
    (∑ n ∈ Ico 3968 4096, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 3968 4096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 3968 4096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4795962 : ℤ) ∧
    (∑ n ∈ Ico 3968 4096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-95919350721243916331879173707 : ℤ) := by
  rcases cdemPrefixStats_3968_4032 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_4032_4096 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 3968 ≤ 4032) (by norm_num : 4032 ≤ 4096), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 3968 ≤ 4032) (by norm_num : 4032 ≤ 4096), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 3968 ≤ 4032) (by norm_num : 4032 ≤ 4096), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 3968 ≤ 4032) (by norm_num : 4032 ≤ 4096), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_3840_4096 :
    (∑ n ∈ Ico 3840 4096, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 3840 4096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 3840 4096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-15044674 : ℤ) ∧
    (∑ n ∈ Ico 3840 4096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-300893656895031100820709029647 : ℤ) := by
  rcases cdemPrefixStats_3840_3968 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_3968_4096 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 3840 ≤ 3968) (by norm_num : 3968 ≤ 4096), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 3840 ≤ 3968) (by norm_num : 3968 ≤ 4096), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 3840 ≤ 3968) (by norm_num : 3968 ≤ 4096), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 3840 ≤ 3968) (by norm_num : 3968 ≤ 4096), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_3584_4096 :
    (∑ n ∈ Ico 3584 4096, mobiusTreeValue 16 mobiusTable1200001 n) = (-22 : ℤ) ∧
    (∑ n ∈ Ico 3584 4096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 3584 4096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-28866393 : ℤ) ∧
    (∑ n ∈ Ico 3584 4096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-577327958429449608756864717302 : ℤ) := by
  rcases cdemPrefixStats_3584_3840 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_3840_4096 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 3584 ≤ 3840) (by norm_num : 3840 ≤ 4096), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 3584 ≤ 3840) (by norm_num : 3840 ≤ 4096), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 3584 ≤ 3840) (by norm_num : 3840 ≤ 4096), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 3584 ≤ 3840) (by norm_num : 3840 ≤ 4096), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_3072_4096 :
    (∑ n ∈ Ico 3072 4096, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 3072 4096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (622 : ℕ) ∧
    (∑ n ∈ Ico 3072 4096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-17200947 : ℤ) ∧
    (∑ n ∈ Ico 3072 4096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-344018966233042193634100865709 : ℤ) := by
  rcases cdemPrefixStats_3072_3584 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_3584_4096 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 3072 ≤ 3584) (by norm_num : 3584 ≤ 4096), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 3072 ≤ 3584) (by norm_num : 3584 ≤ 4096), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 3072 ≤ 3584) (by norm_num : 3584 ≤ 4096), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 3072 ≤ 3584) (by norm_num : 3584 ≤ 4096), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_2048_4096 :
    (∑ n ∈ Ico 2048 4096, mobiusTreeValue 16 mobiusTable1200001 n) = (-26 : ℤ) ∧
    (∑ n ∈ Ico 2048 4096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1246 : ℕ) ∧
    (∑ n ∈ Ico 2048 4096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-41956996 : ℤ) ∧
    (∑ n ∈ Ico 2048 4096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-839140073270313512449860831611 : ℤ) := by
  rcases cdemPrefixStats_2048_3072 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_3072_4096 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 2048 ≤ 3072) (by norm_num : 3072 ≤ 4096), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 2048 ≤ 3072) (by norm_num : 3072 ≤ 4096), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 2048 ≤ 3072) (by norm_num : 3072 ≤ 4096), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 2048 ≤ 3072) (by norm_num : 3072 ≤ 4096), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_0_4096 :
    (∑ n ∈ Ico 0 4096, mobiusTreeValue 16 mobiusTable1200001 n) = (-19 : ℤ) ∧
    (∑ n ∈ Ico 0 4096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2491 : ℕ) ∧
    (∑ n ∈ Ico 0 4096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-20585031 : ℤ) ∧
    (∑ n ∈ Ico 0 4096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-411700669208189062122844686405 : ℤ) := by
  rcases cdemPrefixStats_0_2048 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_2048_4096 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 0 ≤ 2048) (by norm_num : 2048 ≤ 4096), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 0 ≤ 2048) (by norm_num : 2048 ≤ 4096), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 0 ≤ 2048) (by norm_num : 2048 ≤ 4096), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 0 ≤ 2048) (by norm_num : 2048 ≤ 4096), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup000_checked_complete :
    (∑ n ∈ Ico 0 4096, mobiusTreeValue 16 mobiusTable1200001 n) = (-19 : ℤ) ∧
    (∑ n ∈ Ico 0 4096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2491 : ℕ) ∧
    (∑ n ∈ Ico 0 4096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-20585031 : ℤ) ∧
    (∑ n ∈ Ico 0 4096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-411700669208189062122844686405 : ℤ) := cdemPrefixStats_0_4096
end Helfgott
#print axioms Helfgott.cdemPrefixGroup000_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 0 4096, mobiusTreeValue 16 mobiusTable1200001 n) = (-19 : ℤ) ∧
    (∑ n ∈ Ico 0 4096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2491 : ℕ) ∧
    (∑ n ∈ Ico 0 4096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-20585031 : ℤ) ∧
    (∑ n ∈ Ico 0 4096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-411700669208189062122844686405 : ℤ) := Helfgott.cdemPrefixGroup000_checked_complete
#print axioms solution
