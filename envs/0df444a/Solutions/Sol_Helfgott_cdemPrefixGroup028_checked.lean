-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup028_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T02:12:30.489509+00:00
-- url     : https://prove2.me/submissions/ecf39029-4012-4123-a5a7-1de0b1a60f1f

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
private theorem cdemPrefixStats_114688_114752 :
    (∑ n ∈ Ico 114688 114752, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 114688 114752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 114688 114752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (218015 : ℤ) ∧
    (∑ n ∈ Ico 114688 114752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4360375610587927099889695077 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_114752_114816 :
    (∑ n ∈ Ico 114752 114816, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 114752 114816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 114752 114816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-348504 : ℤ) ∧
    (∑ n ∈ Ico 114752 114816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6970166801768565079896360149 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_114688_114816 :
    (∑ n ∈ Ico 114688 114816, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 114688 114816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 114688 114816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-130489 : ℤ) ∧
    (∑ n ∈ Ico 114688 114816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2609791191180637980006665072 : ℤ) := by
  rcases cdemPrefixStats_114688_114752 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_114752_114816 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 114688 ≤ 114752) (by norm_num : 114752 ≤ 114816), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 114688 ≤ 114752) (by norm_num : 114752 ≤ 114816), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 114688 ≤ 114752) (by norm_num : 114752 ≤ 114816), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 114688 ≤ 114752) (by norm_num : 114752 ≤ 114816), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_114816_114880 :
    (∑ n ∈ Ico 114816 114880, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 114816 114880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 114816 114880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-87023 : ℤ) ∧
    (∑ n ∈ Ico 114816 114880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1740499633750698577938181551 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_114880_114944 :
    (∑ n ∈ Ico 114880 114944, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 114880 114944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 114880 114944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (174075 : ℤ) ∧
    (∑ n ∈ Ico 114880 114944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3481530410961258072651270572 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_114816_114944 :
    (∑ n ∈ Ico 114816 114944, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 114816 114944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 114816 114944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (87052 : ℤ) ∧
    (∑ n ∈ Ico 114816 114944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1741030777210559494713089021 : ℤ) := by
  rcases cdemPrefixStats_114816_114880 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_114880_114944 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 114816 ≤ 114880) (by norm_num : 114880 ≤ 114944), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 114816 ≤ 114880) (by norm_num : 114880 ≤ 114944), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 114816 ≤ 114880) (by norm_num : 114880 ≤ 114944), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 114816 ≤ 114880) (by norm_num : 114880 ≤ 114944), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_114688_114944 :
    (∑ n ∈ Ico 114688 114944, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 114688 114944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 114688 114944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-43437 : ℤ) ∧
    (∑ n ∈ Ico 114688 114944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-868760413970078485293576051 : ℤ) := by
  rcases cdemPrefixStats_114688_114816 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_114816_114944 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 114688 ≤ 114816) (by norm_num : 114816 ≤ 114944), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 114688 ≤ 114816) (by norm_num : 114816 ≤ 114944), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 114688 ≤ 114816) (by norm_num : 114816 ≤ 114944), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 114688 ≤ 114816) (by norm_num : 114816 ≤ 114944), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_114944_115008 :
    (∑ n ∈ Ico 114944 115008, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 114944 115008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 114944 115008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (260916 : ℤ) ∧
    (∑ n ∈ Ico 114944 115008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5218359461886277296325857033 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_115008_115072 :
    (∑ n ∈ Ico 115008 115072, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 115008 115072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 115008 115072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (43427 : ℤ) ∧
    (∑ n ∈ Ico 115008 115072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (868567647447446625037138312 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_114944_115072 :
    (∑ n ∈ Ico 114944 115072, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 114944 115072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 114944 115072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (304343 : ℤ) ∧
    (∑ n ∈ Ico 114944 115072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6086927109333723921362995345 : ℤ) := by
  rcases cdemPrefixStats_114944_115008 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_115008_115072 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 114944 ≤ 115008) (by norm_num : 115008 ≤ 115072), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 114944 ≤ 115008) (by norm_num : 115008 ≤ 115072), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 114944 ≤ 115008) (by norm_num : 115008 ≤ 115072), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 114944 ≤ 115008) (by norm_num : 115008 ≤ 115072), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_115072_115136 :
    (∑ n ∈ Ico 115072 115136, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 115072 115136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 115072 115136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-67 : ℤ) ∧
    (∑ n ∈ Ico 115072 115136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1343571864214143792821613 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_115136_115200 :
    (∑ n ∈ Ico 115136 115200, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 115136 115200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 115136 115200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (130179 : ℤ) ∧
    (∑ n ∈ Ico 115136 115200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2603669029464501893398338313 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_115072_115200 :
    (∑ n ∈ Ico 115072 115200, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 115072 115200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 115072 115200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (130112 : ℤ) ∧
    (∑ n ∈ Ico 115072 115200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2602325457600287749605516700 : ℤ) := by
  rcases cdemPrefixStats_115072_115136 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_115136_115200 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 115072 ≤ 115136) (by norm_num : 115136 ≤ 115200), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 115072 ≤ 115136) (by norm_num : 115136 ≤ 115200), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 115072 ≤ 115136) (by norm_num : 115136 ≤ 115200), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 115072 ≤ 115136) (by norm_num : 115136 ≤ 115200), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_114944_115200 :
    (∑ n ∈ Ico 114944 115200, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 114944 115200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 114944 115200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (434455 : ℤ) ∧
    (∑ n ∈ Ico 114944 115200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8689252566934011670968512045 : ℤ) := by
  rcases cdemPrefixStats_114944_115072 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_115072_115200 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 114944 ≤ 115072) (by norm_num : 115072 ≤ 115200), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 114944 ≤ 115072) (by norm_num : 115072 ≤ 115200), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 114944 ≤ 115072) (by norm_num : 115072 ≤ 115200), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 114944 ≤ 115072) (by norm_num : 115072 ≤ 115200), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_114688_115200 :
    (∑ n ∈ Ico 114688 115200, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 114688 115200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 114688 115200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (391018 : ℤ) ∧
    (∑ n ∈ Ico 114688 115200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7820492152963933185674935994 : ℤ) := by
  rcases cdemPrefixStats_114688_114944 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_114944_115200 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 114688 ≤ 114944) (by norm_num : 114944 ≤ 115200), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 114688 ≤ 114944) (by norm_num : 114944 ≤ 115200), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 114688 ≤ 114944) (by norm_num : 114944 ≤ 115200), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 114688 ≤ 114944) (by norm_num : 114944 ≤ 115200), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_115200_115264 :
    (∑ n ∈ Ico 115200 115264, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 115200 115264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 115200 115264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-607462 : ℤ) ∧
    (∑ n ∈ Ico 115200 115264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12149418173367273278040199509 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_115264_115328 :
    (∑ n ∈ Ico 115264 115328, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 115264 115328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 115264 115328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-43292 : ℤ) ∧
    (∑ n ∈ Ico 115264 115328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-865828299361636371456596662 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_115200_115328 :
    (∑ n ∈ Ico 115200 115328, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 115200 115328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 115200 115328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-650754 : ℤ) ∧
    (∑ n ∈ Ico 115200 115328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13015246472728909649496796171 : ℤ) := by
  rcases cdemPrefixStats_115200_115264 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_115264_115328 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 115200 ≤ 115264) (by norm_num : 115264 ≤ 115328), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 115200 ≤ 115264) (by norm_num : 115264 ≤ 115328), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 115200 ≤ 115264) (by norm_num : 115264 ≤ 115328), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 115200 ≤ 115264) (by norm_num : 115264 ≤ 115328), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_115328_115392 :
    (∑ n ∈ Ico 115328 115392, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 115328 115392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 115328 115392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (43346 : ℤ) ∧
    (∑ n ∈ Ico 115328 115392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (866956718579142032619675800 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_115392_115456 :
    (∑ n ∈ Ico 115392 115456, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 115392 115456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 115392 115456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (433197 : ℤ) ∧
    (∑ n ∈ Ico 115392 115456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8664002552194800653929114137 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_115328_115456 :
    (∑ n ∈ Ico 115328 115456, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 115328 115456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 115328 115456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (476543 : ℤ) ∧
    (∑ n ∈ Ico 115328 115456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9530959270773942686548789937 : ℤ) := by
  rcases cdemPrefixStats_115328_115392 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_115392_115456 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 115328 ≤ 115392) (by norm_num : 115392 ≤ 115456), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 115328 ≤ 115392) (by norm_num : 115392 ≤ 115456), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 115328 ≤ 115392) (by norm_num : 115392 ≤ 115456), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 115328 ≤ 115392) (by norm_num : 115392 ≤ 115456), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_115200_115456 :
    (∑ n ∈ Ico 115200 115456, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 115200 115456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 115200 115456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-174211 : ℤ) ∧
    (∑ n ∈ Ico 115200 115456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3484287201954966962948006234 : ℤ) := by
  rcases cdemPrefixStats_115200_115328 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_115328_115456 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 115200 ≤ 115328) (by norm_num : 115328 ≤ 115456), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 115200 ≤ 115328) (by norm_num : 115328 ≤ 115456), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 115200 ≤ 115328) (by norm_num : 115328 ≤ 115456), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 115200 ≤ 115328) (by norm_num : 115328 ≤ 115456), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_115456_115520 :
    (∑ n ∈ Ico 115456 115520, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 115456 115520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 115456 115520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (173135 : ℤ) ∧
    (∑ n ∈ Ico 115456 115520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3462783656398306594191480231 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_115520_115584 :
    (∑ n ∈ Ico 115520 115584, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 115520 115584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 115520 115584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-302910 : ℤ) ∧
    (∑ n ∈ Ico 115520 115584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6058253231538989960091691137 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_115456_115584 :
    (∑ n ∈ Ico 115456 115584, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 115456 115584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 115456 115584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-129775 : ℤ) ∧
    (∑ n ∈ Ico 115456 115584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2595469575140683365900210906 : ℤ) := by
  rcases cdemPrefixStats_115456_115520 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_115520_115584 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 115456 ≤ 115520) (by norm_num : 115520 ≤ 115584), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 115456 ≤ 115520) (by norm_num : 115520 ≤ 115584), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 115456 ≤ 115520) (by norm_num : 115520 ≤ 115584), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 115456 ≤ 115520) (by norm_num : 115520 ≤ 115584), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_115584_115648 :
    (∑ n ∈ Ico 115584 115648, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 115584 115648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 115584 115648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-129728 : ℤ) ∧
    (∑ n ∈ Ico 115584 115648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2594602158901555156734714904 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_115648_115712 :
    (∑ n ∈ Ico 115648 115712, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 115648 115712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 115648 115712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (648326 : ℤ) ∧
    (∑ n ∈ Ico 115648 115712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12966663426310789043510441920 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_115584_115712 :
    (∑ n ∈ Ico 115584 115712, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 115584 115712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (82 : ℕ) ∧
    (∑ n ∈ Ico 115584 115712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (518598 : ℤ) ∧
    (∑ n ∈ Ico 115584 115712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10372061267409233886775727016 : ℤ) := by
  rcases cdemPrefixStats_115584_115648 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_115648_115712 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 115584 ≤ 115648) (by norm_num : 115648 ≤ 115712), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 115584 ≤ 115648) (by norm_num : 115648 ≤ 115712), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 115584 ≤ 115648) (by norm_num : 115648 ≤ 115712), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 115584 ≤ 115648) (by norm_num : 115648 ≤ 115712), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_115456_115712 :
    (∑ n ∈ Ico 115456 115712, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 115456 115712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (161 : ℕ) ∧
    (∑ n ∈ Ico 115456 115712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (388823 : ℤ) ∧
    (∑ n ∈ Ico 115456 115712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7776591692268550520875516110 : ℤ) := by
  rcases cdemPrefixStats_115456_115584 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_115584_115712 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 115456 ≤ 115584) (by norm_num : 115584 ≤ 115712), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 115456 ≤ 115584) (by norm_num : 115584 ≤ 115712), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 115456 ≤ 115584) (by norm_num : 115584 ≤ 115712), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 115456 ≤ 115584) (by norm_num : 115584 ≤ 115712), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_115200_115712 :
    (∑ n ∈ Ico 115200 115712, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 115200 115712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (315 : ℕ) ∧
    (∑ n ∈ Ico 115200 115712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (214612 : ℤ) ∧
    (∑ n ∈ Ico 115200 115712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4292304490313583557927509876 : ℤ) := by
  rcases cdemPrefixStats_115200_115456 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_115456_115712 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 115200 ≤ 115456) (by norm_num : 115456 ≤ 115712), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 115200 ≤ 115456) (by norm_num : 115456 ≤ 115712), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 115200 ≤ 115456) (by norm_num : 115456 ≤ 115712), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 115200 ≤ 115456) (by norm_num : 115456 ≤ 115712), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_114688_115712 :
    (∑ n ∈ Ico 114688 115712, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 114688 115712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (626 : ℕ) ∧
    (∑ n ∈ Ico 114688 115712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (605630 : ℤ) ∧
    (∑ n ∈ Ico 114688 115712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12112796643277516743602445870 : ℤ) := by
  rcases cdemPrefixStats_114688_115200 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_115200_115712 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 114688 ≤ 115200) (by norm_num : 115200 ≤ 115712), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 114688 ≤ 115200) (by norm_num : 115200 ≤ 115712), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 114688 ≤ 115200) (by norm_num : 115200 ≤ 115712), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 114688 ≤ 115200) (by norm_num : 115200 ≤ 115712), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_115712_115776 :
    (∑ n ∈ Ico 115712 115776, mobiusTreeValue 16 mobiusTable1200001 n) = (-17 : ℤ) ∧
    (∑ n ∈ Ico 115712 115776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 115712 115776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-734317 : ℤ) ∧
    (∑ n ∈ Ico 115712 115776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14686519225106204180338502961 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_115776_115840 :
    (∑ n ∈ Ico 115776 115840, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 115776 115840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 115776 115840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (129531 : ℤ) ∧
    (∑ n ∈ Ico 115776 115840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2590621397128907242746644221 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_115712_115840 :
    (∑ n ∈ Ico 115712 115840, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 115712 115840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 115712 115840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-604786 : ℤ) ∧
    (∑ n ∈ Ico 115712 115840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12095897827977296937591858740 : ℤ) := by
  rcases cdemPrefixStats_115712_115776 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_115776_115840 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 115712 ≤ 115776) (by norm_num : 115776 ≤ 115840), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 115712 ≤ 115776) (by norm_num : 115776 ≤ 115840), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 115712 ≤ 115776) (by norm_num : 115776 ≤ 115840), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 115712 ≤ 115776) (by norm_num : 115776 ≤ 115840), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_115840_115904 :
    (∑ n ∈ Ico 115840 115904, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 115840 115904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 115840 115904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-431481 : ℤ) ∧
    (∑ n ∈ Ico 115840 115904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8629683969834508725806687395 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_115904_115968 :
    (∑ n ∈ Ico 115904 115968, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 115904 115968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 115904 115968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-129397 : ℤ) ∧
    (∑ n ∈ Ico 115904 115968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2587872738792499618468291488 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_115840_115968 :
    (∑ n ∈ Ico 115840 115968, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 115840 115968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 115840 115968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-560878 : ℤ) ∧
    (∑ n ∈ Ico 115840 115968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11217556708627008344274978883 : ℤ) := by
  rcases cdemPrefixStats_115840_115904 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_115904_115968 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 115840 ≤ 115904) (by norm_num : 115904 ≤ 115968), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 115840 ≤ 115904) (by norm_num : 115904 ≤ 115968), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 115840 ≤ 115904) (by norm_num : 115904 ≤ 115968), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 115840 ≤ 115904) (by norm_num : 115904 ≤ 115968), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_115712_115968 :
    (∑ n ∈ Ico 115712 115968, mobiusTreeValue 16 mobiusTable1200001 n) = (-27 : ℤ) ∧
    (∑ n ∈ Ico 115712 115968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (151 : ℕ) ∧
    (∑ n ∈ Ico 115712 115968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1165664 : ℤ) ∧
    (∑ n ∈ Ico 115712 115968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-23313454536604305281866837623 : ℤ) := by
  rcases cdemPrefixStats_115712_115840 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_115840_115968 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 115712 ≤ 115840) (by norm_num : 115840 ≤ 115968), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 115712 ≤ 115840) (by norm_num : 115840 ≤ 115968), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 115712 ≤ 115840) (by norm_num : 115840 ≤ 115968), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 115712 ≤ 115840) (by norm_num : 115840 ≤ 115968), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_115968_116032 :
    (∑ n ∈ Ico 115968 116032, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 115968 116032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 115968 116032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (258539 : ℤ) ∧
    (∑ n ∈ Ico 115968 116032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5170868222667181392879568026 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_116032_116096 :
    (∑ n ∈ Ico 116032 116096, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 116032 116096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 116032 116096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-215475 : ℤ) ∧
    (∑ n ∈ Ico 116032 116096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4309549259802369133855786601 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_115968_116096 :
    (∑ n ∈ Ico 115968 116096, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 115968 116096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 115968 116096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (43064 : ℤ) ∧
    (∑ n ∈ Ico 115968 116096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (861318962864812259023781425 : ℤ) := by
  rcases cdemPrefixStats_115968_116032 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_116032_116096 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 115968 ≤ 116032) (by norm_num : 116032 ≤ 116096), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 115968 ≤ 116032) (by norm_num : 116032 ≤ 116096), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 115968 ≤ 116032) (by norm_num : 116032 ≤ 116096), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 115968 ≤ 116032) (by norm_num : 116032 ≤ 116096), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_116096_116160 :
    (∑ n ∈ Ico 116096 116160, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 116096 116160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 116096 116160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (43084 : ℤ) ∧
    (∑ n ∈ Ico 116096 116160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (861615423985908625581909534 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_116160_116224 :
    (∑ n ∈ Ico 116160 116224, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 116160 116224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 116160 116224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (129059 : ℤ) ∧
    (∑ n ∈ Ico 116160 116224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2581177897223469069341976857 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_116096_116224 :
    (∑ n ∈ Ico 116096 116224, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 116096 116224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 116096 116224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (172143 : ℤ) ∧
    (∑ n ∈ Ico 116096 116224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3442793321209377694923886391 : ℤ) := by
  rcases cdemPrefixStats_116096_116160 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_116160_116224 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 116096 ≤ 116160) (by norm_num : 116160 ≤ 116224), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 116096 ≤ 116160) (by norm_num : 116160 ≤ 116224), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 116096 ≤ 116160) (by norm_num : 116160 ≤ 116224), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 116096 ≤ 116160) (by norm_num : 116160 ≤ 116224), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_115968_116224 :
    (∑ n ∈ Ico 115968 116224, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 115968 116224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 115968 116224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (215207 : ℤ) ∧
    (∑ n ∈ Ico 115968 116224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4304112284074189953947667816 : ℤ) := by
  rcases cdemPrefixStats_115968_116096 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_116096_116224 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 115968 ≤ 116096) (by norm_num : 116096 ≤ 116224), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 115968 ≤ 116096) (by norm_num : 116096 ≤ 116224), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 115968 ≤ 116096) (by norm_num : 116096 ≤ 116224), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 115968 ≤ 116096) (by norm_num : 116096 ≤ 116224), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_115712_116224 :
    (∑ n ∈ Ico 115712 116224, mobiusTreeValue 16 mobiusTable1200001 n) = (-22 : ℤ) ∧
    (∑ n ∈ Ico 115712 116224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (306 : ℕ) ∧
    (∑ n ∈ Ico 115712 116224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-950457 : ℤ) ∧
    (∑ n ∈ Ico 115712 116224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-19009342252530115327919169807 : ℤ) := by
  rcases cdemPrefixStats_115712_115968 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_115968_116224 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 115712 ≤ 115968) (by norm_num : 115968 ≤ 116224), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 115712 ≤ 115968) (by norm_num : 115968 ≤ 116224), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 115712 ≤ 115968) (by norm_num : 115968 ≤ 116224), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 115712 ≤ 115968) (by norm_num : 115968 ≤ 116224), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_116224_116288 :
    (∑ n ∈ Ico 116224 116288, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 116224 116288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 116224 116288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-128911 : ℤ) ∧
    (∑ n ∈ Ico 116224 116288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2578299773516028498949887947 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_116288_116352 :
    (∑ n ∈ Ico 116288 116352, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 116288 116352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 116288 116352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (171952 : ℤ) ∧
    (∑ n ∈ Ico 116288 116352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3439114781781425700751949898 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_116224_116352 :
    (∑ n ∈ Ico 116224 116352, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 116224 116352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 116224 116352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (43041 : ℤ) ∧
    (∑ n ∈ Ico 116224 116352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (860815008265397201802061951 : ℤ) := by
  rcases cdemPrefixStats_116224_116288 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_116288_116352 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 116224 ≤ 116288) (by norm_num : 116288 ≤ 116352), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 116224 ≤ 116288) (by norm_num : 116288 ≤ 116352), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 116224 ≤ 116288) (by norm_num : 116288 ≤ 116352), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 116224 ≤ 116288) (by norm_num : 116288 ≤ 116352), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_116352_116416 :
    (∑ n ∈ Ico 116352 116416, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 116352 116416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 116352 116416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-43029 : ℤ) ∧
    (∑ n ∈ Ico 116352 116416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-860627388024676416448643495 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_116416_116480 :
    (∑ n ∈ Ico 116416 116480, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 116416 116480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 116416 116480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (257598 : ℤ) ∧
    (∑ n ∈ Ico 116416 116480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5151961551890633330620018175 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_116352_116480 :
    (∑ n ∈ Ico 116352 116480, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 116352 116480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 116352 116480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (214569 : ℤ) ∧
    (∑ n ∈ Ico 116352 116480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4291334163865956914171374680 : ℤ) := by
  rcases cdemPrefixStats_116352_116416 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_116416_116480 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 116352 ≤ 116416) (by norm_num : 116416 ≤ 116480), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 116352 ≤ 116416) (by norm_num : 116416 ≤ 116480), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 116352 ≤ 116416) (by norm_num : 116416 ≤ 116480), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 116352 ≤ 116416) (by norm_num : 116416 ≤ 116480), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_116224_116480 :
    (∑ n ∈ Ico 116224 116480, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 116224 116480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 116224 116480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (257610 : ℤ) ∧
    (∑ n ∈ Ico 116224 116480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5152149172131354115973436631 : ℤ) := by
  rcases cdemPrefixStats_116224_116352 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_116352_116480 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 116224 ≤ 116352) (by norm_num : 116352 ≤ 116480), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 116224 ≤ 116352) (by norm_num : 116352 ≤ 116480), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 116224 ≤ 116352) (by norm_num : 116352 ≤ 116480), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 116224 ≤ 116352) (by norm_num : 116352 ≤ 116480), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_116480_116544 :
    (∑ n ∈ Ico 116480 116544, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 116480 116544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 116480 116544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (42904 : ℤ) ∧
    (∑ n ∈ Ico 116480 116544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (858111190927476689020847965 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_116544_116608 :
    (∑ n ∈ Ico 116544 116608, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 116544 116608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 116544 116608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (20 : ℤ) ∧
    (∑ n ∈ Ico 116544 116608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (470862684174288633697924 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_116480_116608 :
    (∑ n ∈ Ico 116480 116608, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 116480 116608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 116480 116608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (42924 : ℤ) ∧
    (∑ n ∈ Ico 116480 116608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (858582053611650977654545889 : ℤ) := by
  rcases cdemPrefixStats_116480_116544 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_116544_116608 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 116480 ≤ 116544) (by norm_num : 116544 ≤ 116608), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 116480 ≤ 116544) (by norm_num : 116544 ≤ 116608), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 116480 ≤ 116544) (by norm_num : 116544 ≤ 116608), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 116480 ≤ 116544) (by norm_num : 116544 ≤ 116608), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_116608_116672 :
    (∑ n ∈ Ico 116608 116672, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 116608 116672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 116608 116672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (257242 : ℤ) ∧
    (∑ n ∈ Ico 116608 116672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5144959342386295833461899649 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_116672_116736 :
    (∑ n ∈ Ico 116672 116736, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 116672 116736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 116672 116736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (171350 : ℤ) ∧
    (∑ n ∈ Ico 116672 116736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3427048834156817535382304851 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_116608_116736 :
    (∑ n ∈ Ico 116608 116736, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 116608 116736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 116608 116736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (428592 : ℤ) ∧
    (∑ n ∈ Ico 116608 116736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8572008176543113368844204500 : ℤ) := by
  rcases cdemPrefixStats_116608_116672 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_116672_116736 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 116608 ≤ 116672) (by norm_num : 116672 ≤ 116736), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 116608 ≤ 116672) (by norm_num : 116672 ≤ 116736), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 116608 ≤ 116672) (by norm_num : 116672 ≤ 116736), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 116608 ≤ 116672) (by norm_num : 116672 ≤ 116736), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_116480_116736 :
    (∑ n ∈ Ico 116480 116736, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 116480 116736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 116480 116736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (471516 : ℤ) ∧
    (∑ n ∈ Ico 116480 116736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9430590230154764346498750389 : ℤ) := by
  rcases cdemPrefixStats_116480_116608 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_116608_116736 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 116480 ≤ 116608) (by norm_num : 116608 ≤ 116736), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 116480 ≤ 116608) (by norm_num : 116608 ≤ 116736), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 116480 ≤ 116608) (by norm_num : 116608 ≤ 116736), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 116480 ≤ 116608) (by norm_num : 116608 ≤ 116736), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_116224_116736 :
    (∑ n ∈ Ico 116224 116736, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 116224 116736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 116224 116736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (729126 : ℤ) ∧
    (∑ n ∈ Ico 116224 116736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14582739402286118462472187020 : ℤ) := by
  rcases cdemPrefixStats_116224_116480 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_116480_116736 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 116224 ≤ 116480) (by norm_num : 116480 ≤ 116736), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 116224 ≤ 116480) (by norm_num : 116480 ≤ 116736), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 116224 ≤ 116480) (by norm_num : 116480 ≤ 116736), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 116224 ≤ 116480) (by norm_num : 116480 ≤ 116736), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_115712_116736 :
    (∑ n ∈ Ico 115712 116736, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 115712 116736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (615 : ℕ) ∧
    (∑ n ∈ Ico 115712 116736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-221331 : ℤ) ∧
    (∑ n ∈ Ico 115712 116736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4426602850243996865446982787 : ℤ) := by
  rcases cdemPrefixStats_115712_116224 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_116224_116736 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 115712 ≤ 116224) (by norm_num : 116224 ≤ 116736), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 115712 ≤ 116224) (by norm_num : 116224 ≤ 116736), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 115712 ≤ 116224) (by norm_num : 116224 ≤ 116736), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 115712 ≤ 116224) (by norm_num : 116224 ≤ 116736), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_114688_116736 :
    (∑ n ∈ Ico 114688 116736, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 114688 116736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1241 : ℕ) ∧
    (∑ n ∈ Ico 114688 116736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (384299 : ℤ) ∧
    (∑ n ∈ Ico 114688 116736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7686193793033519878155463083 : ℤ) := by
  rcases cdemPrefixStats_114688_115712 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_115712_116736 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 114688 ≤ 115712) (by norm_num : 115712 ≤ 116736), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 114688 ≤ 115712) (by norm_num : 115712 ≤ 116736), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 114688 ≤ 115712) (by norm_num : 115712 ≤ 116736), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 114688 ≤ 115712) (by norm_num : 115712 ≤ 116736), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_116736_116800 :
    (∑ n ∈ Ico 116736 116800, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 116736 116800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 116736 116800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (299773 : ℤ) ∧
    (∑ n ∈ Ico 116736 116800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5995519219387290179717885857 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_116800_116864 :
    (∑ n ∈ Ico 116800 116864, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 116800 116864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 116800 116864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (299535 : ℤ) ∧
    (∑ n ∈ Ico 116800 116864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5990806121707800770209680091 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_116736_116864 :
    (∑ n ∈ Ico 116736 116864, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 116736 116864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 116736 116864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (599308 : ℤ) ∧
    (∑ n ∈ Ico 116736 116864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11986325341095090949927565948 : ℤ) := by
  rcases cdemPrefixStats_116736_116800 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_116800_116864 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 116736 ≤ 116800) (by norm_num : 116800 ≤ 116864), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 116736 ≤ 116800) (by norm_num : 116800 ≤ 116864), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 116736 ≤ 116800) (by norm_num : 116800 ≤ 116864), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 116736 ≤ 116800) (by norm_num : 116800 ≤ 116864), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_116864_116928 :
    (∑ n ∈ Ico 116864 116928, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 116864 116928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 116864 116928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-85571 : ℤ) ∧
    (∑ n ∈ Ico 116864 116928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1711405602931046357750237204 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_116928_116992 :
    (∑ n ∈ Ico 116928 116992, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 116928 116992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 116928 116992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-384717 : ℤ) ∧
    (∑ n ∈ Ico 116928 116992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7694353796450769655234411514 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_116864_116992 :
    (∑ n ∈ Ico 116864 116992, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 116864 116992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 116864 116992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-470288 : ℤ) ∧
    (∑ n ∈ Ico 116864 116992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9405759399381816012984648718 : ℤ) := by
  rcases cdemPrefixStats_116864_116928 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_116928_116992 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 116864 ≤ 116928) (by norm_num : 116928 ≤ 116992), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 116864 ≤ 116928) (by norm_num : 116928 ≤ 116992), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 116864 ≤ 116928) (by norm_num : 116928 ≤ 116992), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 116864 ≤ 116928) (by norm_num : 116928 ≤ 116992), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_116736_116992 :
    (∑ n ∈ Ico 116736 116992, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 116736 116992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 116736 116992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (129020 : ℤ) ∧
    (∑ n ∈ Ico 116736 116992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2580565941713274936942917230 : ℤ) := by
  rcases cdemPrefixStats_116736_116864 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_116864_116992 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 116736 ≤ 116864) (by norm_num : 116864 ≤ 116992), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 116736 ≤ 116864) (by norm_num : 116864 ≤ 116992), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 116736 ≤ 116864) (by norm_num : 116864 ≤ 116992), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 116736 ≤ 116864) (by norm_num : 116864 ≤ 116992), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_116992_117056 :
    (∑ n ∈ Ico 116992 117056, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 116992 117056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 116992 117056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-683555 : ℤ) ∧
    (∑ n ∈ Ico 116992 117056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13671277638503090907867708655 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_117056_117120 :
    (∑ n ∈ Ico 117056 117120, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 117056 117120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 117056 117120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-85375 : ℤ) ∧
    (∑ n ∈ Ico 117056 117120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1707460606394925398977087479 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_116992_117120 :
    (∑ n ∈ Ico 116992 117120, mobiusTreeValue 16 mobiusTable1200001 n) = (-18 : ℤ) ∧
    (∑ n ∈ Ico 116992 117120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 116992 117120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-768930 : ℤ) ∧
    (∑ n ∈ Ico 116992 117120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-15378738244898016306844796134 : ℤ) := by
  rcases cdemPrefixStats_116992_117056 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_117056_117120 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 116992 ≤ 117056) (by norm_num : 117056 ≤ 117120), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 116992 ≤ 117056) (by norm_num : 117056 ≤ 117120), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 116992 ≤ 117056) (by norm_num : 117056 ≤ 117120), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 116992 ≤ 117056) (by norm_num : 117056 ≤ 117120), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_117120_117184 :
    (∑ n ∈ Ico 117120 117184, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 117120 117184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 117120 117184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (42700 : ℤ) ∧
    (∑ n ∈ Ico 117120 117184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (854072716373513513455669234 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_117184_117248 :
    (∑ n ∈ Ico 117184 117248, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 117184 117248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 117184 117248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-85312 : ℤ) ∧
    (∑ n ∈ Ico 117184 117248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1706237397508045059239819638 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_117120_117248 :
    (∑ n ∈ Ico 117120 117248, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 117120 117248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 117120 117248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-42612 : ℤ) ∧
    (∑ n ∈ Ico 117120 117248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-852164681134531545784150404 : ℤ) := by
  rcases cdemPrefixStats_117120_117184 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_117184_117248 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 117120 ≤ 117184) (by norm_num : 117184 ≤ 117248), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 117120 ≤ 117184) (by norm_num : 117184 ≤ 117248), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 117120 ≤ 117184) (by norm_num : 117184 ≤ 117248), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 117120 ≤ 117184) (by norm_num : 117184 ≤ 117248), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_116992_117248 :
    (∑ n ∈ Ico 116992 117248, mobiusTreeValue 16 mobiusTable1200001 n) = (-19 : ℤ) ∧
    (∑ n ∈ Ico 116992 117248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 116992 117248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-811542 : ℤ) ∧
    (∑ n ∈ Ico 116992 117248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-16230902926032547852628946538 : ℤ) := by
  rcases cdemPrefixStats_116992_117120 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_117120_117248 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 116992 ≤ 117120) (by norm_num : 117120 ≤ 117248), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 116992 ≤ 117120) (by norm_num : 117120 ≤ 117248), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 116992 ≤ 117120) (by norm_num : 117120 ≤ 117248), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 116992 ≤ 117120) (by norm_num : 117120 ≤ 117248), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_116736_117248 :
    (∑ n ∈ Ico 116736 117248, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 116736 117248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 116736 117248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-682522 : ℤ) ∧
    (∑ n ∈ Ico 116736 117248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13650336984319272915686029308 : ℤ) := by
  rcases cdemPrefixStats_116736_116992 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_116992_117248 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 116736 ≤ 116992) (by norm_num : 116992 ≤ 117248), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 116736 ≤ 116992) (by norm_num : 116992 ≤ 117248), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 116736 ≤ 116992) (by norm_num : 116992 ≤ 117248), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 116736 ≤ 116992) (by norm_num : 116992 ≤ 117248), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_117248_117312 :
    (∑ n ∈ Ico 117248 117312, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 117248 117312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 117248 117312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-39 : ℤ) ∧
    (∑ n ∈ Ico 117248 117312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-727208881271795840788266 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_117312_117376 :
    (∑ n ∈ Ico 117312 117376, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 117312 117376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 117312 117376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (213036 : ℤ) ∧
    (∑ n ∈ Ico 117312 117376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4260809375788217711775037463 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_117248_117376 :
    (∑ n ∈ Ico 117248 117376, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 117248 117376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 117248 117376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (212997 : ℤ) ∧
    (∑ n ∈ Ico 117248 117376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4260082166906945915934249197 : ℤ) := by
  rcases cdemPrefixStats_117248_117312 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_117312_117376 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 117248 ≤ 117312) (by norm_num : 117312 ≤ 117376), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 117248 ≤ 117312) (by norm_num : 117312 ≤ 117376), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 117248 ≤ 117312) (by norm_num : 117312 ≤ 117376), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 117248 ≤ 117312) (by norm_num : 117312 ≤ 117376), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_117376_117440 :
    (∑ n ∈ Ico 117376 117440, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 117376 117440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 117376 117440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-383230 : ℤ) ∧
    (∑ n ∈ Ico 117376 117440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7664691712376000234681886054 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_117440_117504 :
    (∑ n ∈ Ico 117440 117504, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 117440 117504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 117440 117504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (212822 : ℤ) ∧
    (∑ n ∈ Ico 117440 117504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4256565029480258900638982708 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_117376_117504 :
    (∑ n ∈ Ico 117376 117504, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 117376 117504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 117376 117504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-170408 : ℤ) ∧
    (∑ n ∈ Ico 117376 117504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3408126682895741334042903346 : ℤ) := by
  rcases cdemPrefixStats_117376_117440 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_117440_117504 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 117376 ≤ 117440) (by norm_num : 117440 ≤ 117504), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 117376 ≤ 117440) (by norm_num : 117440 ≤ 117504), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 117376 ≤ 117440) (by norm_num : 117440 ≤ 117504), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 117376 ≤ 117440) (by norm_num : 117440 ≤ 117504), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_117248_117504 :
    (∑ n ∈ Ico 117248 117504, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 117248 117504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 117248 117504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (42589 : ℤ) ∧
    (∑ n ∈ Ico 117248 117504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (851955484011204581891345851 : ℤ) := by
  rcases cdemPrefixStats_117248_117376 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_117376_117504 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 117248 ≤ 117376) (by norm_num : 117376 ≤ 117504), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 117248 ≤ 117376) (by norm_num : 117376 ≤ 117504), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 117248 ≤ 117376) (by norm_num : 117376 ≤ 117504), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 117248 ≤ 117376) (by norm_num : 117376 ≤ 117504), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_117504_117568 :
    (∑ n ∈ Ico 117504 117568, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 117504 117568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 117504 117568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-382846 : ℤ) ∧
    (∑ n ∈ Ico 117504 117568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7656924683298627499649759978 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_117568_117632 :
    (∑ n ∈ Ico 117568 117632, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 117568 117632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 117568 117632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (85114 : ℤ) ∧
    (∑ n ∈ Ico 117568 117632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1702343493536835795596029168 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_117504_117632 :
    (∑ n ∈ Ico 117504 117632, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 117504 117632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 117504 117632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-297732 : ℤ) ∧
    (∑ n ∈ Ico 117504 117632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5954581189761791704053730810 : ℤ) := by
  rcases cdemPrefixStats_117504_117568 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_117568_117632 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 117504 ≤ 117568) (by norm_num : 117568 ≤ 117632), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 117504 ≤ 117568) (by norm_num : 117568 ≤ 117632), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 117504 ≤ 117568) (by norm_num : 117568 ≤ 117632), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 117504 ≤ 117568) (by norm_num : 117568 ≤ 117632), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_117632_117696 :
    (∑ n ∈ Ico 117632 117696, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 117632 117696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 117632 117696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-42543 : ℤ) ∧
    (∑ n ∈ Ico 117632 117696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-850852726387583555358042095 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_117696_117760 :
    (∑ n ∈ Ico 117696 117760, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 117696 117760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 117696 117760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-84927 : ℤ) ∧
    (∑ n ∈ Ico 117696 117760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1698549949587869972069231625 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_117632_117760 :
    (∑ n ∈ Ico 117632 117760, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 117632 117760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 117632 117760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-127470 : ℤ) ∧
    (∑ n ∈ Ico 117632 117760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2549402675975453527427273720 : ℤ) := by
  rcases cdemPrefixStats_117632_117696 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_117696_117760 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 117632 ≤ 117696) (by norm_num : 117696 ≤ 117760), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 117632 ≤ 117696) (by norm_num : 117696 ≤ 117760), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 117632 ≤ 117696) (by norm_num : 117696 ≤ 117760), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 117632 ≤ 117696) (by norm_num : 117696 ≤ 117760), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_117504_117760 :
    (∑ n ∈ Ico 117504 117760, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 117504 117760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 117504 117760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-425202 : ℤ) ∧
    (∑ n ∈ Ico 117504 117760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8503983865737245231481004530 : ℤ) := by
  rcases cdemPrefixStats_117504_117632 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_117632_117760 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 117504 ≤ 117632) (by norm_num : 117632 ≤ 117760), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 117504 ≤ 117632) (by norm_num : 117632 ≤ 117760), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 117504 ≤ 117632) (by norm_num : 117632 ≤ 117760), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 117504 ≤ 117632) (by norm_num : 117632 ≤ 117760), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_117248_117760 :
    (∑ n ∈ Ico 117248 117760, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 117248 117760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 117248 117760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-382613 : ℤ) ∧
    (∑ n ∈ Ico 117248 117760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7652028381726040649589658679 : ℤ) := by
  rcases cdemPrefixStats_117248_117504 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_117504_117760 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 117248 ≤ 117504) (by norm_num : 117504 ≤ 117760), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 117248 ≤ 117504) (by norm_num : 117504 ≤ 117760), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 117248 ≤ 117504) (by norm_num : 117504 ≤ 117760), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 117248 ≤ 117504) (by norm_num : 117504 ≤ 117760), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_116736_117760 :
    (∑ n ∈ Ico 116736 117760, mobiusTreeValue 16 mobiusTable1200001 n) = (-25 : ℤ) ∧
    (∑ n ∈ Ico 116736 117760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (621 : ℕ) ∧
    (∑ n ∈ Ico 116736 117760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1065135 : ℤ) ∧
    (∑ n ∈ Ico 116736 117760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-21302365366045313565275687987 : ℤ) := by
  rcases cdemPrefixStats_116736_117248 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_117248_117760 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 116736 ≤ 117248) (by norm_num : 117248 ≤ 117760), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 116736 ≤ 117248) (by norm_num : 117248 ≤ 117760), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 116736 ≤ 117248) (by norm_num : 117248 ≤ 117760), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 116736 ≤ 117248) (by norm_num : 117248 ≤ 117760), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_117760_117824 :
    (∑ n ∈ Ico 117760 117824, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 117760 117824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 117760 117824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (509322 : ℤ) ∧
    (∑ n ∈ Ico 117760 117824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10186555695682511880466204966 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_117824_117888 :
    (∑ n ∈ Ico 117824 117888, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 117824 117888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 117824 117888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-84850 : ℤ) ∧
    (∑ n ∈ Ico 117824 117888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1697000603083454579853099623 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_117760_117888 :
    (∑ n ∈ Ico 117760 117888, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 117760 117888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 117760 117888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (424472 : ℤ) ∧
    (∑ n ∈ Ico 117760 117888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8489555092599057300613105343 : ℤ) := by
  rcases cdemPrefixStats_117760_117824 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_117824_117888 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 117760 ≤ 117824) (by norm_num : 117824 ≤ 117888), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 117760 ≤ 117824) (by norm_num : 117824 ≤ 117888), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 117760 ≤ 117824) (by norm_num : 117824 ≤ 117888), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 117760 ≤ 117824) (by norm_num : 117824 ≤ 117888), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_117888_117952 :
    (∑ n ∈ Ico 117888 117952, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 117888 117952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 117888 117952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (127218 : ℤ) ∧
    (∑ n ∈ Ico 117888 117952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2544385394348557138056598341 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_117952_118016 :
    (∑ n ∈ Ico 117952 118016, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 117952 118016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 117952 118016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-211848 : ℤ) ∧
    (∑ n ∈ Ico 117952 118016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4236964813575649279689904025 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_117888_118016 :
    (∑ n ∈ Ico 117888 118016, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 117888 118016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 117888 118016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-84630 : ℤ) ∧
    (∑ n ∈ Ico 117888 118016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1692579419227092141633305684 : ℤ) := by
  rcases cdemPrefixStats_117888_117952 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_117952_118016 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 117888 ≤ 117952) (by norm_num : 117952 ≤ 118016), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 117888 ≤ 117952) (by norm_num : 117952 ≤ 118016), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 117888 ≤ 117952) (by norm_num : 117952 ≤ 118016), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 117888 ≤ 117952) (by norm_num : 117952 ≤ 118016), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_117760_118016 :
    (∑ n ∈ Ico 117760 118016, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 117760 118016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 117760 118016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (339842 : ℤ) ∧
    (∑ n ∈ Ico 117760 118016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6796975673371965158979799659 : ℤ) := by
  rcases cdemPrefixStats_117760_117888 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_117888_118016 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 117760 ≤ 117888) (by norm_num : 117888 ≤ 118016), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 117760 ≤ 117888) (by norm_num : 117888 ≤ 118016), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 117760 ≤ 117888) (by norm_num : 117888 ≤ 118016), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 117760 ≤ 117888) (by norm_num : 117888 ≤ 118016), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_118016_118080 :
    (∑ n ∈ Ico 118016 118080, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 118016 118080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 118016 118080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (211796 : ℤ) ∧
    (∑ n ∈ Ico 118016 118080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4235967243087297532664625693 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_118080_118144 :
    (∑ n ∈ Ico 118080 118144, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 118080 118144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 118080 118144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (211678 : ℤ) ∧
    (∑ n ∈ Ico 118080 118144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4233628481175251129583534020 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_118016_118144 :
    (∑ n ∈ Ico 118016 118144, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 118016 118144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 118016 118144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (423474 : ℤ) ∧
    (∑ n ∈ Ico 118016 118144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8469595724262548662248159713 : ℤ) := by
  rcases cdemPrefixStats_118016_118080 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_118080_118144 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 118016 ≤ 118080) (by norm_num : 118080 ≤ 118144), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 118016 ≤ 118080) (by norm_num : 118080 ≤ 118144), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 118016 ≤ 118080) (by norm_num : 118080 ≤ 118144), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 118016 ≤ 118080) (by norm_num : 118080 ≤ 118144), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_118144_118208 :
    (∑ n ∈ Ico 118144 118208, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 118144 118208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 118144 118208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (211545 : ℤ) ∧
    (∑ n ∈ Ico 118144 118208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4231006205700301821223371991 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_118208_118272 :
    (∑ n ∈ Ico 118208 118272, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 118208 118272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 118208 118272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-296005 : ℤ) ∧
    (∑ n ∈ Ico 118208 118272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5920083833046203952641901440 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_118144_118272 :
    (∑ n ∈ Ico 118144 118272, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 118144 118272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 118144 118272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-84460 : ℤ) ∧
    (∑ n ∈ Ico 118144 118272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1689077627345902131418529449 : ℤ) := by
  rcases cdemPrefixStats_118144_118208 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_118208_118272 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 118144 ≤ 118208) (by norm_num : 118208 ≤ 118272), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 118144 ≤ 118208) (by norm_num : 118208 ≤ 118272), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 118144 ≤ 118208) (by norm_num : 118208 ≤ 118272), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 118144 ≤ 118208) (by norm_num : 118208 ≤ 118272), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_118016_118272 :
    (∑ n ∈ Ico 118016 118272, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 118016 118272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 118016 118272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (339014 : ℤ) ∧
    (∑ n ∈ Ico 118016 118272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6780518096916646530829630264 : ℤ) := by
  rcases cdemPrefixStats_118016_118144 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_118144_118272 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 118016 ≤ 118144) (by norm_num : 118144 ≤ 118272), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 118016 ≤ 118144) (by norm_num : 118144 ≤ 118272), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 118016 ≤ 118144) (by norm_num : 118144 ≤ 118272), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 118016 ≤ 118144) (by norm_num : 118144 ≤ 118272), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_117760_118272 :
    (∑ n ∈ Ico 117760 118272, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 117760 118272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 117760 118272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (678856 : ℤ) ∧
    (∑ n ∈ Ico 117760 118272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13577493770288611689809429923 : ℤ) := by
  rcases cdemPrefixStats_117760_118016 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_118016_118272 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 117760 ≤ 118016) (by norm_num : 118016 ≤ 118272), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 117760 ≤ 118016) (by norm_num : 118016 ≤ 118272), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 117760 ≤ 118016) (by norm_num : 118016 ≤ 118272), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 117760 ≤ 118016) (by norm_num : 118016 ≤ 118272), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_118272_118336 :
    (∑ n ∈ Ico 118272 118336, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 118272 118336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 118272 118336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (42204 : ℤ) ∧
    (∑ n ∈ Ico 118272 118336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (844079540114717643851140712 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_118336_118400 :
    (∑ n ∈ Ico 118336 118400, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 118336 118400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 118336 118400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (380193 : ℤ) ∧
    (∑ n ∈ Ico 118336 118400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7603941816177705752009141987 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_118272_118400 :
    (∑ n ∈ Ico 118272 118400, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 118272 118400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 118272 118400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (422397 : ℤ) ∧
    (∑ n ∈ Ico 118272 118400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8448021356292423395860282699 : ℤ) := by
  rcases cdemPrefixStats_118272_118336 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_118336_118400 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 118272 ≤ 118336) (by norm_num : 118336 ≤ 118400), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 118272 ≤ 118336) (by norm_num : 118336 ≤ 118400), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 118272 ≤ 118336) (by norm_num : 118336 ≤ 118400), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 118272 ≤ 118336) (by norm_num : 118336 ≤ 118400), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_118400_118464 :
    (∑ n ∈ Ico 118400 118464, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 118400 118464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 118400 118464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (42214 : ℤ) ∧
    (∑ n ∈ Ico 118400 118464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (844280571543943274776263299 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_118464_118528 :
    (∑ n ∈ Ico 118464 118528, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 118464 118528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 118464 118528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (253183 : ℤ) ∧
    (∑ n ∈ Ico 118464 118528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5063682994974242401715598427 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_118400_118528 :
    (∑ n ∈ Ico 118400 118528, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 118400 118528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 118400 118528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (295397 : ℤ) ∧
    (∑ n ∈ Ico 118400 118528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5907963566518185676491861726 : ℤ) := by
  rcases cdemPrefixStats_118400_118464 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_118464_118528 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 118400 ≤ 118464) (by norm_num : 118464 ≤ 118528), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 118400 ≤ 118464) (by norm_num : 118464 ≤ 118528), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 118400 ≤ 118464) (by norm_num : 118464 ≤ 118528), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 118400 ≤ 118464) (by norm_num : 118464 ≤ 118528), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_118272_118528 :
    (∑ n ∈ Ico 118272 118528, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 118272 118528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 118272 118528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (717794 : ℤ) ∧
    (∑ n ∈ Ico 118272 118528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14355984922810609072352144425 : ℤ) := by
  rcases cdemPrefixStats_118272_118400 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_118400_118528 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 118272 ≤ 118400) (by norm_num : 118400 ≤ 118528), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 118272 ≤ 118400) (by norm_num : 118400 ≤ 118528), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 118272 ≤ 118400) (by norm_num : 118400 ≤ 118528), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 118272 ≤ 118400) (by norm_num : 118400 ≤ 118528), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_118528_118592 :
    (∑ n ∈ Ico 118528 118592, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 118528 118592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 118528 118592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-295147 : ℤ) ∧
    (∑ n ∈ Ico 118528 118592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5903074009162224678895625790 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_118592_118656 :
    (∑ n ∈ Ico 118592 118656, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 118592 118656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 118592 118656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-168563 : ℤ) ∧
    (∑ n ∈ Ico 118592 118656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3371323833382501516133520122 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_118528_118656 :
    (∑ n ∈ Ico 118528 118656, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 118528 118656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 118528 118656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-463710 : ℤ) ∧
    (∑ n ∈ Ico 118528 118656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9274397842544726195029145912 : ℤ) := by
  rcases cdemPrefixStats_118528_118592 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_118592_118656 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 118528 ≤ 118592) (by norm_num : 118592 ≤ 118656), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 118528 ≤ 118592) (by norm_num : 118592 ≤ 118656), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 118528 ≤ 118592) (by norm_num : 118592 ≤ 118656), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 118528 ≤ 118592) (by norm_num : 118592 ≤ 118656), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_118656_118720 :
    (∑ n ∈ Ico 118656 118720, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 118656 118720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 118656 118720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (84199 : ℤ) ∧
    (∑ n ∈ Ico 118656 118720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1683961626226919892042283919 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_118720_118784 :
    (∑ n ∈ Ico 118720 118784, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 118720 118784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 118720 118784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (294751 : ℤ) ∧
    (∑ n ∈ Ico 118720 118784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5895091603261607098134772946 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_118656_118784 :
    (∑ n ∈ Ico 118656 118784, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 118656 118784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 118656 118784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (378950 : ℤ) ∧
    (∑ n ∈ Ico 118656 118784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7579053229488526990177056865 : ℤ) := by
  rcases cdemPrefixStats_118656_118720 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_118720_118784 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 118656 ≤ 118720) (by norm_num : 118720 ≤ 118784), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 118656 ≤ 118720) (by norm_num : 118720 ≤ 118784), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 118656 ≤ 118720) (by norm_num : 118720 ≤ 118784), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 118656 ≤ 118720) (by norm_num : 118720 ≤ 118784), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_118528_118784 :
    (∑ n ∈ Ico 118528 118784, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 118528 118784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 118528 118784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-84760 : ℤ) ∧
    (∑ n ∈ Ico 118528 118784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1695344613056199204852089047 : ℤ) := by
  rcases cdemPrefixStats_118528_118656 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_118656_118784 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 118528 ≤ 118656) (by norm_num : 118656 ≤ 118784), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 118528 ≤ 118656) (by norm_num : 118656 ≤ 118784), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 118528 ≤ 118656) (by norm_num : 118656 ≤ 118784), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 118528 ≤ 118656) (by norm_num : 118656 ≤ 118784), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_118272_118784 :
    (∑ n ∈ Ico 118272 118784, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 118272 118784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 118272 118784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (633034 : ℤ) ∧
    (∑ n ∈ Ico 118272 118784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12660640309754409867500055378 : ℤ) := by
  rcases cdemPrefixStats_118272_118528 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_118528_118784 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 118272 ≤ 118528) (by norm_num : 118528 ≤ 118784), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 118272 ≤ 118528) (by norm_num : 118528 ≤ 118784), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 118272 ≤ 118528) (by norm_num : 118528 ≤ 118784), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 118272 ≤ 118528) (by norm_num : 118528 ≤ 118784), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_117760_118784 :
    (∑ n ∈ Ico 117760 118784, mobiusTreeValue 16 mobiusTable1200001 n) = (31 : ℤ) ∧
    (∑ n ∈ Ico 117760 118784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (621 : ℕ) ∧
    (∑ n ∈ Ico 117760 118784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1311890 : ℤ) ∧
    (∑ n ∈ Ico 117760 118784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (26238134080043021557309485301 : ℤ) := by
  rcases cdemPrefixStats_117760_118272 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_118272_118784 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 117760 ≤ 118272) (by norm_num : 118272 ≤ 118784), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 117760 ≤ 118272) (by norm_num : 118272 ≤ 118784), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 117760 ≤ 118272) (by norm_num : 118272 ≤ 118784), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 117760 ≤ 118272) (by norm_num : 118272 ≤ 118784), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_116736_118784 :
    (∑ n ∈ Ico 116736 118784, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 116736 118784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1242 : ℕ) ∧
    (∑ n ∈ Ico 116736 118784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (246755 : ℤ) ∧
    (∑ n ∈ Ico 116736 118784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4935768713997707992033797314 : ℤ) := by
  rcases cdemPrefixStats_116736_117760 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_117760_118784 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 116736 ≤ 117760) (by norm_num : 117760 ≤ 118784), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 116736 ≤ 117760) (by norm_num : 117760 ≤ 118784), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 116736 ≤ 117760) (by norm_num : 117760 ≤ 118784), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 116736 ≤ 117760) (by norm_num : 117760 ≤ 118784), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_114688_118784 :
    (∑ n ∈ Ico 114688 118784, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 114688 118784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2483 : ℕ) ∧
    (∑ n ∈ Ico 114688 118784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (631054 : ℤ) ∧
    (∑ n ∈ Ico 114688 118784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12621962507031227870189260397 : ℤ) := by
  rcases cdemPrefixStats_114688_116736 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_116736_118784 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 114688 ≤ 116736) (by norm_num : 116736 ≤ 118784), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 114688 ≤ 116736) (by norm_num : 116736 ≤ 118784), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 114688 ≤ 116736) (by norm_num : 116736 ≤ 118784), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 114688 ≤ 116736) (by norm_num : 116736 ≤ 118784), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup028_checked_complete :
    (∑ n ∈ Ico 114688 118784, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 114688 118784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2483 : ℕ) ∧
    (∑ n ∈ Ico 114688 118784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (631054 : ℤ) ∧
    (∑ n ∈ Ico 114688 118784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12621962507031227870189260397 : ℤ) := cdemPrefixStats_114688_118784
end Helfgott
#print axioms Helfgott.cdemPrefixGroup028_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 114688 118784, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 114688 118784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2483 : ℕ) ∧
    (∑ n ∈ Ico 114688 118784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (631054 : ℤ) ∧
    (∑ n ∈ Ico 114688 118784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12621962507031227870189260397 : ℤ) := Helfgott.cdemPrefixGroup028_checked_complete
#print axioms solution
