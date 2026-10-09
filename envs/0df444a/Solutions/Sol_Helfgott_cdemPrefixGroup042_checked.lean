-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup042_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T02:48:05.415497+00:00
-- url     : https://prove2.me/submissions/3ea76ca0-bb44-46c1-b222-0e8f090bec5e

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
private theorem cdemPrefixStats_172032_172096 :
    (∑ n ∈ Ico 172032 172096, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 172032 172096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 172032 172096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-261460 : ℤ) ∧
    (∑ n ∈ Ico 172032 172096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5229335133459780892086628070 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_172096_172160 :
    (∑ n ∈ Ico 172096 172160, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 172096 172160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 172096 172160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (261413 : ℤ) ∧
    (∑ n ∈ Ico 172096 172160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5228289121876880093268558731 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_172032_172160 :
    (∑ n ∈ Ico 172032 172160, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 172032 172160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 172032 172160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-47 : ℤ) ∧
    (∑ n ∈ Ico 172032 172160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1046011582900798818069339 : ℤ) := by
  rcases cdemPrefixStats_172032_172096 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_172096_172160 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 172032 ≤ 172096) (by norm_num : 172096 ≤ 172160), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 172032 ≤ 172096) (by norm_num : 172096 ≤ 172160), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 172032 ≤ 172096) (by norm_num : 172096 ≤ 172160), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 172032 ≤ 172096) (by norm_num : 172096 ≤ 172160), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_172160_172224 :
    (∑ n ∈ Ico 172160 172224, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 172160 172224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 172160 172224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-58062 : ℤ) ∧
    (∑ n ∈ Ico 172160 172224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1161254748881129524005164056 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_172224_172288 :
    (∑ n ∈ Ico 172224 172288, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 172224 172288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 172224 172288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (290268 : ℤ) ∧
    (∑ n ∈ Ico 172224 172288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5805458083674523768616405835 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_172160_172288 :
    (∑ n ∈ Ico 172160 172288, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 172160 172288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 172160 172288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (232206 : ℤ) ∧
    (∑ n ∈ Ico 172160 172288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4644203334793394244611241779 : ℤ) := by
  rcases cdemPrefixStats_172160_172224 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_172224_172288 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 172160 ≤ 172224) (by norm_num : 172224 ≤ 172288), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 172160 ≤ 172224) (by norm_num : 172224 ≤ 172288), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 172160 ≤ 172224) (by norm_num : 172224 ≤ 172288), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 172160 ≤ 172224) (by norm_num : 172224 ≤ 172288), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_172032_172288 :
    (∑ n ∈ Ico 172032 172288, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 172032 172288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 172032 172288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (232159 : ℤ) ∧
    (∑ n ∈ Ico 172032 172288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4643157323210493445793172440 : ℤ) := by
  rcases cdemPrefixStats_172032_172160 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_172160_172288 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 172032 ≤ 172160) (by norm_num : 172160 ≤ 172288), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 172032 ≤ 172160) (by norm_num : 172160 ≤ 172288), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 172032 ≤ 172160) (by norm_num : 172160 ≤ 172288), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 172032 ≤ 172160) (by norm_num : 172160 ≤ 172288), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_172288_172352 :
    (∑ n ∈ Ico 172288 172352, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 172288 172352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 172288 172352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-232131 : ℤ) ∧
    (∑ n ∈ Ico 172288 172352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4642731006892918358037528530 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_172352_172416 :
    (∑ n ∈ Ico 172352 172416, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 172352 172416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 172352 172416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (116031 : ℤ) ∧
    (∑ n ∈ Ico 172352 172416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2320710640821118035203081566 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_172288_172416 :
    (∑ n ∈ Ico 172288 172416, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 172288 172416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 172288 172416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-116100 : ℤ) ∧
    (∑ n ∈ Ico 172288 172416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2322020366071800322834446964 : ℤ) := by
  rcases cdemPrefixStats_172288_172352 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_172352_172416 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 172288 ≤ 172352) (by norm_num : 172352 ≤ 172416), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 172288 ≤ 172352) (by norm_num : 172352 ≤ 172416), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 172288 ≤ 172352) (by norm_num : 172352 ≤ 172416), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 172288 ≤ 172352) (by norm_num : 172352 ≤ 172416), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_172416_172480 :
    (∑ n ∈ Ico 172416 172480, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 172416 172480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 172416 172480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (28969 : ℤ) ∧
    (∑ n ∈ Ico 172416 172480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (579350346208516045223983350 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_172480_172544 :
    (∑ n ∈ Ico 172480 172544, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 172480 172544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 172480 172544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-57961 : ℤ) ∧
    (∑ n ∈ Ico 172480 172544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1159252255358977292603116735 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_172416_172544 :
    (∑ n ∈ Ico 172416 172544, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 172416 172544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 172416 172544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-28992 : ℤ) ∧
    (∑ n ∈ Ico 172416 172544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-579901909150461247379133385 : ℤ) := by
  rcases cdemPrefixStats_172416_172480 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_172480_172544 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 172416 ≤ 172480) (by norm_num : 172480 ≤ 172544), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 172416 ≤ 172480) (by norm_num : 172480 ≤ 172544), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 172416 ≤ 172480) (by norm_num : 172480 ≤ 172544), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 172416 ≤ 172480) (by norm_num : 172480 ≤ 172544), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_172288_172544 :
    (∑ n ∈ Ico 172288 172544, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 172288 172544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 172288 172544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-145092 : ℤ) ∧
    (∑ n ∈ Ico 172288 172544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2901922275222261570213580349 : ℤ) := by
  rcases cdemPrefixStats_172288_172416 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_172416_172544 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 172288 ≤ 172416) (by norm_num : 172416 ≤ 172544), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 172288 ≤ 172416) (by norm_num : 172416 ≤ 172544), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 172288 ≤ 172416) (by norm_num : 172416 ≤ 172544), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 172288 ≤ 172416) (by norm_num : 172416 ≤ 172544), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_172032_172544 :
    (∑ n ∈ Ico 172032 172544, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 172032 172544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 172032 172544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (87067 : ℤ) ∧
    (∑ n ∈ Ico 172032 172544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1741235047988231875579592091 : ℤ) := by
  rcases cdemPrefixStats_172032_172288 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_172288_172544 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 172032 ≤ 172288) (by norm_num : 172288 ≤ 172544), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 172032 ≤ 172288) (by norm_num : 172288 ≤ 172544), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 172032 ≤ 172288) (by norm_num : 172288 ≤ 172544), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 172032 ≤ 172288) (by norm_num : 172288 ≤ 172544), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_172544_172608 :
    (∑ n ∈ Ico 172544 172608, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 172544 172608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 172544 172608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-173834 : ℤ) ∧
    (∑ n ∈ Ico 172544 172608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3476722442580898373457430448 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_172608_172672 :
    (∑ n ∈ Ico 172608 172672, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 172608 172672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 172608 172672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (86899 : ℤ) ∧
    (∑ n ∈ Ico 172608 172672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1737985243561761049934799124 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_172544_172672 :
    (∑ n ∈ Ico 172544 172672, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 172544 172672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 172544 172672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-86935 : ℤ) ∧
    (∑ n ∈ Ico 172544 172672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1738737199019137323522631324 : ℤ) := by
  rcases cdemPrefixStats_172544_172608 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_172608_172672 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 172544 ≤ 172608) (by norm_num : 172608 ≤ 172672), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 172544 ≤ 172608) (by norm_num : 172608 ≤ 172672), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 172544 ≤ 172608) (by norm_num : 172608 ≤ 172672), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 172544 ≤ 172608) (by norm_num : 172608 ≤ 172672), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_172672_172736 :
    (∑ n ∈ Ico 172672 172736, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 172672 172736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 172672 172736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (173706 : ℤ) ∧
    (∑ n ∈ Ico 172672 172736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3474222713835564791580588803 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_172736_172800 :
    (∑ n ∈ Ico 172736 172800, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 172736 172800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 172736 172800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (86820 : ℤ) ∧
    (∑ n ∈ Ico 172736 172800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1736436049489656522411617449 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_172672_172800 :
    (∑ n ∈ Ico 172672 172800, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 172672 172800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 172672 172800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (260526 : ℤ) ∧
    (∑ n ∈ Ico 172672 172800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5210658763325221313992206252 : ℤ) := by
  rcases cdemPrefixStats_172672_172736 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_172736_172800 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 172672 ≤ 172736) (by norm_num : 172736 ≤ 172800), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 172672 ≤ 172736) (by norm_num : 172736 ≤ 172800), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 172672 ≤ 172736) (by norm_num : 172736 ≤ 172800), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 172672 ≤ 172736) (by norm_num : 172736 ≤ 172800), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_172544_172800 :
    (∑ n ∈ Ico 172544 172800, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 172544 172800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 172544 172800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (173591 : ℤ) ∧
    (∑ n ∈ Ico 172544 172800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3471921564306083990469574928 : ℤ) := by
  rcases cdemPrefixStats_172544_172672 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_172672_172800 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 172544 ≤ 172672) (by norm_num : 172672 ≤ 172800), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 172544 ≤ 172672) (by norm_num : 172672 ≤ 172800), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 172544 ≤ 172672) (by norm_num : 172672 ≤ 172800), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 172544 ≤ 172672) (by norm_num : 172672 ≤ 172800), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_172800_172864 :
    (∑ n ∈ Ico 172800 172864, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 172800 172864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 172800 172864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-231402 : ℤ) ∧
    (∑ n ∈ Ico 172800 172864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4628136438566424932524001375 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_172864_172928 :
    (∑ n ∈ Ico 172864 172928, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 172864 172928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 172864 172928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (28924 : ℤ) ∧
    (∑ n ∈ Ico 172864 172928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (578559692639475936067190637 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_172800_172928 :
    (∑ n ∈ Ico 172800 172928, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 172800 172928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 172800 172928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-202478 : ℤ) ∧
    (∑ n ∈ Ico 172800 172928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4049576745926948996456810738 : ℤ) := by
  rcases cdemPrefixStats_172800_172864 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_172864_172928 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 172800 ≤ 172864) (by norm_num : 172864 ≤ 172928), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 172800 ≤ 172864) (by norm_num : 172864 ≤ 172928), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 172800 ≤ 172864) (by norm_num : 172864 ≤ 172928), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 172800 ≤ 172864) (by norm_num : 172864 ≤ 172928), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_172928_172992 :
    (∑ n ∈ Ico 172928 172992, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 172928 172992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 172928 172992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-86726 : ℤ) ∧
    (∑ n ∈ Ico 172928 172992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1734558697824549233914723805 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_172992_173056 :
    (∑ n ∈ Ico 172992 173056, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 172992 173056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 172992 173056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (57800 : ℤ) ∧
    (∑ n ∈ Ico 172992 173056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1156002546483964023101972519 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_172928_173056 :
    (∑ n ∈ Ico 172928 173056, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 172928 173056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 172928 173056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-28926 : ℤ) ∧
    (∑ n ∈ Ico 172928 173056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-578556151340585210812751286 : ℤ) := by
  rcases cdemPrefixStats_172928_172992 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_172992_173056 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 172928 ≤ 172992) (by norm_num : 172992 ≤ 173056), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 172928 ≤ 172992) (by norm_num : 172992 ≤ 173056), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 172928 ≤ 172992) (by norm_num : 172992 ≤ 173056), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 172928 ≤ 172992) (by norm_num : 172992 ≤ 173056), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_172800_173056 :
    (∑ n ∈ Ico 172800 173056, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 172800 173056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 172800 173056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-231404 : ℤ) ∧
    (∑ n ∈ Ico 172800 173056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4628132897267534207269562024 : ℤ) := by
  rcases cdemPrefixStats_172800_172928 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_172928_173056 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 172800 ≤ 172928) (by norm_num : 172928 ≤ 173056), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 172800 ≤ 172928) (by norm_num : 172928 ≤ 173056), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 172800 ≤ 172928) (by norm_num : 172928 ≤ 173056), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 172800 ≤ 172928) (by norm_num : 172928 ≤ 173056), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_172544_173056 :
    (∑ n ∈ Ico 172544 173056, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 172544 173056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 172544 173056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-57813 : ℤ) ∧
    (∑ n ∈ Ico 172544 173056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1156211332961450216799987096 : ℤ) := by
  rcases cdemPrefixStats_172544_172800 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_172800_173056 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 172544 ≤ 172800) (by norm_num : 172800 ≤ 173056), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 172544 ≤ 172800) (by norm_num : 172800 ≤ 173056), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 172544 ≤ 172800) (by norm_num : 172800 ≤ 173056), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 172544 ≤ 172800) (by norm_num : 172800 ≤ 173056), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_172032_173056 :
    (∑ n ∈ Ico 172032 173056, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 172032 173056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (623 : ℕ) ∧
    (∑ n ∈ Ico 172032 173056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (29254 : ℤ) ∧
    (∑ n ∈ Ico 172032 173056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (585023715026781658779604995 : ℤ) := by
  rcases cdemPrefixStats_172032_172544 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_172544_173056 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 172032 ≤ 172544) (by norm_num : 172544 ≤ 173056), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 172032 ≤ 172544) (by norm_num : 172544 ≤ 173056), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 172032 ≤ 172544) (by norm_num : 172544 ≤ 173056), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 172032 ≤ 172544) (by norm_num : 172544 ≤ 173056), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_173056_173120 :
    (∑ n ∈ Ico 173056 173120, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 173056 173120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 173056 173120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (86681 : ℤ) ∧
    (∑ n ∈ Ico 173056 173120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1733693079933195095048635938 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_173120_173184 :
    (∑ n ∈ Ico 173120 173184, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 173120 173184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 173120 173184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (57764 : ℤ) ∧
    (∑ n ∈ Ico 173120 173184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1155361396765502989230441228 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_173056_173184 :
    (∑ n ∈ Ico 173056 173184, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 173056 173184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 173056 173184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (144445 : ℤ) ∧
    (∑ n ∈ Ico 173056 173184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2889054476698698084279077166 : ℤ) := by
  rcases cdemPrefixStats_173056_173120 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_173120_173184 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 173056 ≤ 173120) (by norm_num : 173120 ≤ 173184), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 173056 ≤ 173120) (by norm_num : 173120 ≤ 173184), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 173056 ≤ 173120) (by norm_num : 173120 ≤ 173184), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 173056 ≤ 173120) (by norm_num : 173120 ≤ 173184), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_173184_173248 :
    (∑ n ∈ Ico 173184 173248, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 173184 173248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 173184 173248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-57 : ℤ) ∧
    (∑ n ∈ Ico 173184 173248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1113162440930394001046902 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_173248_173312 :
    (∑ n ∈ Ico 173248 173312, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 173248 173312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 173248 173312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-288521 : ℤ) ∧
    (∑ n ∈ Ico 173248 173312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5770480289764413622052185433 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_173184_173312 :
    (∑ n ∈ Ico 173184 173312, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 173184 173312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (82 : ℕ) ∧
    (∑ n ∈ Ico 173184 173312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-288578 : ℤ) ∧
    (∑ n ∈ Ico 173184 173312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5771593452205344016053232335 : ℤ) := by
  rcases cdemPrefixStats_173184_173248 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_173248_173312 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 173184 ≤ 173248) (by norm_num : 173248 ≤ 173312), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 173184 ≤ 173248) (by norm_num : 173248 ≤ 173312), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 173184 ≤ 173248) (by norm_num : 173248 ≤ 173312), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 173184 ≤ 173248) (by norm_num : 173248 ≤ 173312), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_173056_173312 :
    (∑ n ∈ Ico 173056 173312, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 173056 173312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (159 : ℕ) ∧
    (∑ n ∈ Ico 173056 173312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-144133 : ℤ) ∧
    (∑ n ∈ Ico 173056 173312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2882538975506645931774155169 : ℤ) := by
  rcases cdemPrefixStats_173056_173184 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_173184_173312 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 173056 ≤ 173184) (by norm_num : 173184 ≤ 173312), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 173056 ≤ 173184) (by norm_num : 173184 ≤ 173312), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 173056 ≤ 173184) (by norm_num : 173184 ≤ 173312), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 173056 ≤ 173184) (by norm_num : 173184 ≤ 173312), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_173312_173376 :
    (∑ n ∈ Ico 173312 173376, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 173312 173376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 173312 173376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (115351 : ℤ) ∧
    (∑ n ∈ Ico 173312 173376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2307071096169859336345759230 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_173376_173440 :
    (∑ n ∈ Ico 173376 173440, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 173376 173440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 173376 173440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (288359 : ℤ) ∧
    (∑ n ∈ Ico 173376 173440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5767325383850638137933670913 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_173312_173440 :
    (∑ n ∈ Ico 173312 173440, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 173312 173440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 173312 173440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (403710 : ℤ) ∧
    (∑ n ∈ Ico 173312 173440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8074396480020497474279430143 : ℤ) := by
  rcases cdemPrefixStats_173312_173376 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_173376_173440 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 173312 ≤ 173376) (by norm_num : 173376 ≤ 173440), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 173312 ≤ 173376) (by norm_num : 173376 ≤ 173440), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 173312 ≤ 173376) (by norm_num : 173376 ≤ 173440), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 173312 ≤ 173376) (by norm_num : 173376 ≤ 173440), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_173440_173504 :
    (∑ n ∈ Ico 173440 173504, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 173440 173504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 173440 173504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (57687 : ℤ) ∧
    (∑ n ∈ Ico 173440 173504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1153764594413300501939920922 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_173504_173568 :
    (∑ n ∈ Ico 173504 173568, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 173504 173568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 173504 173568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-28816 : ℤ) ∧
    (∑ n ∈ Ico 173504 173568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-576252593408919124753418202 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_173440_173568 :
    (∑ n ∈ Ico 173440 173568, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 173440 173568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 173440 173568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (28871 : ℤ) ∧
    (∑ n ∈ Ico 173440 173568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (577512001004381377186502720 : ℤ) := by
  rcases cdemPrefixStats_173440_173504 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_173504_173568 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 173440 ≤ 173504) (by norm_num : 173504 ≤ 173568), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 173440 ≤ 173504) (by norm_num : 173504 ≤ 173568), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 173440 ≤ 173504) (by norm_num : 173504 ≤ 173568), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 173440 ≤ 173504) (by norm_num : 173504 ≤ 173568), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_173312_173568 :
    (∑ n ∈ Ico 173312 173568, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 173312 173568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 173312 173568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (432581 : ℤ) ∧
    (∑ n ∈ Ico 173312 173568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8651908481024878851465932863 : ℤ) := by
  rcases cdemPrefixStats_173312_173440 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_173440_173568 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 173312 ≤ 173440) (by norm_num : 173440 ≤ 173568), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 173312 ≤ 173440) (by norm_num : 173440 ≤ 173568), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 173312 ≤ 173440) (by norm_num : 173440 ≤ 173568), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 173312 ≤ 173440) (by norm_num : 173440 ≤ 173568), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_173056_173568 :
    (∑ n ∈ Ico 173056 173568, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 173056 173568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (314 : ℕ) ∧
    (∑ n ∈ Ico 173056 173568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (288448 : ℤ) ∧
    (∑ n ∈ Ico 173056 173568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5769369505518232919691777694 : ℤ) := by
  rcases cdemPrefixStats_173056_173312 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_173312_173568 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 173056 ≤ 173312) (by norm_num : 173312 ≤ 173568), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 173056 ≤ 173312) (by norm_num : 173312 ≤ 173568), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 173056 ≤ 173312) (by norm_num : 173312 ≤ 173568), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 173056 ≤ 173312) (by norm_num : 173312 ≤ 173568), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_173568_173632 :
    (∑ n ∈ Ico 173568 173632, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 173568 173632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 173568 173632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-57613 : ℤ) ∧
    (∑ n ∈ Ico 173568 173632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1152306043157192578139952228 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_173632_173696 :
    (∑ n ∈ Ico 173632 173696, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 173632 173696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 173632 173696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-143928 : ℤ) ∧
    (∑ n ∈ Ico 173632 173696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2878585733266290220884132031 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_173568_173696 :
    (∑ n ∈ Ico 173568 173696, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 173568 173696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 173568 173696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-201541 : ℤ) ∧
    (∑ n ∈ Ico 173568 173696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4030891776423482799024084259 : ℤ) := by
  rcases cdemPrefixStats_173568_173632 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_173632_173696 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 173568 ≤ 173632) (by norm_num : 173632 ≤ 173696), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 173568 ≤ 173632) (by norm_num : 173632 ≤ 173696), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 173568 ≤ 173632) (by norm_num : 173632 ≤ 173696), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 173568 ≤ 173632) (by norm_num : 173632 ≤ 173696), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_173696_173760 :
    (∑ n ∈ Ico 173696 173760, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 173696 173760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 173696 173760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (287796 : ℤ) ∧
    (∑ n ∈ Ico 173696 173760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5756021920826464641254101307 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_173760_173824 :
    (∑ n ∈ Ico 173760 173824, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 173760 173824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 173760 173824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-172629 : ℤ) ∧
    (∑ n ∈ Ico 173760 173824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3452667807420830053426467584 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_173696_173824 :
    (∑ n ∈ Ico 173696 173824, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 173696 173824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 173696 173824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (115167 : ℤ) ∧
    (∑ n ∈ Ico 173696 173824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2303354113405634587827633723 : ℤ) := by
  rcases cdemPrefixStats_173696_173760 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_173760_173824 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 173696 ≤ 173760) (by norm_num : 173760 ≤ 173824), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 173696 ≤ 173760) (by norm_num : 173760 ≤ 173824), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 173696 ≤ 173760) (by norm_num : 173760 ≤ 173824), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 173696 ≤ 173760) (by norm_num : 173760 ≤ 173824), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_173568_173824 :
    (∑ n ∈ Ico 173568 173824, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 173568 173824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 173568 173824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-86374 : ℤ) ∧
    (∑ n ∈ Ico 173568 173824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1727537663017848211196450536 : ℤ) := by
  rcases cdemPrefixStats_173568_173696 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_173696_173824 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 173568 ≤ 173696) (by norm_num : 173696 ≤ 173824), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 173568 ≤ 173696) (by norm_num : 173696 ≤ 173824), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 173568 ≤ 173696) (by norm_num : 173696 ≤ 173824), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 173568 ≤ 173696) (by norm_num : 173696 ≤ 173824), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_173824_173888 :
    (∑ n ∈ Ico 173824 173888, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 173824 173888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 173824 173888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 173824 173888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-43034981146633888221816 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_173888_173952 :
    (∑ n ∈ Ico 173888 173952, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 173888 173952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 173888 173952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-201258 : ℤ) ∧
    (∑ n ∈ Ico 173888 173952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4025222553578266291182705590 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_173824_173952 :
    (∑ n ∈ Ico 173824 173952, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 173824 173952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 173824 173952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-201261 : ℤ) ∧
    (∑ n ∈ Ico 173824 173952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4025265588559412925070927406 : ℤ) := by
  rcases cdemPrefixStats_173824_173888 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_173888_173952 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 173824 ≤ 173888) (by norm_num : 173888 ≤ 173952), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 173824 ≤ 173888) (by norm_num : 173888 ≤ 173952), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 173824 ≤ 173888) (by norm_num : 173888 ≤ 173952), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 173824 ≤ 173888) (by norm_num : 173888 ≤ 173952), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_173952_174016 :
    (∑ n ∈ Ico 173952 174016, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 173952 174016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 173952 174016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (28745 : ℤ) ∧
    (∑ n ∈ Ico 173952 174016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (574943873688475353223508321 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_174016_174080 :
    (∑ n ∈ Ico 174016 174080, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 174016 174080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 174016 174080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-172343 : ℤ) ∧
    (∑ n ∈ Ico 174016 174080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3446922186594634342626367347 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_173952_174080 :
    (∑ n ∈ Ico 173952 174080, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 173952 174080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 173952 174080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-143598 : ℤ) ∧
    (∑ n ∈ Ico 173952 174080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2871978312906158989402859026 : ℤ) := by
  rcases cdemPrefixStats_173952_174016 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_174016_174080 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 173952 ≤ 174016) (by norm_num : 174016 ≤ 174080), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 173952 ≤ 174016) (by norm_num : 174016 ≤ 174080), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 173952 ≤ 174016) (by norm_num : 174016 ≤ 174080), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 173952 ≤ 174016) (by norm_num : 174016 ≤ 174080), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_173824_174080 :
    (∑ n ∈ Ico 173824 174080, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 173824 174080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 173824 174080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-344859 : ℤ) ∧
    (∑ n ∈ Ico 173824 174080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6897243901465571914473786432 : ℤ) := by
  rcases cdemPrefixStats_173824_173952 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_173952_174080 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 173824 ≤ 173952) (by norm_num : 173952 ≤ 174080), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 173824 ≤ 173952) (by norm_num : 173952 ≤ 174080), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 173824 ≤ 173952) (by norm_num : 173952 ≤ 174080), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 173824 ≤ 173952) (by norm_num : 173952 ≤ 174080), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_173568_174080 :
    (∑ n ∈ Ico 173568 174080, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 173568 174080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 173568 174080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-431233 : ℤ) ∧
    (∑ n ∈ Ico 173568 174080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8624781564483420125670236968 : ℤ) := by
  rcases cdemPrefixStats_173568_173824 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_173824_174080 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 173568 ≤ 173824) (by norm_num : 173824 ≤ 174080), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 173568 ≤ 173824) (by norm_num : 173824 ≤ 174080), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 173568 ≤ 173824) (by norm_num : 173824 ≤ 174080), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 173568 ≤ 173824) (by norm_num : 173824 ≤ 174080), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_173056_174080 :
    (∑ n ∈ Ico 173056 174080, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 173056 174080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (623 : ℕ) ∧
    (∑ n ∈ Ico 173056 174080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-142785 : ℤ) ∧
    (∑ n ∈ Ico 173056 174080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2855412058965187205978459274 : ℤ) := by
  rcases cdemPrefixStats_173056_173568 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_173568_174080 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 173056 ≤ 173568) (by norm_num : 173568 ≤ 174080), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 173056 ≤ 173568) (by norm_num : 173568 ≤ 174080), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 173056 ≤ 173568) (by norm_num : 173568 ≤ 174080), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 173056 ≤ 173568) (by norm_num : 173568 ≤ 174080), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_172032_174080 :
    (∑ n ∈ Ico 172032 174080, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 172032 174080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1246 : ℕ) ∧
    (∑ n ∈ Ico 172032 174080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-113531 : ℤ) ∧
    (∑ n ∈ Ico 172032 174080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2270388343938405547198854279 : ℤ) := by
  rcases cdemPrefixStats_172032_173056 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_173056_174080 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 172032 ≤ 173056) (by norm_num : 173056 ≤ 174080), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 172032 ≤ 173056) (by norm_num : 173056 ≤ 174080), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 172032 ≤ 173056) (by norm_num : 173056 ≤ 174080), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 172032 ≤ 173056) (by norm_num : 173056 ≤ 174080), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_174080_174144 :
    (∑ n ∈ Ico 174080 174144, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 174080 174144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 174080 174144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-172284 : ℤ) ∧
    (∑ n ∈ Ico 174080 174144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3445750946513239408590025670 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_174144_174208 :
    (∑ n ∈ Ico 174144 174208, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 174144 174208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 174144 174208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-57443 : ℤ) ∧
    (∑ n ∈ Ico 174144 174208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1148863742531333706812893596 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_174080_174208 :
    (∑ n ∈ Ico 174080 174208, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 174080 174208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 174080 174208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-229727 : ℤ) ∧
    (∑ n ∈ Ico 174080 174208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4594614689044573115402919266 : ℤ) := by
  rcases cdemPrefixStats_174080_174144 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_174144_174208 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 174080 ≤ 174144) (by norm_num : 174144 ≤ 174208), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 174080 ≤ 174144) (by norm_num : 174144 ≤ 174208), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 174080 ≤ 174144) (by norm_num : 174144 ≤ 174208), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 174080 ≤ 174144) (by norm_num : 174144 ≤ 174208), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_174208_174272 :
    (∑ n ∈ Ico 174208 174272, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 174208 174272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 174208 174272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (86087 : ℤ) ∧
    (∑ n ∈ Ico 174208 174272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1721786163866269997422493930 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_174272_174336 :
    (∑ n ∈ Ico 174272 174336, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 174272 174336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 174272 174336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (9 : ℤ) ∧
    (∑ n ∈ Ico 174272 174336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (164570127634879876299343 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_174208_174336 :
    (∑ n ∈ Ico 174208 174336, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 174208 174336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 174208 174336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (86096 : ℤ) ∧
    (∑ n ∈ Ico 174208 174336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1721950733993904877298793273 : ℤ) := by
  rcases cdemPrefixStats_174208_174272 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_174272_174336 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 174208 ≤ 174272) (by norm_num : 174272 ≤ 174336), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 174208 ≤ 174272) (by norm_num : 174272 ≤ 174336), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 174208 ≤ 174272) (by norm_num : 174272 ≤ 174336), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 174208 ≤ 174272) (by norm_num : 174272 ≤ 174336), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_174080_174336 :
    (∑ n ∈ Ico 174080 174336, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 174080 174336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 174080 174336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-143631 : ℤ) ∧
    (∑ n ∈ Ico 174080 174336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2872663955050668238104125993 : ℤ) := by
  rcases cdemPrefixStats_174080_174208 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_174208_174336 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 174080 ≤ 174208) (by norm_num : 174208 ≤ 174336), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 174080 ≤ 174208) (by norm_num : 174208 ≤ 174336), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 174080 ≤ 174208) (by norm_num : 174208 ≤ 174336), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 174080 ≤ 174208) (by norm_num : 174208 ≤ 174336), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_174336_174400 :
    (∑ n ∈ Ico 174336 174400, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 174336 174400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 174336 174400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (57358 : ℤ) ∧
    (∑ n ∈ Ico 174336 174400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1147153995156119003620355680 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_174400_174464 :
    (∑ n ∈ Ico 174400 174464, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 174400 174464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 174400 174464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (200635 : ℤ) ∧
    (∑ n ∈ Ico 174400 174464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4012716246874848485671547780 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_174336_174464 :
    (∑ n ∈ Ico 174336 174464, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 174336 174464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 174336 174464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (257993 : ℤ) ∧
    (∑ n ∈ Ico 174336 174464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5159870242030967489291903460 : ℤ) := by
  rcases cdemPrefixStats_174336_174400 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_174400_174464 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 174336 ≤ 174400) (by norm_num : 174400 ≤ 174464), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 174336 ≤ 174400) (by norm_num : 174400 ≤ 174464), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 174336 ≤ 174400) (by norm_num : 174400 ≤ 174464), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 174336 ≤ 174400) (by norm_num : 174400 ≤ 174464), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_174464_174528 :
    (∑ n ∈ Ico 174464 174528, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 174464 174528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 174464 174528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-85970 : ℤ) ∧
    (∑ n ∈ Ico 174464 174528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1719407933724460567206385972 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_174528_174592 :
    (∑ n ∈ Ico 174528 174592, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 174528 174592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 174528 174592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 174528 174592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-167399755104440006864493 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_174464_174592 :
    (∑ n ∈ Ico 174464 174592, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 174464 174592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (73 : ℕ) ∧
    (∑ n ∈ Ico 174464 174592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-85979 : ℤ) ∧
    (∑ n ∈ Ico 174464 174592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1719575333479565007213250465 : ℤ) := by
  rcases cdemPrefixStats_174464_174528 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_174528_174592 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 174464 ≤ 174528) (by norm_num : 174528 ≤ 174592), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 174464 ≤ 174528) (by norm_num : 174528 ≤ 174592), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 174464 ≤ 174528) (by norm_num : 174528 ≤ 174592), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 174464 ≤ 174528) (by norm_num : 174528 ≤ 174592), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_174336_174592 :
    (∑ n ∈ Ico 174336 174592, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 174336 174592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 174336 174592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (172014 : ℤ) ∧
    (∑ n ∈ Ico 174336 174592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3440294908551402482078652995 : ℤ) := by
  rcases cdemPrefixStats_174336_174464 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_174464_174592 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 174336 ≤ 174464) (by norm_num : 174464 ≤ 174592), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 174336 ≤ 174464) (by norm_num : 174464 ≤ 174592), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 174336 ≤ 174464) (by norm_num : 174464 ≤ 174592), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 174336 ≤ 174464) (by norm_num : 174464 ≤ 174592), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_174080_174592 :
    (∑ n ∈ Ico 174080 174592, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 174080 174592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 174080 174592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (28383 : ℤ) ∧
    (∑ n ∈ Ico 174080 174592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (567630953500734243974527002 : ℤ) := by
  rcases cdemPrefixStats_174080_174336 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_174336_174592 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 174080 ≤ 174336) (by norm_num : 174336 ≤ 174592), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 174080 ≤ 174336) (by norm_num : 174336 ≤ 174592), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 174080 ≤ 174336) (by norm_num : 174336 ≤ 174592), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 174080 ≤ 174336) (by norm_num : 174336 ≤ 174592), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_174592_174656 :
    (∑ n ∈ Ico 174592 174656, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 174592 174656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 174592 174656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (114553 : ℤ) ∧
    (∑ n ∈ Ico 174592 174656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2291085200864798495531466980 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_174656_174720 :
    (∑ n ∈ Ico 174656 174720, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 174656 174720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 174656 174720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (85860 : ℤ) ∧
    (∑ n ∈ Ico 174656 174720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1717216413713743611335881702 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_174592_174720 :
    (∑ n ∈ Ico 174592 174720, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 174592 174720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 174592 174720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (200413 : ℤ) ∧
    (∑ n ∈ Ico 174592 174720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4008301614578542106867348682 : ℤ) := by
  rcases cdemPrefixStats_174592_174656 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_174656_174720 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 174592 ≤ 174656) (by norm_num : 174656 ≤ 174720), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 174592 ≤ 174656) (by norm_num : 174656 ≤ 174720), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 174592 ≤ 174656) (by norm_num : 174656 ≤ 174720), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 174592 ≤ 174656) (by norm_num : 174656 ≤ 174720), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_174720_174784 :
    (∑ n ∈ Ico 174720 174784, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 174720 174784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 174720 174784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-200290 : ℤ) ∧
    (∑ n ∈ Ico 174720 174784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4005873150026920441239159150 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_174784_174848 :
    (∑ n ∈ Ico 174784 174848, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 174784 174848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 174784 174848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (143012 : ℤ) ∧
    (∑ n ∈ Ico 174784 174848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2860323558571297956636384456 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_174720_174848 :
    (∑ n ∈ Ico 174720 174848, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 174720 174848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 174720 174848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-57278 : ℤ) ∧
    (∑ n ∈ Ico 174720 174848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1145549591455622484602774694 : ℤ) := by
  rcases cdemPrefixStats_174720_174784 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_174784_174848 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 174720 ≤ 174784) (by norm_num : 174784 ≤ 174848), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 174720 ≤ 174784) (by norm_num : 174784 ≤ 174848), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 174720 ≤ 174784) (by norm_num : 174784 ≤ 174848), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 174720 ≤ 174784) (by norm_num : 174784 ≤ 174848), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_174592_174848 :
    (∑ n ∈ Ico 174592 174848, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 174592 174848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (159 : ℕ) ∧
    (∑ n ∈ Ico 174592 174848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (143135 : ℤ) ∧
    (∑ n ∈ Ico 174592 174848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2862752023122919622264573988 : ℤ) := by
  rcases cdemPrefixStats_174592_174720 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_174720_174848 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 174592 ≤ 174720) (by norm_num : 174720 ≤ 174848), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 174592 ≤ 174720) (by norm_num : 174720 ≤ 174848), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 174592 ≤ 174720) (by norm_num : 174720 ≤ 174848), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 174592 ≤ 174720) (by norm_num : 174720 ≤ 174848), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_174848_174912 :
    (∑ n ∈ Ico 174848 174912, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 174848 174912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 174848 174912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-114340 : ℤ) ∧
    (∑ n ∈ Ico 174848 174912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2286779200215077039903009032 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_174912_174976 :
    (∑ n ∈ Ico 174912 174976, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 174912 174976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 174912 174976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-171495 : ℤ) ∧
    (∑ n ∈ Ico 174912 174976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3429949964784711832893660347 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_174848_174976 :
    (∑ n ∈ Ico 174848 174976, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 174848 174976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 174848 174976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-285835 : ℤ) ∧
    (∑ n ∈ Ico 174848 174976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5716729164999788872796669379 : ℤ) := by
  rcases cdemPrefixStats_174848_174912 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_174912_174976 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 174848 ≤ 174912) (by norm_num : 174912 ≤ 174976), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 174848 ≤ 174912) (by norm_num : 174912 ≤ 174976), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 174848 ≤ 174912) (by norm_num : 174912 ≤ 174976), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 174848 ≤ 174912) (by norm_num : 174912 ≤ 174976), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_174976_175040 :
    (∑ n ∈ Ico 174976 175040, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 174976 175040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 174976 175040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (85694 : ℤ) ∧
    (∑ n ∈ Ico 174976 175040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1713910313653801737370155558 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_175040_175104 :
    (∑ n ∈ Ico 175040 175104, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 175040 175104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 175040 175104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (28561 : ℤ) ∧
    (∑ n ∈ Ico 175040 175104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (571255571846416020426097251 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_174976_175104 :
    (∑ n ∈ Ico 174976 175104, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 174976 175104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 174976 175104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (114255 : ℤ) ∧
    (∑ n ∈ Ico 174976 175104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2285165885500217757796252809 : ℤ) := by
  rcases cdemPrefixStats_174976_175040 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_175040_175104 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 174976 ≤ 175040) (by norm_num : 175040 ≤ 175104), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 174976 ≤ 175040) (by norm_num : 175040 ≤ 175104), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 174976 ≤ 175040) (by norm_num : 175040 ≤ 175104), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 174976 ≤ 175040) (by norm_num : 175040 ≤ 175104), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_174848_175104 :
    (∑ n ∈ Ico 174848 175104, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 174848 175104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 174848 175104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-171580 : ℤ) ∧
    (∑ n ∈ Ico 174848 175104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3431563279499571115000416570 : ℤ) := by
  rcases cdemPrefixStats_174848_174976 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_174976_175104 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 174848 ≤ 174976) (by norm_num : 174976 ≤ 175104), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 174848 ≤ 174976) (by norm_num : 174976 ≤ 175104), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 174848 ≤ 174976) (by norm_num : 174976 ≤ 175104), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 174848 ≤ 174976) (by norm_num : 174976 ≤ 175104), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_174592_175104 :
    (∑ n ∈ Ico 174592 175104, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 174592 175104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 174592 175104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-28445 : ℤ) ∧
    (∑ n ∈ Ico 174592 175104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-568811256376651492735842582 : ℤ) := by
  rcases cdemPrefixStats_174592_174848 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_174848_175104 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 174592 ≤ 174848) (by norm_num : 174848 ≤ 175104), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 174592 ≤ 174848) (by norm_num : 174848 ≤ 175104), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 174592 ≤ 174848) (by norm_num : 174848 ≤ 175104), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 174592 ≤ 174848) (by norm_num : 174848 ≤ 175104), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_174080_175104 :
    (∑ n ∈ Ico 174080 175104, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 174080 175104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (622 : ℕ) ∧
    (∑ n ∈ Ico 174080 175104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-62 : ℤ) ∧
    (∑ n ∈ Ico 174080 175104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1180302875917248761315580 : ℤ) := by
  rcases cdemPrefixStats_174080_174592 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_174592_175104 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 174080 ≤ 174592) (by norm_num : 174592 ≤ 175104), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 174080 ≤ 174592) (by norm_num : 174592 ≤ 175104), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 174080 ≤ 174592) (by norm_num : 174592 ≤ 175104), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 174080 ≤ 174592) (by norm_num : 174592 ≤ 175104), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_175104_175168 :
    (∑ n ∈ Ico 175104 175168, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 175104 175168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 175104 175168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (228410 : ℤ) ∧
    (∑ n ∈ Ico 175104 175168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4568292814249702002461140024 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_175168_175232 :
    (∑ n ∈ Ico 175168 175232, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 175168 175232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 175168 175232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (142722 : ℤ) ∧
    (∑ n ∈ Ico 175168 175232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2854523177790900565600338037 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_175104_175232 :
    (∑ n ∈ Ico 175104 175232, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 175104 175232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 175104 175232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (371132 : ℤ) ∧
    (∑ n ∈ Ico 175104 175232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7422815992040602568061478061 : ℤ) := by
  rcases cdemPrefixStats_175104_175168 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_175168_175232 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 175104 ≤ 175168) (by norm_num : 175168 ≤ 175232), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 175104 ≤ 175168) (by norm_num : 175168 ≤ 175232), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 175104 ≤ 175168) (by norm_num : 175168 ≤ 175232), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 175104 ≤ 175168) (by norm_num : 175168 ≤ 175232), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_175232_175296 :
    (∑ n ∈ Ico 175232 175296, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 175232 175296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 175232 175296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (342308 : ℤ) ∧
    (∑ n ∈ Ico 175232 175296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6846234522373608120499411261 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_175296_175360 :
    (∑ n ∈ Ico 175296 175360, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 175296 175360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 175296 175360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (114075 : ℤ) ∧
    (∑ n ∈ Ico 175296 175360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2281581382371975381670110492 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_175232_175360 :
    (∑ n ∈ Ico 175232 175360, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 175232 175360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 175232 175360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (456383 : ℤ) ∧
    (∑ n ∈ Ico 175232 175360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9127815904745583502169521753 : ℤ) := by
  rcases cdemPrefixStats_175232_175296 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_175296_175360 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 175232 ≤ 175296) (by norm_num : 175296 ≤ 175360), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 175232 ≤ 175296) (by norm_num : 175296 ≤ 175360), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 175232 ≤ 175296) (by norm_num : 175296 ≤ 175360), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 175232 ≤ 175296) (by norm_num : 175296 ≤ 175360), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_175104_175360 :
    (∑ n ∈ Ico 175104 175360, mobiusTreeValue 16 mobiusTable1200001 n) = (29 : ℤ) ∧
    (∑ n ∈ Ico 175104 175360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (159 : ℕ) ∧
    (∑ n ∈ Ico 175104 175360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (827515 : ℤ) ∧
    (∑ n ∈ Ico 175104 175360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (16550631896786186070230999814 : ℤ) := by
  rcases cdemPrefixStats_175104_175232 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_175232_175360 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 175104 ≤ 175232) (by norm_num : 175232 ≤ 175360), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 175104 ≤ 175232) (by norm_num : 175232 ≤ 175360), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 175104 ≤ 175232) (by norm_num : 175232 ≤ 175360), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 175104 ≤ 175232) (by norm_num : 175232 ≤ 175360), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_175360_175424 :
    (∑ n ∈ Ico 175360 175424, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 175360 175424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 175360 175424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-113994 : ℤ) ∧
    (∑ n ∈ Ico 175360 175424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2279952364949660413288162150 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_175424_175488 :
    (∑ n ∈ Ico 175424 175488, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 175424 175488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 175424 175488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (85479 : ℤ) ∧
    (∑ n ∈ Ico 175424 175488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1709596539548006693178356634 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_175360_175488 :
    (∑ n ∈ Ico 175360 175488, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 175360 175488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 175360 175488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-28515 : ℤ) ∧
    (∑ n ∈ Ico 175360 175488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-570355825401653720109805516 : ℤ) := by
  rcases cdemPrefixStats_175360_175424 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_175424_175488 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 175360 ≤ 175424) (by norm_num : 175424 ≤ 175488), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 175360 ≤ 175424) (by norm_num : 175424 ≤ 175488), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 175360 ≤ 175424) (by norm_num : 175424 ≤ 175488), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 175360 ≤ 175424) (by norm_num : 175424 ≤ 175488), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_175488_175552 :
    (∑ n ∈ Ico 175488 175552, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 175488 175552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 175488 175552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (199378 : ℤ) ∧
    (∑ n ∈ Ico 175488 175552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3987639924623807538294488702 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_175552_175616 :
    (∑ n ∈ Ico 175552 175616, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 175552 175616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 175552 175616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (341670 : ℤ) ∧
    (∑ n ∈ Ico 175552 175616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6833498891634778602371274222 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_175488_175616 :
    (∑ n ∈ Ico 175488 175616, mobiusTreeValue 16 mobiusTable1200001 n) = (19 : ℤ) ∧
    (∑ n ∈ Ico 175488 175616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 175488 175616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (541048 : ℤ) ∧
    (∑ n ∈ Ico 175488 175616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10821138816258586140665762924 : ℤ) := by
  rcases cdemPrefixStats_175488_175552 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_175552_175616 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 175488 ≤ 175552) (by norm_num : 175552 ≤ 175616), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 175488 ≤ 175552) (by norm_num : 175552 ≤ 175616), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 175488 ≤ 175552) (by norm_num : 175552 ≤ 175616), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 175488 ≤ 175552) (by norm_num : 175552 ≤ 175616), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_175360_175616 :
    (∑ n ∈ Ico 175360 175616, mobiusTreeValue 16 mobiusTable1200001 n) = (18 : ℤ) ∧
    (∑ n ∈ Ico 175360 175616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 175360 175616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (512533 : ℤ) ∧
    (∑ n ∈ Ico 175360 175616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10250782990856932420555957408 : ℤ) := by
  rcases cdemPrefixStats_175360_175488 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_175488_175616 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 175360 ≤ 175488) (by norm_num : 175488 ≤ 175616), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 175360 ≤ 175488) (by norm_num : 175488 ≤ 175616), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 175360 ≤ 175488) (by norm_num : 175488 ≤ 175616), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 175360 ≤ 175488) (by norm_num : 175488 ≤ 175616), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_175104_175616 :
    (∑ n ∈ Ico 175104 175616, mobiusTreeValue 16 mobiusTable1200001 n) = (47 : ℤ) ∧
    (∑ n ∈ Ico 175104 175616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (315 : ℕ) ∧
    (∑ n ∈ Ico 175104 175616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1340048 : ℤ) ∧
    (∑ n ∈ Ico 175104 175616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (26801414887643118490786957222 : ℤ) := by
  rcases cdemPrefixStats_175104_175360 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_175360_175616 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 175104 ≤ 175360) (by norm_num : 175360 ≤ 175616), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 175104 ≤ 175360) (by norm_num : 175360 ≤ 175616), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 175104 ≤ 175360) (by norm_num : 175360 ≤ 175616), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 175104 ≤ 175360) (by norm_num : 175360 ≤ 175616), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_175616_175680 :
    (∑ n ∈ Ico 175616 175680, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 175616 175680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 175616 175680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-256198 : ℤ) ∧
    (∑ n ∈ Ico 175616 175680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5124059194663428322329839422 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_175680_175744 :
    (∑ n ∈ Ico 175680 175744, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 175680 175744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 175680 175744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-313017 : ℤ) ∧
    (∑ n ∈ Ico 175680 175744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6260438435185328279489649848 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_175616_175744 :
    (∑ n ∈ Ico 175616 175744, mobiusTreeValue 16 mobiusTable1200001 n) = (-20 : ℤ) ∧
    (∑ n ∈ Ico 175616 175744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 175616 175744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-569215 : ℤ) ∧
    (∑ n ∈ Ico 175616 175744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11384497629848756601819489270 : ℤ) := by
  rcases cdemPrefixStats_175616_175680 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_175680_175744 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 175616 ≤ 175680) (by norm_num : 175680 ≤ 175744), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 175616 ≤ 175680) (by norm_num : 175680 ≤ 175744), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 175616 ≤ 175680) (by norm_num : 175680 ≤ 175744), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 175616 ≤ 175680) (by norm_num : 175680 ≤ 175744), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_175744_175808 :
    (∑ n ∈ Ico 175744 175808, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 175744 175808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 175744 175808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (56878 : ℤ) ∧
    (∑ n ∈ Ico 175744 175808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1137536695315080487394957464 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_175808_175872 :
    (∑ n ∈ Ico 175808 175872, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 175808 175872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 175808 175872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (142173 : ℤ) ∧
    (∑ n ∈ Ico 175808 175872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2843503803066520039240635480 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_175744_175872 :
    (∑ n ∈ Ico 175744 175872, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 175744 175872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 175744 175872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (199051 : ℤ) ∧
    (∑ n ∈ Ico 175744 175872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3981040498381600526635592944 : ℤ) := by
  rcases cdemPrefixStats_175744_175808 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_175808_175872 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 175744 ≤ 175808) (by norm_num : 175808 ≤ 175872), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 175744 ≤ 175808) (by norm_num : 175808 ≤ 175872), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 175744 ≤ 175808) (by norm_num : 175808 ≤ 175872), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 175744 ≤ 175808) (by norm_num : 175808 ≤ 175872), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_175616_175872 :
    (∑ n ∈ Ico 175616 175872, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 175616 175872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 175616 175872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-370164 : ℤ) ∧
    (∑ n ∈ Ico 175616 175872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7403457131467156075183896326 : ℤ) := by
  rcases cdemPrefixStats_175616_175744 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_175744_175872 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 175616 ≤ 175744) (by norm_num : 175744 ≤ 175872), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 175616 ≤ 175744) (by norm_num : 175744 ≤ 175872), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 175616 ≤ 175744) (by norm_num : 175744 ≤ 175872), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 175616 ≤ 175744) (by norm_num : 175744 ≤ 175872), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_175872_175936 :
    (∑ n ∈ Ico 175872 175936, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 175872 175936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 175872 175936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-170562 : ℤ) ∧
    (∑ n ∈ Ico 175872 175936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3411339283617764225467982899 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_175936_176000 :
    (∑ n ∈ Ico 175936 176000, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 175936 176000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 175936 176000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-255718 : ℤ) ∧
    (∑ n ∈ Ico 175936 176000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5114466234194634235909556269 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_175872_176000 :
    (∑ n ∈ Ico 175872 176000, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 175872 176000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 175872 176000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-426280 : ℤ) ∧
    (∑ n ∈ Ico 175872 176000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8525805517812398461377539168 : ℤ) := by
  rcases cdemPrefixStats_175872_175936 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_175936_176000 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 175872 ≤ 175936) (by norm_num : 175936 ≤ 176000), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 175872 ≤ 175936) (by norm_num : 175936 ≤ 176000), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 175872 ≤ 175936) (by norm_num : 175936 ≤ 176000), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 175872 ≤ 175936) (by norm_num : 175936 ≤ 176000), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_176000_176064 :
    (∑ n ∈ Ico 176000 176064, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 176000 176064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 176000 176064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (56842 : ℤ) ∧
    (∑ n ∈ Ico 176000 176064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1136805729299776184785491712 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_176064_176128 :
    (∑ n ∈ Ico 176064 176128, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 176064 176128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 176064 176128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-28381 : ℤ) ∧
    (∑ n ∈ Ico 176064 176128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-567633433965128377330821151 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_176000_176128 :
    (∑ n ∈ Ico 176000 176128, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 176000 176128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 176000 176128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (28461 : ℤ) ∧
    (∑ n ∈ Ico 176000 176128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (569172295334647807454670561 : ℤ) := by
  rcases cdemPrefixStats_176000_176064 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_176064_176128 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 176000 ≤ 176064) (by norm_num : 176064 ≤ 176128), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 176000 ≤ 176064) (by norm_num : 176064 ≤ 176128), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 176000 ≤ 176064) (by norm_num : 176064 ≤ 176128), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 176000 ≤ 176064) (by norm_num : 176064 ≤ 176128), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_175872_176128 :
    (∑ n ∈ Ico 175872 176128, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 175872 176128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 175872 176128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-397819 : ℤ) ∧
    (∑ n ∈ Ico 175872 176128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7956633222477750653922868607 : ℤ) := by
  rcases cdemPrefixStats_175872_176000 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_176000_176128 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 175872 ≤ 176000) (by norm_num : 176000 ≤ 176128), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 175872 ≤ 176000) (by norm_num : 176000 ≤ 176128), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 175872 ≤ 176000) (by norm_num : 176000 ≤ 176128), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 175872 ≤ 176000) (by norm_num : 176000 ≤ 176128), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_175616_176128 :
    (∑ n ∈ Ico 175616 176128, mobiusTreeValue 16 mobiusTable1200001 n) = (-27 : ℤ) ∧
    (∑ n ∈ Ico 175616 176128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 175616 176128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-767983 : ℤ) ∧
    (∑ n ∈ Ico 175616 176128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-15360090353944906729106764933 : ℤ) := by
  rcases cdemPrefixStats_175616_175872 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_175872_176128 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 175616 ≤ 175872) (by norm_num : 175872 ≤ 176128), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 175616 ≤ 175872) (by norm_num : 175872 ≤ 176128), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 175616 ≤ 175872) (by norm_num : 175872 ≤ 176128), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 175616 ≤ 175872) (by norm_num : 175872 ≤ 176128), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_175104_176128 :
    (∑ n ∈ Ico 175104 176128, mobiusTreeValue 16 mobiusTable1200001 n) = (20 : ℤ) ∧
    (∑ n ∈ Ico 175104 176128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (624 : ℕ) ∧
    (∑ n ∈ Ico 175104 176128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (572065 : ℤ) ∧
    (∑ n ∈ Ico 175104 176128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11441324533698211761680192289 : ℤ) := by
  rcases cdemPrefixStats_175104_175616 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_175616_176128 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 175104 ≤ 175616) (by norm_num : 175616 ≤ 176128), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 175104 ≤ 175616) (by norm_num : 175616 ≤ 176128), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 175104 ≤ 175616) (by norm_num : 175616 ≤ 176128), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 175104 ≤ 175616) (by norm_num : 175616 ≤ 176128), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_174080_176128 :
    (∑ n ∈ Ico 174080 176128, mobiusTreeValue 16 mobiusTable1200001 n) = (20 : ℤ) ∧
    (∑ n ∈ Ico 174080 176128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1246 : ℕ) ∧
    (∑ n ∈ Ico 174080 176128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (572003 : ℤ) ∧
    (∑ n ∈ Ico 174080 176128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11440144230822294512918876709 : ℤ) := by
  rcases cdemPrefixStats_174080_175104 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_175104_176128 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 174080 ≤ 175104) (by norm_num : 175104 ≤ 176128), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 174080 ≤ 175104) (by norm_num : 175104 ≤ 176128), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 174080 ≤ 175104) (by norm_num : 175104 ≤ 176128), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 174080 ≤ 175104) (by norm_num : 175104 ≤ 176128), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_172032_176128 :
    (∑ n ∈ Ico 172032 176128, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 172032 176128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2492 : ℕ) ∧
    (∑ n ∈ Ico 172032 176128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (458472 : ℤ) ∧
    (∑ n ∈ Ico 172032 176128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9169755886883888965720022430 : ℤ) := by
  rcases cdemPrefixStats_172032_174080 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_174080_176128 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 172032 ≤ 174080) (by norm_num : 174080 ≤ 176128), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 172032 ≤ 174080) (by norm_num : 174080 ≤ 176128), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 172032 ≤ 174080) (by norm_num : 174080 ≤ 176128), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 172032 ≤ 174080) (by norm_num : 174080 ≤ 176128), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup042_checked_complete :
    (∑ n ∈ Ico 172032 176128, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 172032 176128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2492 : ℕ) ∧
    (∑ n ∈ Ico 172032 176128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (458472 : ℤ) ∧
    (∑ n ∈ Ico 172032 176128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9169755886883888965720022430 : ℤ) := cdemPrefixStats_172032_176128
end Helfgott
#print axioms Helfgott.cdemPrefixGroup042_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 172032 176128, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 172032 176128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2492 : ℕ) ∧
    (∑ n ∈ Ico 172032 176128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (458472 : ℤ) ∧
    (∑ n ∈ Ico 172032 176128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9169755886883888965720022430 : ℤ) := Helfgott.cdemPrefixGroup042_checked_complete
#print axioms solution
