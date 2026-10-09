-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup031_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T02:20:52.460102+00:00
-- url     : https://prove2.me/submissions/77787bfb-6bc3-44dc-83a2-5d5f6e9b9fe0

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
private theorem cdemPrefixStats_126976_127040 :
    (∑ n ∈ Ico 126976 127040, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 126976 127040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 126976 127040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (236199 : ℤ) ∧
    (∑ n ∈ Ico 126976 127040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4723975404791756963072583268 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_127040_127104 :
    (∑ n ∈ Ico 127040 127104, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 127040 127104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 127040 127104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (550905 : ℤ) ∧
    (∑ n ∈ Ico 127040 127104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11018187397085985039628913037 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_126976_127104 :
    (∑ n ∈ Ico 126976 127104, mobiusTreeValue 16 mobiusTable1200001 n) = (20 : ℤ) ∧
    (∑ n ∈ Ico 126976 127104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 126976 127104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (787104 : ℤ) ∧
    (∑ n ∈ Ico 126976 127104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15742162801877742002701496305 : ℤ) := by
  rcases cdemPrefixStats_126976_127040 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_127040_127104 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 126976 ≤ 127040) (by norm_num : 127040 ≤ 127104), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 126976 ≤ 127040) (by norm_num : 127040 ≤ 127104), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 126976 ≤ 127040) (by norm_num : 127040 ≤ 127104), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 126976 ≤ 127040) (by norm_num : 127040 ≤ 127104), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_127104_127168 :
    (∑ n ∈ Ico 127104 127168, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 127104 127168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 127104 127168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-157318 : ℤ) ∧
    (∑ n ∈ Ico 127104 127168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3146366971445842303019381521 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_127168_127232 :
    (∑ n ∈ Ico 127168 127232, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 127168 127232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 127168 127232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (314462 : ℤ) ∧
    (∑ n ∈ Ico 127168 127232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6289382544586117444899271198 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_127104_127232 :
    (∑ n ∈ Ico 127104 127232, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 127104 127232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 127104 127232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (157144 : ℤ) ∧
    (∑ n ∈ Ico 127104 127232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3143015573140275141879889677 : ℤ) := by
  rcases cdemPrefixStats_127104_127168 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_127168_127232 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 127104 ≤ 127168) (by norm_num : 127168 ≤ 127232), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 127104 ≤ 127168) (by norm_num : 127168 ≤ 127232), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 127104 ≤ 127168) (by norm_num : 127168 ≤ 127232), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 127104 ≤ 127168) (by norm_num : 127168 ≤ 127232), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_126976_127232 :
    (∑ n ∈ Ico 126976 127232, mobiusTreeValue 16 mobiusTable1200001 n) = (24 : ℤ) ∧
    (∑ n ∈ Ico 126976 127232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (160 : ℕ) ∧
    (∑ n ∈ Ico 126976 127232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (944248 : ℤ) ∧
    (∑ n ∈ Ico 126976 127232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18885178375018017144581385982 : ℤ) := by
  rcases cdemPrefixStats_126976_127104 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_127104_127232 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 126976 ≤ 127104) (by norm_num : 127104 ≤ 127232), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 126976 ≤ 127104) (by norm_num : 127104 ≤ 127232), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 126976 ≤ 127104) (by norm_num : 127104 ≤ 127232), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 126976 ≤ 127104) (by norm_num : 127104 ≤ 127232), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_127232_127296 :
    (∑ n ∈ Ico 127232 127296, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 127232 127296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 127232 127296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-235703 : ℤ) ∧
    (∑ n ∈ Ico 127232 127296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4714146012007860878506545317 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_127296_127360 :
    (∑ n ∈ Ico 127296 127360, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 127296 127360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 127296 127360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (549712 : ℤ) ∧
    (∑ n ∈ Ico 127296 127360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10994417090048769784784939655 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_127232_127360 :
    (∑ n ∈ Ico 127232 127360, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 127232 127360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 127232 127360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (314009 : ℤ) ∧
    (∑ n ∈ Ico 127232 127360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6280271078040908906278394338 : ℤ) := by
  rcases cdemPrefixStats_127232_127296 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_127296_127360 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 127232 ≤ 127296) (by norm_num : 127296 ≤ 127360), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 127232 ≤ 127296) (by norm_num : 127296 ≤ 127360), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 127232 ≤ 127296) (by norm_num : 127296 ≤ 127360), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 127232 ≤ 127296) (by norm_num : 127296 ≤ 127360), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_127360_127424 :
    (∑ n ∈ Ico 127360 127424, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 127360 127424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 127360 127424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-78507 : ℤ) ∧
    (∑ n ∈ Ico 127360 127424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1570228474634804199698134861 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_127424_127488 :
    (∑ n ∈ Ico 127424 127488, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 127424 127488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 127424 127488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (313843 : ℤ) ∧
    (∑ n ∈ Ico 127424 127488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6277026825632078335860634811 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_127360_127488 :
    (∑ n ∈ Ico 127360 127488, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 127360 127488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 127360 127488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (235336 : ℤ) ∧
    (∑ n ∈ Ico 127360 127488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4706798350997274136162499950 : ℤ) := by
  rcases cdemPrefixStats_127360_127424 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_127424_127488 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 127360 ≤ 127424) (by norm_num : 127424 ≤ 127488), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 127360 ≤ 127424) (by norm_num : 127424 ≤ 127488), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 127360 ≤ 127424) (by norm_num : 127424 ≤ 127488), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 127360 ≤ 127424) (by norm_num : 127424 ≤ 127488), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_127232_127488 :
    (∑ n ∈ Ico 127232 127488, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 127232 127488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 127232 127488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (549345 : ℤ) ∧
    (∑ n ∈ Ico 127232 127488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10987069429038183042440894288 : ℤ) := by
  rcases cdemPrefixStats_127232_127360 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_127360_127488 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 127232 ≤ 127360) (by norm_num : 127360 ≤ 127488), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 127232 ≤ 127360) (by norm_num : 127360 ≤ 127488), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 127232 ≤ 127360) (by norm_num : 127360 ≤ 127488), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 127232 ≤ 127360) (by norm_num : 127360 ≤ 127488), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_126976_127488 :
    (∑ n ∈ Ico 126976 127488, mobiusTreeValue 16 mobiusTable1200001 n) = (38 : ℤ) ∧
    (∑ n ∈ Ico 126976 127488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (316 : ℕ) ∧
    (∑ n ∈ Ico 126976 127488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1493593 : ℤ) ∧
    (∑ n ∈ Ico 126976 127488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (29872247804056200187022280270 : ℤ) := by
  rcases cdemPrefixStats_126976_127232 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_127232_127488 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 126976 ≤ 127232) (by norm_num : 127232 ≤ 127488), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 126976 ≤ 127232) (by norm_num : 127232 ≤ 127488), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 126976 ≤ 127232) (by norm_num : 127232 ≤ 127488), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 126976 ≤ 127232) (by norm_num : 127232 ≤ 127488), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_127488_127552 :
    (∑ n ∈ Ico 127488 127552, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 127488 127552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 127488 127552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (39173 : ℤ) ∧
    (∑ n ∈ Ico 127488 127552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (783501982247327367782558872 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_127552_127616 :
    (∑ n ∈ Ico 127552 127616, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 127552 127616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 127552 127616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (156767 : ℤ) ∧
    (∑ n ∈ Ico 127552 127616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3135312418294112288456856064 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_127488_127616 :
    (∑ n ∈ Ico 127488 127616, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 127488 127616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 127488 127616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (195940 : ℤ) ∧
    (∑ n ∈ Ico 127488 127616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3918814400541439656239414936 : ℤ) := by
  rcases cdemPrefixStats_127488_127552 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_127552_127616 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 127488 ≤ 127552) (by norm_num : 127552 ≤ 127616), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 127488 ≤ 127552) (by norm_num : 127552 ≤ 127616), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 127488 ≤ 127552) (by norm_num : 127552 ≤ 127616), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 127488 ≤ 127552) (by norm_num : 127552 ≤ 127616), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_127616_127680 :
    (∑ n ∈ Ico 127616 127680, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 127616 127680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 127616 127680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 127616 127680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-288257446838107222400679 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_127680_127744 :
    (∑ n ∈ Ico 127680 127744, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 127680 127744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 127680 127744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (78321 : ℤ) ∧
    (∑ n ∈ Ico 127680 127744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1566440484030943860932615305 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_127616_127744 :
    (∑ n ∈ Ico 127616 127744, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 127616 127744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 127616 127744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (78310 : ℤ) ∧
    (∑ n ∈ Ico 127616 127744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1566152226584105753710214626 : ℤ) := by
  rcases cdemPrefixStats_127616_127680 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_127680_127744 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 127616 ≤ 127680) (by norm_num : 127680 ≤ 127744), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 127616 ≤ 127680) (by norm_num : 127680 ≤ 127744), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 127616 ≤ 127680) (by norm_num : 127680 ≤ 127744), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 127616 ≤ 127680) (by norm_num : 127680 ≤ 127744), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_127488_127744 :
    (∑ n ∈ Ico 127488 127744, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 127488 127744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 127488 127744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (274250 : ℤ) ∧
    (∑ n ∈ Ico 127488 127744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5484966627125545409949629562 : ℤ) := by
  rcases cdemPrefixStats_127488_127616 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_127616_127744 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 127488 ≤ 127616) (by norm_num : 127616 ≤ 127744), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 127488 ≤ 127616) (by norm_num : 127616 ≤ 127744), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 127488 ≤ 127616) (by norm_num : 127616 ≤ 127744), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 127488 ≤ 127616) (by norm_num : 127616 ≤ 127744), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_127744_127808 :
    (∑ n ∈ Ico 127744 127808, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 127744 127808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 127744 127808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (156468 : ℤ) ∧
    (∑ n ∈ Ico 127744 127808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3129400323233074235853590704 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_127808_127872 :
    (∑ n ∈ Ico 127808 127872, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 127808 127872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 127808 127872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-234681 : ℤ) ∧
    (∑ n ∈ Ico 127808 127872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4693678815367394418899962324 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_127744_127872 :
    (∑ n ∈ Ico 127744 127872, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 127744 127872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 127744 127872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-78213 : ℤ) ∧
    (∑ n ∈ Ico 127744 127872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1564278492134320183046371620 : ℤ) := by
  rcases cdemPrefixStats_127744_127808 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_127808_127872 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 127744 ≤ 127808) (by norm_num : 127808 ≤ 127872), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 127744 ≤ 127808) (by norm_num : 127808 ≤ 127872), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 127744 ≤ 127808) (by norm_num : 127808 ≤ 127872), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 127744 ≤ 127808) (by norm_num : 127808 ≤ 127872), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_127872_127936 :
    (∑ n ∈ Ico 127872 127936, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 127872 127936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 127872 127936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-390936 : ℤ) ∧
    (∑ n ∈ Ico 127872 127936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7818791836413400025038490471 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_127936_128000 :
    (∑ n ∈ Ico 127936 128000, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 127936 128000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 127936 128000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (78166 : ℤ) ∧
    (∑ n ∈ Ico 127936 128000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1563324392169753578304124494 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_127872_128000 :
    (∑ n ∈ Ico 127872 128000, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 127872 128000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 127872 128000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-312770 : ℤ) ∧
    (∑ n ∈ Ico 127872 128000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6255467444243646446734365977 : ℤ) := by
  rcases cdemPrefixStats_127872_127936 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_127936_128000 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 127872 ≤ 127936) (by norm_num : 127936 ≤ 128000), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 127872 ≤ 127936) (by norm_num : 127936 ≤ 128000), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 127872 ≤ 127936) (by norm_num : 127936 ≤ 128000), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 127872 ≤ 127936) (by norm_num : 127936 ≤ 128000), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_127744_128000 :
    (∑ n ∈ Ico 127744 128000, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 127744 128000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 127744 128000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-390983 : ℤ) ∧
    (∑ n ∈ Ico 127744 128000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7819745936377966629780737597 : ℤ) := by
  rcases cdemPrefixStats_127744_127872 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_127872_128000 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 127744 ≤ 127872) (by norm_num : 127872 ≤ 128000), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 127744 ≤ 127872) (by norm_num : 127872 ≤ 128000), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 127744 ≤ 127872) (by norm_num : 127872 ≤ 128000), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 127744 ≤ 127872) (by norm_num : 127872 ≤ 128000), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_127488_128000 :
    (∑ n ∈ Ico 127488 128000, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 127488 128000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 127488 128000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-116733 : ℤ) ∧
    (∑ n ∈ Ico 127488 128000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2334779309252421219831108035 : ℤ) := by
  rcases cdemPrefixStats_127488_127744 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_127744_128000 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 127488 ≤ 127744) (by norm_num : 127744 ≤ 128000), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 127488 ≤ 127744) (by norm_num : 127744 ≤ 128000), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 127488 ≤ 127744) (by norm_num : 127744 ≤ 128000), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 127488 ≤ 127744) (by norm_num : 127744 ≤ 128000), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_126976_128000 :
    (∑ n ∈ Ico 126976 128000, mobiusTreeValue 16 mobiusTable1200001 n) = (35 : ℤ) ∧
    (∑ n ∈ Ico 126976 128000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (625 : ℕ) ∧
    (∑ n ∈ Ico 126976 128000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1376860 : ℤ) ∧
    (∑ n ∈ Ico 126976 128000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (27537468494803778967191172235 : ℤ) := by
  rcases cdemPrefixStats_126976_127488 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_127488_128000 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 126976 ≤ 127488) (by norm_num : 127488 ≤ 128000), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 126976 ≤ 127488) (by norm_num : 127488 ≤ 128000), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 126976 ≤ 127488) (by norm_num : 127488 ≤ 128000), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 126976 ≤ 127488) (by norm_num : 127488 ≤ 128000), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_128000_128064 :
    (∑ n ∈ Ico 128000 128064, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 128000 128064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 128000 128064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (39086 : ℤ) ∧
    (∑ n ∈ Ico 128000 128064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (781750330293968728404507479 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_128064_128128 :
    (∑ n ∈ Ico 128064 128128, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 128064 128128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 128064 128128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (234206 : ℤ) ∧
    (∑ n ∈ Ico 128064 128128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4684224856197913936672039074 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_128000_128128 :
    (∑ n ∈ Ico 128000 128128, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 128000 128128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 128000 128128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (273292 : ℤ) ∧
    (∑ n ∈ Ico 128000 128128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5465975186491882665076546553 : ℤ) := by
  rcases cdemPrefixStats_128000_128064 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_128064_128128 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 128000 ≤ 128064) (by norm_num : 128064 ≤ 128128), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 128000 ≤ 128064) (by norm_num : 128064 ≤ 128128), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 128000 ≤ 128064) (by norm_num : 128064 ≤ 128128), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 128000 ≤ 128064) (by norm_num : 128064 ≤ 128128), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_128128_128192 :
    (∑ n ∈ Ico 128128 128192, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 128128 128192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 128128 128192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (273110 : ℤ) ∧
    (∑ n ∈ Ico 128128 128192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5462263743426708679136708904 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_128192_128256 :
    (∑ n ∈ Ico 128192 128256, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 128192 128256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 128192 128256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-350943 : ℤ) ∧
    (∑ n ∈ Ico 128192 128256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7018948637014806772075337982 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_128128_128256 :
    (∑ n ∈ Ico 128128 128256, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 128128 128256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 128128 128256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-77833 : ℤ) ∧
    (∑ n ∈ Ico 128128 128256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1556684893588098092938629078 : ℤ) := by
  rcases cdemPrefixStats_128128_128192 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_128192_128256 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 128128 ≤ 128192) (by norm_num : 128192 ≤ 128256), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 128128 ≤ 128192) (by norm_num : 128192 ≤ 128256), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 128128 ≤ 128192) (by norm_num : 128192 ≤ 128256), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 128128 ≤ 128192) (by norm_num : 128192 ≤ 128256), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_128000_128256 :
    (∑ n ∈ Ico 128000 128256, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 128000 128256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 128000 128256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (195459 : ℤ) ∧
    (∑ n ∈ Ico 128000 128256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3909290292903784572137917475 : ℤ) := by
  rcases cdemPrefixStats_128000_128128 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_128128_128256 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 128000 ≤ 128128) (by norm_num : 128128 ≤ 128256), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 128000 ≤ 128128) (by norm_num : 128128 ≤ 128256), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 128000 ≤ 128128) (by norm_num : 128128 ≤ 128256), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 128000 ≤ 128128) (by norm_num : 128128 ≤ 128256), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_128256_128320 :
    (∑ n ∈ Ico 128256 128320, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 128256 128320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 128256 128320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-233872 : ℤ) ∧
    (∑ n ∈ Ico 128256 128320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4677499488086429975315977259 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_128320_128384 :
    (∑ n ∈ Ico 128320 128384, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 128320 128384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 128320 128384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (116894 : ℤ) ∧
    (∑ n ∈ Ico 128320 128384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2337832279924621376948151482 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_128256_128384 :
    (∑ n ∈ Ico 128256 128384, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 128256 128384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 128256 128384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-116978 : ℤ) ∧
    (∑ n ∈ Ico 128256 128384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2339667208161808598367825777 : ℤ) := by
  rcases cdemPrefixStats_128256_128320 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_128320_128384 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 128256 ≤ 128320) (by norm_num : 128320 ≤ 128384), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 128256 ≤ 128320) (by norm_num : 128320 ≤ 128384), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 128256 ≤ 128320) (by norm_num : 128320 ≤ 128384), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 128256 ≤ 128320) (by norm_num : 128320 ≤ 128384), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_128384_128448 :
    (∑ n ∈ Ico 128384 128448, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 128384 128448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 128384 128448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-233590 : ℤ) ∧
    (∑ n ∈ Ico 128384 128448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4671829986648951899433412075 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_128448_128512 :
    (∑ n ∈ Ico 128448 128512, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 128448 128512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 128448 128512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-36 : ℤ) ∧
    (∑ n ∈ Ico 128448 128512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-690599175685805044073671 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_128384_128512 :
    (∑ n ∈ Ico 128384 128512, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 128384 128512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 128384 128512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-233626 : ℤ) ∧
    (∑ n ∈ Ico 128384 128512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4672520585824637704477485746 : ℤ) := by
  rcases cdemPrefixStats_128384_128448 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_128448_128512 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 128384 ≤ 128448) (by norm_num : 128448 ≤ 128512), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 128384 ≤ 128448) (by norm_num : 128448 ≤ 128512), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 128384 ≤ 128448) (by norm_num : 128448 ≤ 128512), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 128384 ≤ 128448) (by norm_num : 128448 ≤ 128512), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_128256_128512 :
    (∑ n ∈ Ico 128256 128512, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 128256 128512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (159 : ℕ) ∧
    (∑ n ∈ Ico 128256 128512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-350604 : ℤ) ∧
    (∑ n ∈ Ico 128256 128512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7012187793986446302845311523 : ℤ) := by
  rcases cdemPrefixStats_128256_128384 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_128384_128512 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 128256 ≤ 128384) (by norm_num : 128384 ≤ 128512), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 128256 ≤ 128384) (by norm_num : 128384 ≤ 128512), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 128256 ≤ 128384) (by norm_num : 128384 ≤ 128512), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 128256 ≤ 128384) (by norm_num : 128384 ≤ 128512), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_128000_128512 :
    (∑ n ∈ Ico 128000 128512, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 128000 128512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (314 : ℕ) ∧
    (∑ n ∈ Ico 128000 128512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-155145 : ℤ) ∧
    (∑ n ∈ Ico 128000 128512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3102897501082661730707394048 : ℤ) := by
  rcases cdemPrefixStats_128000_128256 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_128256_128512 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 128000 ≤ 128256) (by norm_num : 128256 ≤ 128512), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 128000 ≤ 128256) (by norm_num : 128256 ≤ 128512), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 128000 ≤ 128256) (by norm_num : 128256 ≤ 128512), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 128000 ≤ 128256) (by norm_num : 128256 ≤ 128512), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_128512_128576 :
    (∑ n ∈ Ico 128512 128576, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 128512 128576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 128512 128576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-38922 : ℤ) ∧
    (∑ n ∈ Ico 128512 128576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-778427981226910237960294162 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_128576_128640 :
    (∑ n ∈ Ico 128576 128640, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 128576 128640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 128576 128640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-116615 : ℤ) ∧
    (∑ n ∈ Ico 128576 128640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2332379450829377793923439491 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_128512_128640 :
    (∑ n ∈ Ico 128512 128640, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 128512 128640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 128512 128640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-155537 : ℤ) ∧
    (∑ n ∈ Ico 128512 128640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3110807432056288031883733653 : ℤ) := by
  rcases cdemPrefixStats_128512_128576 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_128576_128640 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 128512 ≤ 128576) (by norm_num : 128576 ≤ 128640), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 128512 ≤ 128576) (by norm_num : 128576 ≤ 128640), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 128512 ≤ 128576) (by norm_num : 128576 ≤ 128640), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 128512 ≤ 128576) (by norm_num : 128576 ≤ 128640), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_128640_128704 :
    (∑ n ∈ Ico 128640 128704, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 128640 128704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 128640 128704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (38855 : ℤ) ∧
    (∑ n ∈ Ico 128640 128704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (777109555529848161145223350 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_128704_128768 :
    (∑ n ∈ Ico 128704 128768, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 128704 128768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 128704 128768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-38836 : ℤ) ∧
    (∑ n ∈ Ico 128704 128768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-776867860277795107570147430 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_128640_128768 :
    (∑ n ∈ Ico 128640 128768, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 128640 128768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 128640 128768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (19 : ℤ) ∧
    (∑ n ∈ Ico 128640 128768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (241695252053053575075920 : ℤ) := by
  rcases cdemPrefixStats_128640_128704 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_128704_128768 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 128640 ≤ 128704) (by norm_num : 128704 ≤ 128768), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 128640 ≤ 128704) (by norm_num : 128704 ≤ 128768), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 128640 ≤ 128704) (by norm_num : 128704 ≤ 128768), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 128640 ≤ 128704) (by norm_num : 128704 ≤ 128768), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_128512_128768 :
    (∑ n ∈ Ico 128512 128768, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 128512 128768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 128512 128768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-155518 : ℤ) ∧
    (∑ n ∈ Ico 128512 128768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3110565736804234978308657733 : ℤ) := by
  rcases cdemPrefixStats_128512_128640 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_128640_128768 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 128512 ≤ 128640) (by norm_num : 128640 ≤ 128768), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 128512 ≤ 128640) (by norm_num : 128640 ≤ 128768), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 128512 ≤ 128640) (by norm_num : 128640 ≤ 128768), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 128512 ≤ 128640) (by norm_num : 128640 ≤ 128768), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_128768_128832 :
    (∑ n ∈ Ico 128768 128832, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 128768 128832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 128768 128832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (427036 : ℤ) ∧
    (∑ n ∈ Ico 128768 128832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8540812882168548691580423882 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_128832_128896 :
    (∑ n ∈ Ico 128832 128896, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 128832 128896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 128832 128896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-232853 : ℤ) ∧
    (∑ n ∈ Ico 128832 128896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4657107362219656498898060558 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_128768_128896 :
    (∑ n ∈ Ico 128768 128896, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 128768 128896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (73 : ℕ) ∧
    (∑ n ∈ Ico 128768 128896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (194183 : ℤ) ∧
    (∑ n ∈ Ico 128768 128896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3883705519948892192682363324 : ℤ) := by
  rcases cdemPrefixStats_128768_128832 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_128832_128896 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 128768 ≤ 128832) (by norm_num : 128832 ≤ 128896), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 128768 ≤ 128832) (by norm_num : 128832 ≤ 128896), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 128768 ≤ 128832) (by norm_num : 128832 ≤ 128896), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 128768 ≤ 128832) (by norm_num : 128832 ≤ 128896), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_128896_128960 :
    (∑ n ∈ Ico 128896 128960, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 128896 128960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 128896 128960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-232591 : ℤ) ∧
    (∑ n ∈ Ico 128896 128960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4651889228751824148504560673 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_128960_129024 :
    (∑ n ∈ Ico 128960 129024, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 128960 129024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 128960 129024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-426329 : ℤ) ∧
    (∑ n ∈ Ico 128960 129024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8526651157361783815388052161 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_128896_129024 :
    (∑ n ∈ Ico 128896 129024, mobiusTreeValue 16 mobiusTable1200001 n) = (-17 : ℤ) ∧
    (∑ n ∈ Ico 128896 129024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 128896 129024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-658920 : ℤ) ∧
    (∑ n ∈ Ico 128896 129024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13178540386113607963892612834 : ℤ) := by
  rcases cdemPrefixStats_128896_128960 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_128960_129024 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 128896 ≤ 128960) (by norm_num : 128960 ≤ 129024), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 128896 ≤ 128960) (by norm_num : 128960 ≤ 129024), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 128896 ≤ 128960) (by norm_num : 128960 ≤ 129024), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 128896 ≤ 128960) (by norm_num : 128960 ≤ 129024), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_128768_129024 :
    (∑ n ∈ Ico 128768 129024, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 128768 129024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 128768 129024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-464737 : ℤ) ∧
    (∑ n ∈ Ico 128768 129024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9294834866164715771210249510 : ℤ) := by
  rcases cdemPrefixStats_128768_128896 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_128896_129024 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 128768 ≤ 128896) (by norm_num : 128896 ≤ 129024), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 128768 ≤ 128896) (by norm_num : 128896 ≤ 129024), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 128768 ≤ 128896) (by norm_num : 128896 ≤ 129024), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 128768 ≤ 128896) (by norm_num : 128896 ≤ 129024), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_128512_129024 :
    (∑ n ∈ Ico 128512 129024, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 128512 129024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (308 : ℕ) ∧
    (∑ n ∈ Ico 128512 129024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-620255 : ℤ) ∧
    (∑ n ∈ Ico 128512 129024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12405400602968950749518907243 : ℤ) := by
  rcases cdemPrefixStats_128512_128768 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_128768_129024 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 128512 ≤ 128768) (by norm_num : 128768 ≤ 129024), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 128512 ≤ 128768) (by norm_num : 128768 ≤ 129024), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 128512 ≤ 128768) (by norm_num : 128768 ≤ 129024), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 128512 ≤ 128768) (by norm_num : 128768 ≤ 129024), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_128000_129024 :
    (∑ n ∈ Ico 128000 129024, mobiusTreeValue 16 mobiusTable1200001 n) = (-20 : ℤ) ∧
    (∑ n ∈ Ico 128000 129024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (622 : ℕ) ∧
    (∑ n ∈ Ico 128000 129024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-775400 : ℤ) ∧
    (∑ n ∈ Ico 128000 129024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-15508298104051612480226301291 : ℤ) := by
  rcases cdemPrefixStats_128000_128512 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_128512_129024 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 128000 ≤ 128512) (by norm_num : 128512 ≤ 129024), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 128000 ≤ 128512) (by norm_num : 128512 ≤ 129024), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 128000 ≤ 128512) (by norm_num : 128512 ≤ 129024), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 128000 ≤ 128512) (by norm_num : 128512 ≤ 129024), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_126976_129024 :
    (∑ n ∈ Ico 126976 129024, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 126976 129024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1247 : ℕ) ∧
    (∑ n ∈ Ico 126976 129024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (601460 : ℤ) ∧
    (∑ n ∈ Ico 126976 129024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12029170390752166486964870944 : ℤ) := by
  rcases cdemPrefixStats_126976_128000 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_128000_129024 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 126976 ≤ 128000) (by norm_num : 128000 ≤ 129024), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 126976 ≤ 128000) (by norm_num : 128000 ≤ 129024), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 126976 ≤ 128000) (by norm_num : 128000 ≤ 129024), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 126976 ≤ 128000) (by norm_num : 128000 ≤ 129024), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_129024_129088 :
    (∑ n ∈ Ico 129024 129088, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 129024 129088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 129024 129088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-77447 : ℤ) ∧
    (∑ n ∈ Ico 129024 129088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1548910275309112793929572827 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_129088_129152 :
    (∑ n ∈ Ico 129088 129152, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 129088 129152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 129088 129152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-542118 : ℤ) ∧
    (∑ n ∈ Ico 129088 129152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10842543336556954469434787753 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_129024_129152 :
    (∑ n ∈ Ico 129024 129152, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 129024 129152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 129024 129152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-619565 : ℤ) ∧
    (∑ n ∈ Ico 129024 129152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12391453611866067263364360580 : ℤ) := by
  rcases cdemPrefixStats_129024_129088 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_129088_129152 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 129024 ≤ 129088) (by norm_num : 129088 ≤ 129152), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 129024 ≤ 129088) (by norm_num : 129088 ≤ 129152), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 129024 ≤ 129088) (by norm_num : 129088 ≤ 129152), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 129024 ≤ 129088) (by norm_num : 129088 ≤ 129152), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_129152_129216 :
    (∑ n ∈ Ico 129152 129216, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 129152 129216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 129152 129216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (77441 : ℤ) ∧
    (∑ n ∈ Ico 129152 129216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1548862591580452909322358459 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_129216_129280 :
    (∑ n ∈ Ico 129216 129280, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 129216 129280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 129216 129280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-154733 : ℤ) ∧
    (∑ n ∈ Ico 129216 129280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3094676018817887111222128445 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_129152_129280 :
    (∑ n ∈ Ico 129152 129280, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 129152 129280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 129152 129280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-77292 : ℤ) ∧
    (∑ n ∈ Ico 129152 129280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1545813427237434201899769986 : ℤ) := by
  rcases cdemPrefixStats_129152_129216 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_129216_129280 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 129152 ≤ 129216) (by norm_num : 129216 ≤ 129280), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 129152 ≤ 129216) (by norm_num : 129216 ≤ 129280), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 129152 ≤ 129216) (by norm_num : 129216 ≤ 129280), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 129152 ≤ 129216) (by norm_num : 129216 ≤ 129280), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_129024_129280 :
    (∑ n ∈ Ico 129024 129280, mobiusTreeValue 16 mobiusTable1200001 n) = (-18 : ℤ) ∧
    (∑ n ∈ Ico 129024 129280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 129024 129280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-696857 : ℤ) ∧
    (∑ n ∈ Ico 129024 129280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13937267039103501465264130566 : ℤ) := by
  rcases cdemPrefixStats_129024_129152 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_129152_129280 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 129024 ≤ 129152) (by norm_num : 129152 ≤ 129280), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 129024 ≤ 129152) (by norm_num : 129152 ≤ 129280), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 129024 ≤ 129152) (by norm_num : 129152 ≤ 129280), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 129024 ≤ 129152) (by norm_num : 129152 ≤ 129280), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_129280_129344 :
    (∑ n ∈ Ico 129280 129344, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 129280 129344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 129280 129344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (231948 : ℤ) ∧
    (∑ n ∈ Ico 129280 129344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4639031560527138079628877728 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_129344_129408 :
    (∑ n ∈ Ico 129344 129408, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 129344 129408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 129344 129408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-193250 : ℤ) ∧
    (∑ n ∈ Ico 129344 129408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3864991397892073063354903068 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_129280_129408 :
    (∑ n ∈ Ico 129280 129408, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 129280 129408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 129280 129408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (38698 : ℤ) ∧
    (∑ n ∈ Ico 129280 129408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (774040162635065016273974660 : ℤ) := by
  rcases cdemPrefixStats_129280_129344 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_129344_129408 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 129280 ≤ 129344) (by norm_num : 129344 ≤ 129408), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 129280 ≤ 129344) (by norm_num : 129344 ≤ 129408), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 129280 ≤ 129344) (by norm_num : 129344 ≤ 129408), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 129280 ≤ 129344) (by norm_num : 129344 ≤ 129408), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_129408_129472 :
    (∑ n ∈ Ico 129408 129472, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 129408 129472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (35 : ℕ) ∧
    (∑ n ∈ Ico 129408 129472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-502125 : ℤ) ∧
    (∑ n ∈ Ico 129408 129472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10042601058192159219908542764 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_129472_129536 :
    (∑ n ∈ Ico 129472 129536, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 129472 129536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 129472 129536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-347429 : ℤ) ∧
    (∑ n ∈ Ico 129472 129536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6948650381155939981611947123 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_129408_129536 :
    (∑ n ∈ Ico 129408 129536, mobiusTreeValue 16 mobiusTable1200001 n) = (-22 : ℤ) ∧
    (∑ n ∈ Ico 129408 129536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (74 : ℕ) ∧
    (∑ n ∈ Ico 129408 129536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-849554 : ℤ) ∧
    (∑ n ∈ Ico 129408 129536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-16991251439348099201520489887 : ℤ) := by
  rcases cdemPrefixStats_129408_129472 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_129472_129536 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 129408 ≤ 129472) (by norm_num : 129472 ≤ 129536), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 129408 ≤ 129472) (by norm_num : 129472 ≤ 129536), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 129408 ≤ 129472) (by norm_num : 129472 ≤ 129536), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 129408 ≤ 129472) (by norm_num : 129472 ≤ 129536), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_129280_129536 :
    (∑ n ∈ Ico 129280 129536, mobiusTreeValue 16 mobiusTable1200001 n) = (-21 : ℤ) ∧
    (∑ n ∈ Ico 129280 129536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 129280 129536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-810856 : ℤ) ∧
    (∑ n ∈ Ico 129280 129536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-16217211276713034185246515227 : ℤ) := by
  rcases cdemPrefixStats_129280_129408 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_129408_129536 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 129280 ≤ 129408) (by norm_num : 129408 ≤ 129536), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 129280 ≤ 129408) (by norm_num : 129408 ≤ 129536), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 129280 ≤ 129408) (by norm_num : 129408 ≤ 129536), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 129280 ≤ 129408) (by norm_num : 129408 ≤ 129536), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_129024_129536 :
    (∑ n ∈ Ico 129024 129536, mobiusTreeValue 16 mobiusTable1200001 n) = (-39 : ℤ) ∧
    (∑ n ∈ Ico 129024 129536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 129024 129536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1507713 : ℤ) ∧
    (∑ n ∈ Ico 129024 129536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-30154478315816535650510645793 : ℤ) := by
  rcases cdemPrefixStats_129024_129280 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_129280_129536 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 129024 ≤ 129280) (by norm_num : 129280 ≤ 129536), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 129024 ≤ 129280) (by norm_num : 129280 ≤ 129536), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 129024 ≤ 129280) (by norm_num : 129280 ≤ 129536), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 129024 ≤ 129280) (by norm_num : 129280 ≤ 129536), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_129536_129600 :
    (∑ n ∈ Ico 129536 129600, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 129536 129600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 129536 129600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-192919 : ℤ) ∧
    (∑ n ∈ Ico 129536 129600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3858405871940980013290883653 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_129600_129664 :
    (∑ n ∈ Ico 129600 129664, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 129600 129664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 129600 129664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-154262 : ℤ) ∧
    (∑ n ∈ Ico 129600 129664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3085306821392195215677705017 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_129536_129664 :
    (∑ n ∈ Ico 129536 129664, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 129536 129664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 129536 129664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-347181 : ℤ) ∧
    (∑ n ∈ Ico 129536 129664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6943712693333175228968588670 : ℤ) := by
  rcases cdemPrefixStats_129536_129600 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_129600_129664 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 129536 ≤ 129600) (by norm_num : 129600 ≤ 129664), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 129536 ≤ 129600) (by norm_num : 129600 ≤ 129664), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 129536 ≤ 129600) (by norm_num : 129600 ≤ 129664), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 129536 ≤ 129600) (by norm_num : 129600 ≤ 129664), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_129664_129728 :
    (∑ n ∈ Ico 129664 129728, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 129664 129728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 129664 129728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-154198 : ℤ) ∧
    (∑ n ∈ Ico 129664 129728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3083992625002310571448072761 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_129728_129792 :
    (∑ n ∈ Ico 129728 129792, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 129728 129792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 129728 129792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (77005 : ℤ) ∧
    (∑ n ∈ Ico 129728 129792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1540095398941824066800871836 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_129664_129792 :
    (∑ n ∈ Ico 129664 129792, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 129664 129792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 129664 129792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-77193 : ℤ) ∧
    (∑ n ∈ Ico 129664 129792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1543897226060486504647200925 : ℤ) := by
  rcases cdemPrefixStats_129664_129728 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_129728_129792 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 129664 ≤ 129728) (by norm_num : 129728 ≤ 129792), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 129664 ≤ 129728) (by norm_num : 129728 ≤ 129792), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 129664 ≤ 129728) (by norm_num : 129728 ≤ 129792), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 129664 ≤ 129728) (by norm_num : 129728 ≤ 129792), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_129536_129792 :
    (∑ n ∈ Ico 129536 129792, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 129536 129792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 129536 129792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-424374 : ℤ) ∧
    (∑ n ∈ Ico 129536 129792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8487609919393661733615789595 : ℤ) := by
  rcases cdemPrefixStats_129536_129664 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_129664_129792 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 129536 ≤ 129664) (by norm_num : 129664 ≤ 129792), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 129536 ≤ 129664) (by norm_num : 129664 ≤ 129792), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 129536 ≤ 129664) (by norm_num : 129664 ≤ 129792), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 129536 ≤ 129664) (by norm_num : 129664 ≤ 129792), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_129792_129856 :
    (∑ n ∈ Ico 129792 129856, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 129792 129856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 129792 129856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (77003 : ℤ) ∧
    (∑ n ∈ Ico 129792 129856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1540114236702747417304546838 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_129856_129920 :
    (∑ n ∈ Ico 129856 129920, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 129856 129920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 129856 129920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-153976 : ℤ) ∧
    (∑ n ∈ Ico 129856 129920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3079588208456560156736041583 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_129792_129920 :
    (∑ n ∈ Ico 129792 129920, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 129792 129920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 129792 129920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-76973 : ℤ) ∧
    (∑ n ∈ Ico 129792 129920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1539473971753812739431494745 : ℤ) := by
  rcases cdemPrefixStats_129792_129856 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_129856_129920 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 129792 ≤ 129856) (by norm_num : 129856 ≤ 129920), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 129792 ≤ 129856) (by norm_num : 129856 ≤ 129920), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 129792 ≤ 129856) (by norm_num : 129856 ≤ 129920), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 129792 ≤ 129856) (by norm_num : 129856 ≤ 129920), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_129920_129984 :
    (∑ n ∈ Ico 129920 129984, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 129920 129984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 129920 129984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (40 : ℤ) ∧
    (∑ n ∈ Ico 129920 129984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (840896837825888734867523 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_129984_130048 :
    (∑ n ∈ Ico 129984 130048, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 129984 130048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 129984 130048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (76983 : ℤ) ∧
    (∑ n ∈ Ico 129984 130048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1539644639167270475410024669 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_129920_130048 :
    (∑ n ∈ Ico 129920 130048, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 129920 130048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 129920 130048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (77023 : ℤ) ∧
    (∑ n ∈ Ico 129920 130048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1540485536005096364144892192 : ℤ) := by
  rcases cdemPrefixStats_129920_129984 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_129984_130048 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 129920 ≤ 129984) (by norm_num : 129984 ≤ 130048), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 129920 ≤ 129984) (by norm_num : 129984 ≤ 130048), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 129920 ≤ 129984) (by norm_num : 129984 ≤ 130048), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 129920 ≤ 129984) (by norm_num : 129984 ≤ 130048), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_129792_130048 :
    (∑ n ∈ Ico 129792 130048, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 129792 130048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 129792 130048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (50 : ℤ) ∧
    (∑ n ∈ Ico 129792 130048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1011564251283624713397447 : ℤ) := by
  rcases cdemPrefixStats_129792_129920 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_129920_130048 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 129792 ≤ 129920) (by norm_num : 129920 ≤ 130048), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 129792 ≤ 129920) (by norm_num : 129920 ≤ 130048), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 129792 ≤ 129920) (by norm_num : 129920 ≤ 130048), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 129792 ≤ 129920) (by norm_num : 129920 ≤ 130048), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_129536_130048 :
    (∑ n ∈ Ico 129536 130048, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 129536 130048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (315 : ℕ) ∧
    (∑ n ∈ Ico 129536 130048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-424324 : ℤ) ∧
    (∑ n ∈ Ico 129536 130048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8486598355142378108902392148 : ℤ) := by
  rcases cdemPrefixStats_129536_129792 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_129792_130048 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 129536 ≤ 129792) (by norm_num : 129792 ≤ 130048), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 129536 ≤ 129792) (by norm_num : 129792 ≤ 130048), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 129536 ≤ 129792) (by norm_num : 129792 ≤ 130048), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 129536 ≤ 129792) (by norm_num : 129792 ≤ 130048), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_129024_130048 :
    (∑ n ∈ Ico 129024 130048, mobiusTreeValue 16 mobiusTable1200001 n) = (-50 : ℤ) ∧
    (∑ n ∈ Ico 129024 130048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (626 : ℕ) ∧
    (∑ n ∈ Ico 129024 130048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1932037 : ℤ) ∧
    (∑ n ∈ Ico 129024 130048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-38641076670958913759413037941 : ℤ) := by
  rcases cdemPrefixStats_129024_129536 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_129536_130048 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 129024 ≤ 129536) (by norm_num : 129536 ≤ 130048), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 129024 ≤ 129536) (by norm_num : 129536 ≤ 130048), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 129024 ≤ 129536) (by norm_num : 129536 ≤ 130048), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 129024 ≤ 129536) (by norm_num : 129536 ≤ 130048), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_130048_130112 :
    (∑ n ∈ Ico 130048 130112, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 130048 130112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 130048 130112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-192180 : ℤ) ∧
    (∑ n ∈ Ico 130048 130112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3843699613128489815100931685 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_130112_130176 :
    (∑ n ∈ Ico 130112 130176, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 130112 130176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 130112 130176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (115224 : ℤ) ∧
    (∑ n ∈ Ico 130112 130176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2304513080319409527803827773 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_130048_130176 :
    (∑ n ∈ Ico 130048 130176, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 130048 130176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 130048 130176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-76956 : ℤ) ∧
    (∑ n ∈ Ico 130048 130176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1539186532809080287297103912 : ℤ) := by
  rcases cdemPrefixStats_130048_130112 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_130112_130176 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 130048 ≤ 130112) (by norm_num : 130112 ≤ 130176), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 130048 ≤ 130112) (by norm_num : 130112 ≤ 130176), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 130048 ≤ 130112) (by norm_num : 130112 ≤ 130176), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 130048 ≤ 130112) (by norm_num : 130112 ≤ 130176), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_130176_130240 :
    (∑ n ∈ Ico 130176 130240, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 130176 130240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 130176 130240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (537609 : ℤ) ∧
    (∑ n ∈ Ico 130176 130240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10752346220059756952424539175 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_130240_130304 :
    (∑ n ∈ Ico 130240 130304, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 130240 130304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 130240 130304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-191936 : ℤ) ∧
    (∑ n ∈ Ico 130240 130304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3838741973166374242174055179 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_130176_130304 :
    (∑ n ∈ Ico 130176 130304, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 130176 130304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 130176 130304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (345673 : ℤ) ∧
    (∑ n ∈ Ico 130176 130304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6913604246893382710250483996 : ℤ) := by
  rcases cdemPrefixStats_130176_130240 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_130240_130304 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 130176 ≤ 130240) (by norm_num : 130240 ≤ 130304), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 130176 ≤ 130240) (by norm_num : 130240 ≤ 130304), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 130176 ≤ 130240) (by norm_num : 130240 ≤ 130304), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 130176 ≤ 130240) (by norm_num : 130240 ≤ 130304), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_130048_130304 :
    (∑ n ∈ Ico 130048 130304, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 130048 130304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 130048 130304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (268717 : ℤ) ∧
    (∑ n ∈ Ico 130048 130304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5374417714084302422953380084 : ℤ) := by
  rcases cdemPrefixStats_130048_130176 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_130176_130304 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 130048 ≤ 130176) (by norm_num : 130176 ≤ 130304), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 130048 ≤ 130176) (by norm_num : 130176 ≤ 130304), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 130048 ≤ 130176) (by norm_num : 130176 ≤ 130304), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 130048 ≤ 130176) (by norm_num : 130176 ≤ 130304), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_130304_130368 :
    (∑ n ∈ Ico 130304 130368, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 130304 130368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 130304 130368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-306874 : ℤ) ∧
    (∑ n ∈ Ico 130304 130368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6137569898347017044105599270 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_130368_130432 :
    (∑ n ∈ Ico 130368 130432, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 130368 130432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 130368 130432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-383366 : ℤ) ∧
    (∑ n ∈ Ico 130368 130432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7667453334949428514299425989 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_130304_130432 :
    (∑ n ∈ Ico 130304 130432, mobiusTreeValue 16 mobiusTable1200001 n) = (-18 : ℤ) ∧
    (∑ n ∈ Ico 130304 130432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 130304 130432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-690240 : ℤ) ∧
    (∑ n ∈ Ico 130304 130432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13805023233296445558405025259 : ℤ) := by
  rcases cdemPrefixStats_130304_130368 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_130368_130432 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 130304 ≤ 130368) (by norm_num : 130368 ≤ 130432), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 130304 ≤ 130368) (by norm_num : 130368 ≤ 130432), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 130304 ≤ 130368) (by norm_num : 130368 ≤ 130432), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 130304 ≤ 130368) (by norm_num : 130368 ≤ 130432), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_130432_130496 :
    (∑ n ∈ Ico 130432 130496, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 130432 130496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 130432 130496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-153289 : ℤ) ∧
    (∑ n ∈ Ico 130432 130496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3065827285527168492048195160 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_130496_130560 :
    (∑ n ∈ Ico 130496 130560, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 130496 130560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 130496 130560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-306445 : ℤ) ∧
    (∑ n ∈ Ico 130496 130560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6129029608512583657807567776 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_130432_130560 :
    (∑ n ∈ Ico 130432 130560, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 130432 130560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 130432 130560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-459734 : ℤ) ∧
    (∑ n ∈ Ico 130432 130560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9194856894039752149855762936 : ℤ) := by
  rcases cdemPrefixStats_130432_130496 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_130496_130560 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 130432 ≤ 130496) (by norm_num : 130496 ≤ 130560), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 130432 ≤ 130496) (by norm_num : 130496 ≤ 130560), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 130432 ≤ 130496) (by norm_num : 130496 ≤ 130560), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 130432 ≤ 130496) (by norm_num : 130496 ≤ 130560), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_130304_130560 :
    (∑ n ∈ Ico 130304 130560, mobiusTreeValue 16 mobiusTable1200001 n) = (-30 : ℤ) ∧
    (∑ n ∈ Ico 130304 130560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 130304 130560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1149974 : ℤ) ∧
    (∑ n ∈ Ico 130304 130560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-22999880127336197708260788195 : ℤ) := by
  rcases cdemPrefixStats_130304_130432 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_130432_130560 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 130304 ≤ 130432) (by norm_num : 130432 ≤ 130560), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 130304 ≤ 130432) (by norm_num : 130432 ≤ 130560), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 130304 ≤ 130432) (by norm_num : 130432 ≤ 130560), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 130304 ≤ 130432) (by norm_num : 130432 ≤ 130560), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_130048_130560 :
    (∑ n ∈ Ico 130048 130560, mobiusTreeValue 16 mobiusTable1200001 n) = (-23 : ℤ) ∧
    (∑ n ∈ Ico 130048 130560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 130048 130560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-881257 : ℤ) ∧
    (∑ n ∈ Ico 130048 130560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-17625462413251895285307408111 : ℤ) := by
  rcases cdemPrefixStats_130048_130304 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_130304_130560 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 130048 ≤ 130304) (by norm_num : 130304 ≤ 130560), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 130048 ≤ 130304) (by norm_num : 130304 ≤ 130560), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 130048 ≤ 130304) (by norm_num : 130304 ≤ 130560), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 130048 ≤ 130304) (by norm_num : 130304 ≤ 130560), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_130560_130624 :
    (∑ n ∈ Ico 130560 130624, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 130560 130624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 130560 130624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (344611 : ℤ) ∧
    (∑ n ∈ Ico 130560 130624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6892326590191802406454927503 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_130624_130688 :
    (∑ n ∈ Ico 130624 130688, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 130624 130688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (35 : ℕ) ∧
    (∑ n ∈ Ico 130624 130688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-267888 : ℤ) ∧
    (∑ n ∈ Ico 130624 130688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5357849781299076210253010979 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_130560_130688 :
    (∑ n ∈ Ico 130560 130688, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 130560 130688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 130560 130688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (76723 : ℤ) ∧
    (∑ n ∈ Ico 130560 130688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1534476808892726196201916524 : ℤ) := by
  rcases cdemPrefixStats_130560_130624 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_130624_130688 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 130560 ≤ 130624) (by norm_num : 130624 ≤ 130688), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 130560 ≤ 130624) (by norm_num : 130624 ≤ 130688), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 130560 ≤ 130624) (by norm_num : 130624 ≤ 130688), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 130560 ≤ 130624) (by norm_num : 130624 ≤ 130688), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_130688_130752 :
    (∑ n ∈ Ico 130688 130752, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 130688 130752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 130688 130752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (153005 : ℤ) ∧
    (∑ n ∈ Ico 130688 130752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3060262237133890132998518840 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_130752_130816 :
    (∑ n ∈ Ico 130752 130816, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 130752 130816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 130752 130816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (267662 : ℤ) ∧
    (∑ n ∈ Ico 130752 130816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5353324950426673900065952957 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_130688_130816 :
    (∑ n ∈ Ico 130688 130816, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 130688 130816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 130688 130816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (420667 : ℤ) ∧
    (∑ n ∈ Ico 130688 130816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8413587187560564033064471797 : ℤ) := by
  rcases cdemPrefixStats_130688_130752 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_130752_130816 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 130688 ≤ 130752) (by norm_num : 130752 ≤ 130816), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 130688 ≤ 130752) (by norm_num : 130752 ≤ 130816), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 130688 ≤ 130752) (by norm_num : 130752 ≤ 130816), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 130688 ≤ 130752) (by norm_num : 130752 ≤ 130816), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_130560_130816 :
    (∑ n ∈ Ico 130560 130816, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 130560 130816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 130560 130816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (497390 : ℤ) ∧
    (∑ n ∈ Ico 130560 130816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9948063996453290229266388321 : ℤ) := by
  rcases cdemPrefixStats_130560_130688 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_130688_130816 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 130560 ≤ 130688) (by norm_num : 130688 ≤ 130816), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 130560 ≤ 130688) (by norm_num : 130688 ≤ 130816), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 130560 ≤ 130688) (by norm_num : 130688 ≤ 130816), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 130560 ≤ 130688) (by norm_num : 130688 ≤ 130816), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_130816_130880 :
    (∑ n ∈ Ico 130816 130880, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 130816 130880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 130816 130880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (76386 : ℤ) ∧
    (∑ n ∈ Ico 130816 130880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1527731773635927382192733997 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_130880_130944 :
    (∑ n ∈ Ico 130880 130944, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 130880 130944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 130880 130944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (267367 : ℤ) ∧
    (∑ n ∈ Ico 130880 130944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5347389520051024875718110783 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_130816_130944 :
    (∑ n ∈ Ico 130816 130944, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 130816 130944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 130816 130944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (343753 : ℤ) ∧
    (∑ n ∈ Ico 130816 130944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6875121293686952257910844780 : ℤ) := by
  rcases cdemPrefixStats_130816_130880 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_130880_130944 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 130816 ≤ 130880) (by norm_num : 130880 ≤ 130944), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 130816 ≤ 130880) (by norm_num : 130880 ≤ 130944), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 130816 ≤ 130880) (by norm_num : 130880 ≤ 130944), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 130816 ≤ 130880) (by norm_num : 130880 ≤ 130944), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_130944_131008 :
    (∑ n ∈ Ico 130944 131008, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 130944 131008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 130944 131008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-76388 : ℤ) ∧
    (∑ n ∈ Ico 130944 131008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1527766687342564188110859593 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_131008_131072 :
    (∑ n ∈ Ico 131008 131072, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 131008 131072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 131008 131072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-381545 : ℤ) ∧
    (∑ n ∈ Ico 131008 131072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7630984188225194934743780018 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_130944_131072 :
    (∑ n ∈ Ico 130944 131072, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 130944 131072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 130944 131072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-457933 : ℤ) ∧
    (∑ n ∈ Ico 130944 131072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9158750875567759122854639611 : ℤ) := by
  rcases cdemPrefixStats_130944_131008 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_131008_131072 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 130944 ≤ 131008) (by norm_num : 131008 ≤ 131072), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 130944 ≤ 131008) (by norm_num : 131008 ≤ 131072), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 130944 ≤ 131008) (by norm_num : 131008 ≤ 131072), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 130944 ≤ 131008) (by norm_num : 131008 ≤ 131072), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_130816_131072 :
    (∑ n ∈ Ico 130816 131072, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 130816 131072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 130816 131072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-114180 : ℤ) ∧
    (∑ n ∈ Ico 130816 131072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2283629581880806864943794831 : ℤ) := by
  rcases cdemPrefixStats_130816_130944 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_130944_131072 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 130816 ≤ 130944) (by norm_num : 130944 ≤ 131072), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 130816 ≤ 130944) (by norm_num : 130944 ≤ 131072), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 130816 ≤ 130944) (by norm_num : 130944 ≤ 131072), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 130816 ≤ 130944) (by norm_num : 130944 ≤ 131072), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_130560_131072 :
    (∑ n ∈ Ico 130560 131072, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 130560 131072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 130560 131072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (383210 : ℤ) ∧
    (∑ n ∈ Ico 130560 131072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7664434414572483364322593490 : ℤ) := by
  rcases cdemPrefixStats_130560_130816 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_130816_131072 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 130560 ≤ 130816) (by norm_num : 130816 ≤ 131072), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 130560 ≤ 130816) (by norm_num : 130816 ≤ 131072), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 130560 ≤ 130816) (by norm_num : 130816 ≤ 131072), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 130560 ≤ 130816) (by norm_num : 130816 ≤ 131072), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_130048_131072 :
    (∑ n ∈ Ico 130048 131072, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 130048 131072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (619 : ℕ) ∧
    (∑ n ∈ Ico 130048 131072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-498047 : ℤ) ∧
    (∑ n ∈ Ico 130048 131072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9961027998679411920984814621 : ℤ) := by
  rcases cdemPrefixStats_130048_130560 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_130560_131072 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 130048 ≤ 130560) (by norm_num : 130560 ≤ 131072), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 130048 ≤ 130560) (by norm_num : 130560 ≤ 131072), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 130048 ≤ 130560) (by norm_num : 130560 ≤ 131072), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 130048 ≤ 130560) (by norm_num : 130560 ≤ 131072), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_129024_131072 :
    (∑ n ∈ Ico 129024 131072, mobiusTreeValue 16 mobiusTable1200001 n) = (-63 : ℤ) ∧
    (∑ n ∈ Ico 129024 131072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1245 : ℕ) ∧
    (∑ n ∈ Ico 129024 131072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2430084 : ℤ) ∧
    (∑ n ∈ Ico 129024 131072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-48602104669638325680397852562 : ℤ) := by
  rcases cdemPrefixStats_129024_130048 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_130048_131072 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 129024 ≤ 130048) (by norm_num : 130048 ≤ 131072), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 129024 ≤ 130048) (by norm_num : 130048 ≤ 131072), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 129024 ≤ 130048) (by norm_num : 130048 ≤ 131072), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 129024 ≤ 130048) (by norm_num : 130048 ≤ 131072), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_126976_131072 :
    (∑ n ∈ Ico 126976 131072, mobiusTreeValue 16 mobiusTable1200001 n) = (-48 : ℤ) ∧
    (∑ n ∈ Ico 126976 131072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2492 : ℕ) ∧
    (∑ n ∈ Ico 126976 131072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1828624 : ℤ) ∧
    (∑ n ∈ Ico 126976 131072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-36572934278886159193432981618 : ℤ) := by
  rcases cdemPrefixStats_126976_129024 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_129024_131072 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 126976 ≤ 129024) (by norm_num : 129024 ≤ 131072), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 126976 ≤ 129024) (by norm_num : 129024 ≤ 131072), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 126976 ≤ 129024) (by norm_num : 129024 ≤ 131072), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 126976 ≤ 129024) (by norm_num : 129024 ≤ 131072), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup031_checked_complete :
    (∑ n ∈ Ico 126976 131072, mobiusTreeValue 16 mobiusTable1200001 n) = (-48 : ℤ) ∧
    (∑ n ∈ Ico 126976 131072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2492 : ℕ) ∧
    (∑ n ∈ Ico 126976 131072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1828624 : ℤ) ∧
    (∑ n ∈ Ico 126976 131072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-36572934278886159193432981618 : ℤ) := cdemPrefixStats_126976_131072
end Helfgott
#print axioms Helfgott.cdemPrefixGroup031_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 126976 131072, mobiusTreeValue 16 mobiusTable1200001 n) = (-48 : ℤ) ∧
    (∑ n ∈ Ico 126976 131072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2492 : ℕ) ∧
    (∑ n ∈ Ico 126976 131072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1828624 : ℤ) ∧
    (∑ n ∈ Ico 126976 131072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-36572934278886159193432981618 : ℤ) := Helfgott.cdemPrefixGroup031_checked_complete
#print axioms solution
